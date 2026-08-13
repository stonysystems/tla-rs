//! Projection pass (Phase 52.M1): clean-subset TLA+ → single-process spec.
//!
//! The clean subset (`docs/clean_tla_subset.md`) is a *global* model: state is
//! `[Node -> T]` and actions are taken by a quantified node. A tla-rs spec is
//! about **one** node. Projection is what removes the node dimension, and this
//! module is the analysis half of it — it decides what the projected spec's
//! types are. Emission lives in `emit.rs`.
//!
//! ## What "projecting a type" means
//!
//! A variable declared `x \in [Node -> T]` holds one `T` per node; the node
//! taking the step owns exactly one of them, so the projected type is `T`.
//! Nested arrays are the case worth stating: `req \in [Node -> [Node -> Nat]]`
//! projects to `Map<int, int>`, **not** to `int` — the outer index is the node
//! and disappears, while the inner index is a peer and survives. That is the
//! node's own table *about* its peers, and dropping both indices would silently
//! delete the protocol's knowledge.
//!
//! ## Reuse boundary
//!
//! This reuses the front half of `transpiler/src/tla/` — tokenizer, parser,
//! AST, and the clean-subset linter's analysis. It does **not** reuse
//! `translator.rs`, whose expression codegen targets the global model and does
//! not currently produce compiling Verus for a spec from the wild (see TODO.md
//! 52.M1's scoping note). The plan called for extending the existing
//! translator; that was written assuming it worked on this input.

use std::collections::BTreeMap;

use crate::tla::ast::{TlaBinOp, TlaExpr, TlaModule, TlaUnaryOp};
use crate::tla::clean_subset::{lint_module, CleanSubsetReport};

/// Type names the emitter always writes. An enum named after a variable must
/// not collide with one.
const EMITTED_TYPE_NAMES: &[&str] = &["LState", "LConstants", "LMessage", "LPacket"];

/// Field names a spec uses for a message's variant tag. Which one a spec uses
/// is style, not meaning, so the projection recognises the common spellings.
pub const TAG_FIELDS: &[&str] = &["type", "kind", "tag", "mtype"];
/// Field names that address a message. After projection these belong to the
/// packet -- the framework routes -- so they are not payload.
pub const ROUTING_FIELDS: &[&str] = &[
    "src", "dst", "source", "dest", "sender", "receiver", "msource", "mdest",
];

/// A Verus type in the projected spec.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProjectedType {
    Int,
    Bool,
    Set(Box<ProjectedType>),
    Map(Box<ProjectedType>, Box<ProjectedType>),
    Seq(Box<ProjectedType>),
    /// A finite set of string literals, which becomes an enum.
    Enum {
        name: String,
        variants: Vec<String>,
    },
    /// A record set, which becomes a struct. Named after the operator that
    /// defines it -- `LogEntry` in the source becomes `LLogEntry`.
    Record {
        name: String,
        fields: Vec<(String, ProjectedType)>,
    },
    /// A type the pass could not resolve; carries what it saw, so the failure
    /// is reportable rather than silently becoming `int`.
    Unresolved(String),
}

impl ProjectedType {
    pub fn render(&self) -> String {
        match self {
            ProjectedType::Int => "int".to_string(),
            ProjectedType::Bool => "bool".to_string(),
            ProjectedType::Set(inner) => format!("Set<{}>", inner.render()),
            ProjectedType::Map(k, v) => format!("Map<{}, {}>", k.render(), v.render()),
            ProjectedType::Seq(inner) => format!("Seq<{}>", inner.render()),
            ProjectedType::Enum { name, .. } => name.clone(),
            ProjectedType::Record { name, .. } => name.clone(),
            ProjectedType::Unresolved(what) => format!("/* unresolved: {what} */"),
        }
    }

    pub fn is_unresolved(&self) -> bool {
        matches!(self, ProjectedType::Unresolved(_))
    }
}

/// A field of the projected `LState`.
#[derive(Debug, Clone)]
pub struct StateField {
    /// Name in the projected spec (snake_case).
    pub name: String,
    /// Name in the source spec.
    pub source_name: String,
    pub ty: ProjectedType,
}

/// One variant of the projected message enum.
#[derive(Debug, Clone)]
pub struct MessageVariant {
    /// Variant name (`Req`), derived from the message's `type` tag.
    pub name: String,
    /// The tag as written in the source (`"req"`).
    pub tag: String,
    /// Payload fields, excluding the tag and the routing fields.
    pub fields: Vec<(String, ProjectedType)>,
}

/// The projected shape of a clean-subset module.
#[derive(Debug, Clone)]
pub struct ProjectedSpec {
    pub module_name: String,
    /// The node set as written in the source (`Proc`, `0 .. N - 1`).
    pub node_set: String,
    /// The source spec's network variable, which the projection removes.
    pub network_variable: Option<String>,
    pub state_fields: Vec<StateField>,
    /// Constants other than the node set, plus the implicit `node_id`.
    pub constants: Vec<(String, ProjectedType)>,
    pub messages: Vec<MessageVariant>,
    /// Enums the projection had to introduce, in declaration order: a state
    /// field whose TLA+ type is a set of string literals becomes one.
    pub enums: Vec<(String, Vec<String>)>,
    /// Structs the projection had to introduce: a record set used as a type
    /// becomes one, named after the operator that defines it.
    pub records: Vec<(String, Vec<(String, ProjectedType)>)>,
    /// Operator definitions, so later passes can inline message constructors
    /// and broadcast helpers without re-walking the module.
    pub operator_bodies: BTreeMap<String, (Vec<String>, TlaExpr)>,
    /// Anything the pass could not project, stated plainly rather than guessed.
    pub gaps: Vec<String>,
}

/// Why a module could not be projected at all.
///
/// The report is boxed: carrying it by value makes every `Result` from this
/// module as large as a full lint report, and the error path is the rare one.
#[derive(Debug, Clone)]
pub enum ProjectionError {
    /// The module is not in the clean subset. Projection is only defined there.
    NotClean(Box<CleanSubsetReport>),
}

/// Project a parsed clean-subset module.
pub fn project_module(module: &TlaModule) -> Result<ProjectedSpec, ProjectionError> {
    let report = lint_module(module);
    if !report.is_clean() {
        return Err(ProjectionError::NotClean(Box::new(report)));
    }
    let node_set = report
        .node_set
        .clone()
        .expect("a clean module has a node set");

    let ctx = ProjectionContext {
        module,
        node_set: node_set.clone(),
    };

    let mut gaps = Vec::new();
    let mut messages = ctx.project_messages(&mut gaps);

    let mut state_fields = Vec::new();
    let mut enums = Vec::new();
    let mut records = Vec::new();
    for var in &report.per_node_variables {
        match ctx.projected_state_type(var) {
            Some(mut ty) => {
                // A set of string literals becomes an enum, and it is named
                // after the variable it types -- the source has no name for it.
                // An enum nested inside a record has no variable to be named
                // after, so it takes the record's name and the field's:
                // `Record`'s `status` field becomes `LRecordStatus`. Leaving it
                // unnamed emitted `pub status: ,` -- a field with no type.
                // The record must be named before its nested enums are, so
                // an enum inside an inline record gets the record's name.
                name_anonymous_records(&mut ty, var);
                name_nested_enums(&mut ty, &mut enums);
                if let ProjectedType::Enum { name, variants } = &mut ty {
                    if name.is_empty() {
                        // Raft's variable really is called `state`, and
                        // `LState` is already the projected state struct.
                        let candidate = format!("L{}", to_pascal_case(var));
                        *name = if EMITTED_TYPE_NAMES.contains(&candidate.as_str()) {
                            format!("{candidate}Kind")
                        } else {
                            candidate
                        };
                    }
                    enums.push((name.clone(), variants.clone()));
                }
                collect_records(&ty, &mut records);
                if ty.is_unresolved() {
                    gaps.push(format!("variable `{var}`: {}", ty.render()));
                }
                state_fields.push(StateField {
                    name: to_snake_case(var),
                    source_name: var.clone(),
                    ty,
                });
            }
            None => gaps.push(format!(
                "variable `{var}` is per-node but its element type could not be \
                 read off a declaration"
            )),
        }
    }

    // A message field declared with an inline set of literals --
    // `mresult: {Ok, StaleTerm, EntryMismatch}` -- is an enum the source never
    // named, exactly like an unnamed enum inside a record. Unnamed, it is
    // dropped from `enums` and never declared, and the emitter writes
    // `Resp { res:  }` -- a field with **no type at all**, and a guard
    // `res is Ok` naming a variant of nothing.
    //
    // The same defect was found and fixed for records-in-state (EPaxos's
    // `status`) and the message path was missed. Named after the variant and
    // the field, which is the only naming available: the source has none.
    for variant in &mut messages {
        for (field, ty) in &mut variant.fields {
            name_nested_enums(ty, &mut enums);
            if let ProjectedType::Enum { name, variants } = ty {
                if name.is_empty() {
                    *name = format!(
                        "L{}{}",
                        to_pascal_case(&variant.name),
                        to_pascal_case(field)
                    );
                    if !enums.iter().any(|(n, _)| *n == *name) {
                        enums.push((name.clone(), variants.clone()));
                    }
                }
            }
        }
    }

    let constants = ctx.project_constants();

    Ok(ProjectedSpec {
        module_name: module.name.clone(),
        node_set,
        network_variable: report.network_variable.clone(),
        state_fields,
        constants,
        messages,
        enums,
        records,
        operator_bodies: module
            .operators
            .iter()
            .map(|op| {
                (
                    op.name.clone(),
                    (
                        op.params.iter().map(|p| p.name.clone()).collect(),
                        op.body.clone(),
                    ),
                )
            })
            .collect(),
        gaps,
    })
}

struct ProjectionContext<'a> {
    module: &'a TlaModule,
    node_set: String,
}

impl ProjectedSpec {
    /// The name of the constant that carries the node set in the projected
    /// spec.
    ///
    /// This used to be "the first constant with a set type", which is right
    /// only when the node set is the spec's one set constant. It is not on the
    /// tier4 Jetpack composition: the node set is the *operator*
    /// `Node == Server \cup Client`, so the synthetic constant is appended
    /// after `Server`, `Client`, `Commands`, `CmdId` and `Key` -- and the
    /// heuristic picked `server`. Nothing would have reported that; the spec
    /// would have typechecked and quantified over the wrong set.
    pub fn node_set_constant(&self) -> String {
        let named = to_snake_case(&self.node_set);
        if self.constants.iter().any(|(n, _)| *n == named) {
            return named;
        }
        let synthesised = if self
            .node_set
            .chars()
            .all(|ch| ch.is_alphanumeric() || ch == '_')
        {
            named
        } else {
            "nodes".to_string()
        };
        if self.constants.iter().any(|(n, _)| *n == synthesised) {
            return synthesised;
        }
        // No such constant: keep the historical fallback rather than emitting
        // a name that is certainly wrong.
        self.constants
            .iter()
            .find(|(_, ty)| matches!(ty, ProjectedType::Set(_)))
            .map(|(n, _)| n.clone())
            .unwrap_or_else(|| "procs".to_string())
    }
}

impl ProjectionContext<'_> {
    /// Resolve a 0-ary operator to its body, so `Clock == Nat \ {0}` can be
    /// followed when a variable is declared over `Clock`.
    fn resolve(&self, name: &str) -> Option<&TlaExpr> {
        self.module
            .operators
            .iter()
            .find(|op| op.name == name && op.params.is_empty())
            .map(|op| &op.body)
    }

    /// The projected type of a per-node variable: find its declaration
    /// `x \in [Node -> T]` and project `T`.
    fn projected_state_type(&self, var: &str) -> Option<ProjectedType> {
        for op in &self.module.operators {
            if let Some(ty) = self.find_declaration(&op.body, var) {
                return Some(ty);
            }
        }
        None
    }

    fn find_declaration(&self, expr: &TlaExpr, var: &str) -> Option<ProjectedType> {
        match expr {
            TlaExpr::BinOp {
                op: TlaBinOp::In,
                left,
                right,
            } if matches!(&**left, TlaExpr::Ident(n) if n == var) => {
                // `x \in [Node -> T]` -- project away the outer index.
                if let TlaExpr::FnSet { domain, range } = &**right {
                    if self.renders_as_node_set(domain) {
                        return Some(self.project_type(range));
                    }
                }
                None
            }
            TlaExpr::BinOp { left, right, .. } => self
                .find_declaration(left, var)
                .or_else(|| self.find_declaration(right, var)),
            _ => None,
        }
    }

    fn renders_as_node_set(&self, expr: &TlaExpr) -> bool {
        render_set_expr(expr) == self.node_set
    }

    /// Map a TLA+ type expression onto a Verus type.
    fn project_type(&self, expr: &TlaExpr) -> ProjectedType {
        match expr {
            TlaExpr::Ident(name) => match name.as_str() {
                "Nat" | "Int" | "Integer" => ProjectedType::Int,
                "BOOLEAN" | "Bool" => ProjectedType::Bool,
                other => {
                    // A named set: follow the definition if there is one, and
                    // otherwise treat a node-set-like name as node ids.
                    if let Some(body) = self.resolve(other) {
                        let projected = self.project_type(body);
                        // A record set gets its name from the operator that
                        // defines it: `LogEntry` becomes `LLogEntry`.
                        if let ProjectedType::Record { name, fields } = projected {
                            return ProjectedType::Record {
                                name: if name.is_empty() {
                                    format!("L{}", to_pascal_case(other))
                                } else {
                                    name
                                },
                                fields,
                            };
                        }
                        projected
                    } else if other == self.node_set {
                        ProjectedType::Int
                    } else if self.module.constants.iter().any(|c| c.name == *other) {
                        // An uninterpreted CONSTANT set: its elements are
                        // opaque identifiers with no structure the spec relies
                        // on, so they project to `int`. Paxos's `Value` is one,
                        // and the hand-written tla-rs Paxos represents it the
                        // same way.
                        ProjectedType::Int
                    } else {
                        ProjectedType::Unresolved(format!("unknown set `{other}`"))
                    }
                }
            },
            TlaExpr::Bool(_) => ProjectedType::Bool,
            // `[D -> R]` -- a table indexed by something that is not the node.
            TlaExpr::FnSet { domain, range } => ProjectedType::Map(
                Box::new(self.project_type(domain)),
                Box::new(self.project_type(range)),
            ),
            TlaExpr::UnaryOp {
                op: TlaUnaryOp::Subset,
                operand,
            } => ProjectedType::Set(Box::new(self.project_type(operand))),
            // `Seq(T)`
            TlaExpr::OpApply { op, args } if matches!(&**op, TlaExpr::Ident(n) if n == "Seq") => {
                match args.first() {
                    Some(arg) => ProjectedType::Seq(Box::new(self.project_type(arg))),
                    None => ProjectedType::Unresolved("Seq with no element type".into()),
                }
            }
            // `1 .. N` and other integer ranges are sets of node ids/integers.
            TlaExpr::BinOp {
                op: TlaBinOp::DotDot,
                ..
            } => ProjectedType::Int,
            // `S \ {0}`, `S \cup T` -- the element type is that of either side.
            TlaExpr::BinOp {
                op: TlaBinOp::Setminus | TlaBinOp::Cup | TlaBinOp::Cap,
                left,
                ..
            } => self.project_type(left),
            // A record set is a struct; the caller names it.
            TlaExpr::RecordSet(fields) => ProjectedType::Record {
                name: String::new(),
                fields: fields
                    .iter()
                    .map(|(name, ty)| (to_snake_case(name), self.project_type(ty)))
                    .collect(),
            },
            // A set of string literals is an enumeration. A spec usually names
            // its labels (`Follower == "follower"`) rather than repeating the
            // literal, so a 0-ary operator is followed to the string behind it
            // -- otherwise the set reads as opaque identifiers and the field
            // silently becomes an `int` that string literals are assigned to.
            TlaExpr::SetEnum(items) => {
                let labels: Vec<String> = items
                    .iter()
                    .filter_map(|item| match item {
                        TlaExpr::String(s) => Some(s.clone()),
                        TlaExpr::Ident(name) => match self.resolve(name) {
                            Some(TlaExpr::String(s)) => Some(s.clone()),
                            _ => None,
                        },
                        _ => None,
                    })
                    .collect();
                if labels.len() == items.len() && !labels.is_empty() {
                    ProjectedType::Enum {
                        name: String::new(), // named by the caller, which knows the field
                        variants: labels.iter().map(|l| variant_name_for(l)).collect(),
                    }
                } else if items
                    .iter()
                    .all(|i| matches!(i, TlaExpr::Number(_) | TlaExpr::Ident(_)))
                {
                    ProjectedType::Int
                } else {
                    ProjectedType::Unresolved("set literal of mixed kinds".into())
                }
            }
            other => ProjectedType::Unresolved(format!("type expression {other:?}")),
        }
    }

    /// Constants of the projected spec: the source's `CONSTANT`s, with the node
    /// set kept as a `Set<int>` and `node_id` added, since a projected node
    /// still has to know which node it is.
    fn project_constants(&self) -> Vec<(String, ProjectedType)> {
        let mut out = Vec::new();
        let node_set_is_named_constant = self
            .module
            .constants
            .iter()
            .any(|c| c.name == self.node_set);

        for constant in &self.module.constants {
            let ty = if constant.name == self.node_set || self.used_as_a_set(&constant.name) {
                ProjectedType::Set(Box::new(ProjectedType::Int))
            } else {
                ProjectedType::Int
            };
            out.push((to_snake_case(&constant.name), ty));
        }
        if !node_set_is_named_constant {
            // The node set is a defined operator (`Proc == 1 .. N`), so carry it
            // explicitly: the projected spec quantifies over peers.
            out.push((
                to_snake_case(&self.node_set_field_name()),
                ProjectedType::Set(Box::new(ProjectedType::Int)),
            ));
        }
        out.push(("node_id".to_string(), ProjectedType::Int));
        out
    }

    /// Whether a `CONSTANT` is a set rather than a scalar.
    ///
    /// A `CONSTANT` declaration carries no type, so the spec's *use* is the only
    /// evidence. `\E v \in Value` and `[Value -> T]` both say `Value` is a set;
    /// `MaxBallot` appears in neither and stays an `int`.
    fn used_as_a_set(&self, name: &str) -> bool {
        fn used(expr: &TlaExpr, name: &str) -> bool {
            let here = match expr {
                TlaExpr::BinOp {
                    op: TlaBinOp::In | TlaBinOp::NotIn | TlaBinOp::Subseteq,
                    right,
                    ..
                } => matches!(&**right, TlaExpr::Ident(n) if n == name),
                TlaExpr::FnSet { domain, .. } => {
                    matches!(&**domain, TlaExpr::Ident(n) if n == name)
                }
                // A quantifier's bounding set is not a child expression, so it
                // has to be looked at directly.
                TlaExpr::Exists { vars, .. } | TlaExpr::Forall { vars, .. } => vars
                    .iter()
                    .any(|b| matches!(&b.set, Some(TlaExpr::Ident(n)) if n == name)),
                _ => false,
            };
            here || crate::tla::action_projection::children(expr)
                .into_iter()
                .any(|c| used(c, name))
        }
        self.module.operators.iter().any(|op| used(&op.body, name))
    }

    /// A field name for the node set when it is an expression (`0 .. N - 1`)
    /// rather than a name.
    fn node_set_field_name(&self) -> String {
        if self
            .node_set
            .chars()
            .all(|ch| ch.is_alphanumeric() || ch == '_')
        {
            self.node_set.clone()
        } else {
            "nodes".to_string()
        }
    }

    /// Derive the message enum from the source's `Message == [type: {...}, ...]`
    /// record-set declaration.
    ///
    /// The tag field is what splits the enum: a message set whose `type` field
    /// ranges over string literals has one variant per literal. Routing fields
    /// (`src`, `dst`) are dropped from the payload — after projection they
    /// belong to the packet, not to the message.
    fn project_messages(&self, gaps: &mut Vec<String>) -> Vec<MessageVariant> {
        // The message type may be a single record set, or a union of them --
        // Paxos declares one per phase and unions them. Collecting the union's
        // members keeps both the tag set and the payload complete.
        let mut record_sets: Vec<&Vec<(String, TlaExpr)>> = Vec::new();
        for op in &self.module.operators {
            collect_record_sets(&op.body, &mut record_sets);
        }
        // Only tagged record sets are messages. A spec may declare untagged
        // ones for its own data -- Raft's `LogEntry` is one, and it is declared
        // *before* `Message`, so stopping at the first record set found would
        // take the log entry and then discard it, leaving the spec with no
        // messages at all.
        record_sets.retain(|fields| {
            fields
                .iter()
                .any(|(name, _)| TAG_FIELDS.contains(&name.as_str()))
        });
        if record_sets.is_empty() {
            return Vec::new();
        }

        let mut merged: Vec<(String, TlaExpr)> = Vec::new();
        let mut tag_literals: Vec<TlaExpr> = Vec::new();
        for fields in &record_sets {
            for (name, value) in fields.iter() {
                if TAG_FIELDS.contains(&name.as_str()) {
                    // The tag set may be *named*: `Message == [type: Tags, ..]`
                    // with `Tags == {"a", "b"}`. Reading only a literal
                    // `SetEnum` here dropped every variant behind such a name
                    // -- silently. With one declaration of several written that
                    // way, the emitted spec loses that message kind, its
                    // receive handler becomes unreachable from the dispatch,
                    // `clean-tla` exits 0 with no gap, and Verus reports
                    // `0 verified, 0 errors`. A protocol message disappears and
                    // every check still passes.
                    let resolved = match value {
                        TlaExpr::SetEnum(_) => Some(value.clone()),
                        TlaExpr::Ident(name) => match self.resolve(name) {
                            Some(body @ TlaExpr::SetEnum(_)) => Some(body.clone()),
                            _ => None,
                        },
                        _ => None,
                    };
                    match resolved {
                        Some(TlaExpr::SetEnum(items)) => {
                            for item in &items {
                                if !tag_literals.contains(item) {
                                    tag_literals.push(item.clone());
                                }
                            }
                        }
                        // Anything else is a tag set the projection cannot read,
                        // and guessing would drop messages. Say so.
                        _ => gaps.push(format!(
                            "the message tag field `{name}` is declared as `{}`, \
                             which is not a set of literals the projection can \
                             read -- every message kind behind it would be \
                             dropped from the spec",
                            crate::tla::action_projection::render_source(value)
                        )),
                    }
                } else if !merged.iter().any(|(n, _)| n == name) {
                    merged.push((name.clone(), value.clone()));
                }
            }
        }
        let record_set = &merged;
        // No refutable pattern here: `tag_literals` is built above, so a match
        // on it can only succeed. There *was* one, whose gap message ("message
        // tag field is not a set of literals") could never fire -- the
        // condition it named is real and reachable, but it arrives as an
        // **empty** `tag_literals` and used to fall straight through the loop
        // below producing zero variants. That is now reported where it happens,
        // in the tag harvesting above.
        let tags = tag_literals;

        let payload: Vec<(String, ProjectedType)> = record_set
            .iter()
            .filter(|(name, _)| {
                !TAG_FIELDS.contains(&name.as_str()) && !ROUTING_FIELDS.contains(&name.as_str())
            })
            .map(|(name, ty)| (to_snake_case(name), self.project_type(ty)))
            .collect();

        let mut variants = Vec::new();
        for tag in &tags {
            // A spec usually names its tags (`RequestVoteRequest == "rvq"`),
            // so follow a 0-ary operator to the literal behind it.
            let tag = match tag {
                TlaExpr::String(t) => t.clone(),
                TlaExpr::Ident(name) => match self.resolve(name) {
                    Some(TlaExpr::String(t)) => t.clone(),
                    _ => {
                        gaps.push(format!("message tag `{name}` is not a string literal"));
                        continue;
                    }
                },
                other => {
                    gaps.push(format!("message tag {other:?} is not a string literal"));
                    continue;
                }
            };
            let tag = &tag;
            // A variant carries only the fields its constructor actually fills
            // in. A field a constructor sets to a literal (`clock |-> 0` in an
            // acknowledgement) carries no information and is not payload; the
            // record-set declaration lists it only because every message shares
            // one record type.
            let fields = match self.constructor_payload(tag) {
                Some(informative) => payload
                    .iter()
                    .filter(|(name, _)| informative.contains(name))
                    .cloned()
                    .collect(),
                None => payload.clone(),
            };
            variants.push(MessageVariant {
                name: variant_name_for(tag),
                tag: tag.clone(),
                fields,
            });
        }
        variants
    }

    /// The fields a constructor for `tag` fills with something other than a
    /// literal, i.e. the ones that carry information.
    /// The payload fields a tag's constructors put in the message.
    ///
    /// The **union** across every constructor for that tag, not the first one
    /// found. A spec may have more than one -- a thin form and a form carrying
    /// an extra field -- and taking the first in declaration order meant
    /// swapping two definitions decided whether the variant carried its
    /// payload at all. With the thin one first the emitted variant was
    /// `LMessage::M` with no fields while the handler still referred to `val`,
    /// which is an unbound name; with the other order everything worked.
    ///
    /// The union is what the declared `Message` type already says the variant
    /// holds, so it cannot invent a field, and it cannot drop one either.
    fn constructor_payload(&self, tag: &str) -> Option<Vec<String>> {
        let mut union: Vec<String> = Vec::new();
        let mut seen_any = false;
        for op in &self.module.operators {
            let TlaExpr::Record(fields) = &op.body else {
                continue;
            };
            let tags_match = fields.iter().any(|(name, value)| {
                TAG_FIELDS.contains(&name.as_str())
                    && match value {
                        TlaExpr::String(t) => t == tag,
                        // A constructor usually names its tag rather than
                        // spelling the literal, exactly as the declaration does.
                        TlaExpr::Ident(name) => {
                            matches!(self.resolve(name), Some(TlaExpr::String(t)) if t == tag)
                        }
                        _ => false,
                    }
            });
            if !tags_match {
                continue;
            }
            seen_any = true;
            for (name, value) in fields.iter().filter(|(_, value)| {
                !matches!(
                    value,
                    TlaExpr::Number(_) | TlaExpr::String(_) | TlaExpr::Bool(_)
                )
            }) {
                let _ = value;
                let name = to_snake_case(name);
                if !union.contains(&name) {
                    union.push(name);
                }
            }
        }
        seen_any.then_some(union)
    }
}

/// Collect the struct types a projected type mentions, innermost first.
/// Give every enum nested inside a record a name, and register it.
///
/// A top-level enum is named after the variable it types. One inside a record
/// has no variable, so it is named after the record and the field.
fn name_nested_enums(ty: &mut ProjectedType, enums: &mut Vec<(String, Vec<String>)>) {
    match ty {
        ProjectedType::Record { name, fields } => {
            let record = name.clone();
            for (field, field_ty) in fields.iter_mut() {
                if let ProjectedType::Enum { name, variants } = field_ty {
                    if name.is_empty() {
                        *name = format!("{record}{}", to_pascal_case(field));
                        if !enums.iter().any(|(n, _)| *n == *name) {
                            enums.push((name.clone(), variants.clone()));
                        }
                    }
                } else {
                    name_nested_enums(field_ty, enums);
                }
            }
        }
        ProjectedType::Set(inner) | ProjectedType::Seq(inner) => name_nested_enums(inner, enums),
        ProjectedType::Map(k, v) => {
            name_nested_enums(k, enums);
            name_nested_enums(v, enums);
        }
        _ => {}
    }
}

/// Name a record type that the source never named.
///
/// A type invariant may state the record inline --
/// `pendingReconfig \in [Node -> [op: .., target: ..]]` -- rather than through
/// a named operator like `Config == [id: .., members: .., committed: ..]`.
/// A nameless record is dropped by [`collect_records`], so nothing declares it
/// and every value of that shape then fails to match a declared type: four of
/// the tier4 composition's gaps were this one record.
///
/// Named after the variable it types, exactly as an unnamed nested enum is
/// named after the record and field it sits in.
fn name_anonymous_records(ty: &mut ProjectedType, var: &str) {
    match ty {
        ProjectedType::Record { name, fields } => {
            if name.is_empty() {
                *name = format!("L{}", to_pascal_case(var));
            }
            for (_, field_ty) in fields.iter_mut() {
                name_anonymous_records(field_ty, var);
            }
        }
        ProjectedType::Set(inner) | ProjectedType::Seq(inner) => name_anonymous_records(inner, var),
        ProjectedType::Map(k, v) => {
            name_anonymous_records(k, var);
            name_anonymous_records(v, var);
        }
        _ => {}
    }
}

fn collect_records(ty: &ProjectedType, out: &mut Vec<(String, Vec<(String, ProjectedType)>)>) {
    match ty {
        ProjectedType::Record { name, fields } => {
            for (_, field_ty) in fields {
                collect_records(field_ty, out);
            }
            if !name.is_empty() && !out.iter().any(|(n, _)| n == name) {
                out.push((name.clone(), fields.clone()));
            }
        }
        ProjectedType::Set(inner) | ProjectedType::Seq(inner) => collect_records(inner, out),
        ProjectedType::Map(k, v) => {
            collect_records(k, out);
            collect_records(v, out);
        }
        _ => {}
    }
}

/// Collect record sets out of an expression, following `\cup` unions.
fn collect_record_sets<'e>(expr: &'e TlaExpr, out: &mut Vec<&'e Vec<(String, TlaExpr)>>) {
    match expr {
        TlaExpr::RecordSet(fields) => out.push(fields),
        TlaExpr::BinOp {
            op: TlaBinOp::Cup,
            left,
            right,
        } => {
            collect_record_sets(left, out);
            collect_record_sets(right, out);
        }
        _ => {}
    }
}

/// Render a set expression the way the linter does, so node-set comparisons
/// agree between the two.
fn render_set_expr(expr: &TlaExpr) -> String {
    use crate::verus2tla::TlaPrinter;
    TlaPrinter::new().print_expr(expr, 0).trim().to_string()
}

/// `sendSeq` -> `send_seq`, `req` -> `req`, `N` -> `n`.
pub fn to_snake_case(name: &str) -> String {
    let mut out = String::with_capacity(name.len() + 4);
    for (i, ch) in name.chars().enumerate() {
        // `!` is TLA+'s INSTANCE qualifier: `B!Entry` is `Entry` of the module
        // instantiated as `B`. It is part of the name and it is not a legal
        // Rust identifier character, so it becomes the separator it already is.
        // Without this the tier4 composition emitted `LB!Entry` and
        // `LJ!IsFastQuorum` -- output that does not parse.
        if ch == '!' {
            if !out.is_empty() && !out.ends_with('_') {
                out.push('_');
            }
        } else if ch.is_uppercase() {
            if i != 0 && !out.ends_with('_') {
                out.push('_');
            }
            out.extend(ch.to_lowercase());
        } else {
            out.push(ch);
        }
    }
    out
}

/// `pc` -> `Pc`, `send_seq` -> `SendSeq`.
pub fn to_pascal_case(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    let mut capitalize = true;
    for ch in name.chars() {
        // See `to_snake_case`: `!` is the INSTANCE qualifier, so like `_` it
        // separates words rather than appearing in the identifier.
        if ch == '_' || ch == '!' {
            capitalize = true;
        } else if capitalize {
            out.extend(ch.to_uppercase());
            capitalize = false;
        } else {
            out.push(ch);
        }
    }
    out
}

/// `"req"` -> `Req`.
pub fn variant_name_for(tag: &str) -> String {
    // A tag need not be a Rust identifier. Paxos's phases are "1a", "1b", "2a"
    // and "2b", and EPaxos's statuses are "pre-accepted" and "committed" --
    // `LMessage::1a` and `LRecordStatus::Pre-accepted` both fail to parse.
    // Word-split on anything that is not alphanumeric, PascalCase the parts,
    // and prefix `M` when the result would start with a digit.
    let mut out = String::new();
    for word in tag.split(|c: char| !c.is_alphanumeric()) {
        let mut chars = word.chars();
        if let Some(first) = chars.next() {
            out.extend(first.to_uppercase());
            out.push_str(chars.as_str());
        }
    }
    match out.chars().next() {
        Some(first) if !first.is_alphabetic() => format!("M{out}"),
        Some(_) => out,
        None => String::new(),
    }
}

/// Field names of the projected state, for callers that only need the shape.
pub fn state_field_map(spec: &ProjectedSpec) -> BTreeMap<String, String> {
    spec.state_fields
        .iter()
        .map(|f| (f.source_name.clone(), f.ty.render()))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tla::parse_module;

    fn project(source: &str) -> ProjectedSpec {
        let module = parse_module(source).expect("test spec must parse");
        match project_module(&module) {
            Ok(spec) => spec,
            Err(ProjectionError::NotClean(report)) => {
                panic!("test spec must be clean, got {:?}", report.findings)
            }
        }
    }

    fn field(spec: &ProjectedSpec, name: &str) -> String {
        spec.state_fields
            .iter()
            .find(|f| f.source_name == name)
            .unwrap_or_else(|| panic!("no state field `{name}` in {:?}", spec.state_fields))
            .ty
            .render()
    }

    #[test]
    fn projects_away_the_node_index() {
        let source = r#"---- MODULE Test ----
VARIABLES clock, crit
TypeOK == /\ clock \in [Proc -> Nat]
          /\ crit \in [Proc -> BOOLEAN]
Step(p) == clock' = [clock EXCEPT ![p] = 0]
Next == \E p \in Proc : Step(p)
===="#;
        let spec = project(source);
        assert_eq!(field(&spec, "clock"), "int");
        assert_eq!(field(&spec, "crit"), "bool");
        assert!(spec.gaps.is_empty(), "unexpected gaps: {:?}", spec.gaps);
    }

    #[test]
    fn keeps_the_inner_index_of_a_two_level_array() {
        // The case that matters: [Node -> [Node -> Nat]] is this node's table
        // about its peers, so exactly one index is removed.
        let source = r#"---- MODULE Test ----
VARIABLES req
TypeOK == req \in [Proc -> [Proc -> Nat]]
Step(p) == req' = [req EXCEPT ![p][p] = 0]
Next == \E p \in Proc : Step(p)
===="#;
        let spec = project(source);
        assert_eq!(
            field(&spec, "req"),
            "Map<int, int>",
            "dropping both indices would delete the node's knowledge of its peers"
        );
    }

    #[test]
    fn projects_set_and_sequence_valued_state() {
        let source = r#"---- MODULE Test ----
VARIABLES ack, log
TypeOK == /\ ack \in [Proc -> SUBSET Proc]
          /\ log \in [Proc -> Seq(Nat)]
Step(p) == ack' = ack
Next == \E p \in Proc : Step(p)
===="#;
        let spec = project(source);
        assert_eq!(field(&spec, "ack"), "Set<int>");
        assert_eq!(field(&spec, "log"), "Seq<int>");
    }

    #[test]
    fn follows_a_named_set_definition() {
        // `Clock == Nat \ {0}` -- the declaration names a defined set.
        let source = r#"---- MODULE Test ----
VARIABLES clock
Clock == Nat \ {0}
TypeOK == clock \in [Proc -> Clock]
Step(p) == clock' = clock
Next == \E p \in Proc : Step(p)
===="#;
        let spec = project(source);
        assert_eq!(field(&spec, "clock"), "int");
    }

    #[test]
    fn derives_the_message_enum_from_the_tag_field() {
        let source = r#"---- MODULE Test ----
VARIABLES clock
Message == [type: {"req", "ack"}, src: Proc, dst: Proc, seq: Nat]
TypeOK == clock \in [Proc -> Nat]
Step(p) == clock' = clock
Next == \E p \in Proc : Step(p)
===="#;
        let spec = project(source);
        let names: Vec<&str> = spec.messages.iter().map(|m| m.name.as_str()).collect();
        assert_eq!(names, vec!["Req", "Ack"]);
        let payload: Vec<&str> = spec.messages[0]
            .fields
            .iter()
            .map(|(n, _)| n.as_str())
            .collect();
        assert_eq!(
            payload,
            vec!["seq"],
            "routing fields belong to the packet after projection, not the message"
        );
    }

    #[test]
    fn adds_node_id_to_the_constants() {
        // A projected node still has to know which node it is: the source
        // spec's `self` becomes `c.node_id`.
        let source = r#"---- MODULE Test ----
CONSTANT N
VARIABLES clock
Proc == 1 .. N
TypeOK == clock \in [Proc -> Nat]
Step(p) == clock' = clock
Next == \E p \in Proc : Step(p)
===="#;
        let spec = project(source);
        let names: Vec<&str> = spec.constants.iter().map(|(n, _)| n.as_str()).collect();
        assert!(names.contains(&"node_id"), "got {names:?}");
        assert!(names.contains(&"n"), "source constants are kept: {names:?}");
    }

    #[test]
    fn refuses_to_project_a_module_that_is_not_clean() {
        let source = r#"---- MODULE Test ----
VARIABLES x
TypeOK == x \in [Proc -> Nat]
Step(p) == x' = [x EXCEPT ![p] = x[p + 1]]
Next == \E p \in Proc : Step(p)
===="#;
        let module = parse_module(source).unwrap();
        match project_module(&module) {
            Err(ProjectionError::NotClean(report)) => {
                assert!(!report.is_clean());
            }
            Ok(spec) => panic!("a C2-violating spec must not project: {spec:?}"),
        }
    }

    #[test]
    fn reports_an_unresolvable_element_type_instead_of_guessing() {
        let source = r#"---- MODULE Test ----
VARIABLES weird
TypeOK == weird \in [Proc -> Mystery]
Step(p) == weird' = weird
Next == \E p \in Proc : Step(p)
===="#;
        let spec = project(source);
        assert!(
            !spec.gaps.is_empty(),
            "an unknown element type must be reported, not silently become int"
        );
        assert!(field(&spec, "weird").contains("unresolved"));
    }

    #[test]
    fn names_an_enum_after_the_variable_it_types() {
        // The source has no name for `{"a", "b", "Done"}`; it is the type of
        // `pc`, so that is what it is called.
        let source = r#"---- MODULE Test ----
VARIABLES pc
TypeOK == pc \in [Proc -> {"a", "b", "Done"}]
Step(p) == pc' = pc
Next == \E p \in Proc : Step(p)
===="#;
        let spec = project(source);
        assert_eq!(field(&spec, "pc"), "LPc");
        assert_eq!(
            spec.enums,
            vec![(
                "LPc".to_string(),
                vec!["A".to_string(), "B".to_string(), "Done".to_string()]
            )]
        );
    }
}
