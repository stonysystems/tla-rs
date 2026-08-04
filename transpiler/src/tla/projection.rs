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
    let messages = ctx.project_messages(&mut gaps);

    let mut state_fields = Vec::new();
    let mut enums = Vec::new();
    for var in &report.per_node_variables {
        match ctx.projected_state_type(var) {
            Some(mut ty) => {
                // A set of string literals becomes an enum, and it is named
                // after the variable it types -- the source has no name for it.
                if let ProjectedType::Enum { name, variants } = &mut ty {
                    if name.is_empty() {
                        *name = format!("L{}", to_pascal_case(var));
                    }
                    enums.push((name.clone(), variants.clone()));
                }
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

    let constants = ctx.project_constants();

    Ok(ProjectedSpec {
        module_name: module.name.clone(),
        node_set,
        network_variable: report.network_variable.clone(),
        state_fields,
        constants,
        messages,
        enums,
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
                        self.project_type(body)
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
            // A set of string literals is an enumeration.
            TlaExpr::SetEnum(items) => {
                let labels: Vec<String> = items
                    .iter()
                    .filter_map(|item| match item {
                        TlaExpr::String(s) => Some(s.clone()),
                        _ => None,
                    })
                    .collect();
                if labels.len() == items.len() && !labels.is_empty() {
                    ProjectedType::Enum {
                        name: String::new(), // named by the caller, which knows the field
                        variants: labels.iter().map(|l| to_variant_name(l)).collect(),
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
            let ty = if constant.name == self.node_set {
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
        const TAG_FIELDS: &[&str] = &["type", "kind", "tag"];
        const ROUTING_FIELDS: &[&str] = &["src", "dst", "source", "dest", "sender", "receiver"];

        // The message type may be a single record set, or a union of them --
        // Paxos declares one per phase and unions them. Collecting the union's
        // members keeps both the tag set and the payload complete.
        let mut record_sets: Vec<&Vec<(String, TlaExpr)>> = Vec::new();
        for op in &self.module.operators {
            collect_record_sets(&op.body, &mut record_sets);
            if !record_sets.is_empty() {
                break;
            }
        }
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
                    if let TlaExpr::SetEnum(items) = value {
                        for item in items {
                            if !tag_literals.contains(item) {
                                tag_literals.push(item.clone());
                            }
                        }
                    }
                } else if !merged.iter().any(|(n, _)| n == name) {
                    merged.push((name.clone(), value.clone()));
                }
            }
        }
        let record_set = &merged;
        let tag_expr = TlaExpr::SetEnum(tag_literals);

        let TlaExpr::SetEnum(tags) = &tag_expr else {
            gaps.push("message tag field is not a set of literals".into());
            return Vec::new();
        };

        let payload: Vec<(String, ProjectedType)> = record_set
            .iter()
            .filter(|(name, _)| {
                !TAG_FIELDS.contains(&name.as_str()) && !ROUTING_FIELDS.contains(&name.as_str())
            })
            .map(|(name, ty)| (to_snake_case(name), self.project_type(ty)))
            .collect();

        let mut variants = Vec::new();
        for tag in tags {
            let TlaExpr::String(tag) = tag else {
                gaps.push(format!("message tag {tag:?} is not a string literal"));
                continue;
            };
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
                name: to_variant_name(tag),
                tag: tag.clone(),
                fields,
            });
        }
        variants
    }

    /// The fields a constructor for `tag` fills with something other than a
    /// literal, i.e. the ones that carry information.
    fn constructor_payload(&self, tag: &str) -> Option<Vec<String>> {
        for op in &self.module.operators {
            let TlaExpr::Record(fields) = &op.body else {
                continue;
            };
            let tags_match = fields.iter().any(|(name, value)| {
                matches!(name.as_str(), "type" | "kind" | "tag")
                    && matches!(value, TlaExpr::String(t) if t == tag)
            });
            if !tags_match {
                continue;
            }
            return Some(
                fields
                    .iter()
                    .filter(|(_, value)| {
                        !matches!(
                            value,
                            TlaExpr::Number(_) | TlaExpr::String(_) | TlaExpr::Bool(_)
                        )
                    })
                    .map(|(name, _)| to_snake_case(name))
                    .collect(),
            );
        }
        None
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
        if ch.is_uppercase() {
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
        if ch == '_' {
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
fn to_variant_name(tag: &str) -> String {
    let mut chars = tag.chars();
    match chars.next() {
        // A tag need not be a Rust identifier: Paxos's phases are "1a", "1b",
        // "2a" and "2b", and `LMessage::1a` does not parse. A leading `M` makes
        // it one without losing the tag.
        Some(first) if !first.is_alphabetic() => format!("M{tag}"),
        Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
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
