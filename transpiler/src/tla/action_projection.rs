//! Action projection (Phase 52.M1.b): a clean-subset action becomes a
//! single-node action predicate.
//!
//! [`crate::tla::projection`] decides the projected spec's *types*; this module
//! decides its *actions*. For each operator the linter identifies as acting on
//! behalf of a node, it produces the conjuncts of the corresponding
//! `LFoo(s, s_, c, .., sent_packets)` predicate:
//!
//! - reads of the acting node's state (`x[self]`) become `s.x`;
//! - updates (`x' = [x EXCEPT ![self] = e]`) become `s_.x == e`;
//! - a send (`net' = net \cup S`) becomes `sent_packets == S`;
//! - a receive's message fields become parameters, because delivery is the
//!   framework's job after projection;
//! - **P5**: every state field the action does not update gets an explicit
//!   `s_.f == s.f`, which is the conjunct hand-written specs most often forget.
//!
//! Anything this pass cannot project is recorded as a gap. It never guesses:
//! an action that silently loses a conjunct is worse than one that is reported
//! as unfinished, because the result still looks like a spec.

use std::collections::BTreeMap;

use crate::tla::ast::{TlaBinOp, TlaExceptPath, TlaExpr, TlaModule, TlaUnaryOp};
use crate::tla::clean_subset::node_parameterized_operators;
use crate::tla::projection::{
    to_snake_case, ProjectedSpec, ProjectedType, ProjectionError, ROUTING_FIELDS, TAG_FIELDS,
};

/// How an action is reached.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ActionKind {
    /// Taken spontaneously by the node.
    Local,
    /// Taken on receipt of a message; the message's fields are parameters.
    Receive,
}

/// A helper operator kept as its own projected spec function.
///
/// Helpers are *not* inlined by default. Keeping `beats` as `Lbeats` preserves
/// the source spec's own factoring, so a human can match the output against the
/// input concept by concept — which is the point of a deterministic translator.
/// The exception is a helper the call site hands the received *message*: after
/// projection the message is destructured into parameters, so that signature
/// cannot survive and the helper must be inlined.
#[derive(Debug, Clone)]
pub struct ProjectedHelper {
    pub name: String,
    pub source_name: String,
    /// Whether the helper reads node state, i.e. whether it needs `s`.
    pub reads_state: bool,
    /// Parameters beyond `s` and `c`, in source order with the node parameter
    /// removed.
    pub params: Vec<String>,
    pub body: String,
    /// The helper's result type, decided from the TLA+ body rather than from
    /// the emitted text: `IF Len(l) = 0 THEN 0 ELSE l[Len(l)].term` reads like
    /// a predicate if all you have is the string.
    pub return_type: Option<String>,
    pub gaps: Vec<String>,
}

/// Marks an identifier whose text is already projected Verus, so the projector
/// passes it through instead of trying to resolve it as a TLA+ name.
const PROJECTED_MARK: &str = "\u{1}";

/// Marker for a conjunct that the dispatch consumes rather than the action.
const DISPATCH_PREFIX: &str = "\u{0}dispatch:";

/// A projected action predicate.
#[derive(Debug, Clone)]
pub struct ProjectedAction {
    /// Name in the projected spec (`LRequest`).
    pub name: String,
    /// Name in the source spec (`Request`).
    pub source_name: String,
    pub kind: ActionKind,
    /// Parameters beyond `s`, `s_`, `c` and `sent_packets`.
    pub params: Vec<String>,
    /// For each parameter, the membership its `Next` binder imposed
    /// (`\E b \in Ballot`), projected. Dropping it would let `LNext` take
    /// transitions the source spec forbids.
    pub param_bounds: Vec<Option<String>>,
    /// Conjuncts in source order, already rendered as Verus.
    pub conjuncts: Vec<String>,
    /// P5 frame conditions for the fields this action leaves alone.
    pub frame: Vec<String>,
    /// The message tag this action handles, when it is a receive. The dispatch
    /// matches on it; the action itself no longer states it.
    pub handles_tag: Option<String>,
    /// What could not be projected. A non-empty list means the action is not
    /// finished, and the emitter must not present it as if it were.
    pub gaps: Vec<String>,
}

/// Everything the projection produces for one module.
#[derive(Debug, Clone)]
pub struct ProjectedModule {
    pub spec: ProjectedSpec,
    pub helpers: Vec<ProjectedHelper>,
    pub actions: Vec<ProjectedAction>,
    /// Conjuncts of the projected `LInit`.
    pub init: Vec<String>,
    pub init_gaps: Vec<String>,
}

/// Project `Init` to this node's initial state.
///
/// `Init` says what every node starts with (`clock = [p \in Proc |-> 1]`), so
/// projecting it is reading off the per-node value. The network's initial value
/// has no counterpart: after projection there is no network in the state.
fn project_init(module: &TlaModule, spec: &ProjectedSpec) -> (Vec<String>, Vec<String>) {
    let Some(init) = module.operators.iter().find(|o| o.name == "Init") else {
        return (
            Vec::new(),
            vec!["no `Init` operator: the spec has no initial state".to_string()],
        );
    };

    // `Init` is not a node action, so it has no node parameter. The binder of
    // each function constructor plays that role for the conjunct it heads.
    let ctx = ActionContext {
        spec,
        param_types: Default::default(),
        msg_tag: None,
        node_param: String::new(),
        msg_param: None,
        network: spec.network_variable.clone(),
    };

    let mut conjuncts = Vec::new();
    let mut gaps = Vec::new();
    for conjunct in flatten_conjunction(&init.body) {
        let TlaExpr::BinOp {
            op: TlaBinOp::Eq,
            left,
            right,
        } = conjunct
        else {
            gaps.push(format!("`Init` conjunct {}", render_source(conjunct)));
            continue;
        };
        let TlaExpr::Ident(var) = &**left else {
            gaps.push(format!("`Init` conjunct {}", render_source(conjunct)));
            continue;
        };
        if ctx.is_network(var) {
            continue; // the network is not part of the projected state
        }
        let Some(field) = ctx.state_field(var) else {
            gaps.push(format!("`Init` sets unknown variable `{var}`"));
            continue;
        };
        // `[p \in Node |-> v]` -- the node's own initial value is `v`.
        // `[p \in Node |-> v]` gives this node's value directly; the binder is
        // the node for the purposes of that conjunct.
        let (inner_expr, node_ctx);
        match &**right {
            TlaExpr::FnConstruct {
                var: binder, body, ..
            } => {
                node_ctx = ActionContext {
                    spec,
                    param_types: Default::default(),
                    msg_tag: None,
                    node_param: binder.clone(),
                    msg_param: None,
                    network: spec.network_variable.clone(),
                };
                inner_expr = &**body;
            }
            other => {
                node_ctx = ActionContext {
                    spec,
                    param_types: Default::default(),
                    msg_tag: None,
                    node_param: String::new(),
                    msg_param: None,
                    network: spec.network_variable.clone(),
                };
                inner_expr = other;
            }
        }

        if let Some(variant) = node_ctx.enum_variant(field, inner_expr) {
            conjuncts.push(format!("s.{field} is {variant}"));
            continue;
        }
        if let Some(ty) = node_ctx.field_type(field).cloned() {
            if let Some(text) = node_ctx.typed_value(&ty, inner_expr) {
                conjuncts.push(format!("s.{field} == {text}"));
                continue;
            }
        }
        match node_ctx.project_expr(inner_expr) {
            Ok(text) => conjuncts.push(format!("s.{field} == {text}")),
            Err(gap) => gaps.push(format!("`Init` for `{var}`: {gap}")),
        }
    }
    (conjuncts, gaps)
}

/// Project a clean-subset module end to end.
///
/// Constants are pruned to those the projected output actually references. The
/// source's `N` defines the node set, which projection turns into a constant in
/// its own right, and `maxClock` exists only for a model-checking constraint
/// that does not project — carrying either into the spec would state knobs the
/// spec does not use.
pub fn project(module: &TlaModule) -> Result<ProjectedModule, ProjectionError> {
    let mut spec = crate::tla::projection::project_module(module)?;
    let helpers = project_helpers(module, &spec);
    let actions = project_actions(module, &spec);

    let mut texts: Vec<&String> = Vec::new();
    for helper in &helpers {
        texts.push(&helper.body);
    }
    for action in &actions {
        texts.extend(action.param_bounds.iter().flatten());
        texts.extend(action.conjuncts.iter());
        texts.extend(action.frame.iter());
    }
    spec.constants.retain(|(name, _)| {
        name == "node_id" || texts.iter().any(|t| references_constant(t, name))
    });

    let (init, init_gaps) = project_init(module, &spec);

    Ok(ProjectedModule {
        spec,
        helpers,
        actions,
        init,
        init_gaps,
    })
}

/// Whether `text` references `c.<name>` as a whole field, not as a prefix of a
/// longer one — `c.n` must not be found inside `c.node_id`.
fn references_constant(text: &str, name: &str) -> bool {
    let needle = format!("c.{name}");
    let mut from = 0;
    while let Some(at) = text[from..].find(&needle) {
        let end = from + at + needle.len();
        let next = text[end..].chars().next();
        if !next.is_some_and(|ch| ch.is_alphanumeric() || ch == '_') {
            return true;
        }
        from = end;
    }
    false
}

/// Project the helpers a module's actions call **as functions**.
///
/// Only helpers that survive projection are emitted. A message constructor or a
/// broadcast is inlined at its use site, and a helper handed the received
/// message cannot keep its signature; emitting those would produce definitions
/// nothing calls, and in the constructors' case ones that cannot be projected
/// at all. So the set is taken from what action projection actually referenced.
pub fn project_helpers(module: &TlaModule, spec: &ProjectedSpec) -> Vec<ProjectedHelper> {
    let called = called_helpers(module, spec);
    let param_types = infer_helper_param_types(module, spec);
    let node_params = node_parameterized_operators(module);
    let mut helpers = Vec::new();

    // Driven by what the actions call, not by which operators take a node.
    // `IsMajority(s)` takes a *set*, so it is not node-parameterized, but the
    // actions call it and the emitted spec would not compile without it.
    for op_name in &called {
        let node_param = node_params.get(op_name).cloned().unwrap_or_default();
        let node_param = &node_param;
        let Some(op) = module.operators.iter().find(|o| o.name == *op_name) else {
            continue;
        };
        // Actions are handled by `project_actions`; helpers are the rest.
        if mentions_prime(&op.body) {
            continue;
        }
        let ctx = ActionContext {
            spec,
            param_types: op
                .params
                .iter()
                .map(|p| {
                    (
                        safe_param_name(&p.name),
                        param_types
                            .get(&(op.name.clone(), p.name.clone()))
                            .cloned()
                            .unwrap_or(ProjectedType::Int),
                    )
                })
                .collect(),
            msg_tag: None,
            node_param: node_param.clone(),
            msg_param: None,
            network: spec.network_variable.clone(),
        };
        // The signature renames parameters that would collide with the
        // projected spec's own `s`, `s_` and `c`; the body has to agree.
        let mut renamed = op.body.clone();
        for param in &op.params {
            let safe = safe_param_name(&param.name);
            if safe != param.name {
                renamed = substitute(&renamed, &param.name, &TlaExpr::Ident(safe));
            }
        }
        let (body, gaps) = match ctx.project_expr(&renamed) {
            Ok(text) => (text, Vec::new()),
            Err(gap) => (String::new(), vec![gap]),
        };
        helpers.push(ProjectedHelper {
            name: format!("L{op_name}"),
            source_name: op_name.clone(),
            reads_state: reads_state(&op.body, spec),
            params: op
                .params
                .iter()
                .filter(|p| p.name != *node_param)
                .map(|p| {
                    format!(
                        "{}: {}",
                        safe_param_name(&p.name),
                        param_types
                            .get(&(op.name.clone(), p.name.clone()))
                            .map(|t| t.render())
                            .unwrap_or_else(|| helper_param_type(op, &p.name).to_string())
                    )
                })
                .collect(),
            return_type: ctx.value_type(&renamed).map(|t| t.render()),
            body,
            gaps,
        });
    }

    helpers.sort_by_key(|h| {
        module
            .operators
            .iter()
            .position(|o| o.name == h.source_name)
            .unwrap_or(usize::MAX)
    });
    helpers
}

/// Helper names that action projection emitted calls to.
fn called_helpers(module: &TlaModule, spec: &ProjectedSpec) -> std::collections::BTreeSet<String> {
    let mut called = std::collections::BTreeSet::new();
    for action in project_actions(module, spec) {
        for text in action.conjuncts.iter().chain(action.frame.iter()) {
            for op in module.operators.iter() {
                if text.contains(&format!("L{}(", op.name)) {
                    called.insert(op.name.clone());
                }
            }
        }
    }
    called
}

/// A parameter name that cannot collide with the projected spec's own `s`,
/// `s_` and `c`. A source spec is free to name a parameter `s`, and Paxos's
/// `IsMajority(s)` does exactly that.
fn safe_param_name(name: &str) -> String {
    let snake = to_snake_case(name);
    match snake.as_str() {
        "s" | "s_" | "c" => format!("{snake}_arg"),
        _ => snake,
    }
}

/// A helper parameter's type: a set when the body counts it, otherwise an
/// identifier.
/// The type of each helper parameter, read off the *call sites*.
///
/// `LastTerm(log[i])` says more about `LastTerm`'s parameter than its body
/// does: the argument is a per-node state field, so the parameter has that
/// field's projected type -- `Seq<LLogEntry>`, not the `Seq<int>` a
/// body-shape heuristic would guess. Where no call site is informative the
/// caller falls back to `helper_param_type`.
fn infer_helper_param_types(
    module: &TlaModule,
    spec: &ProjectedSpec,
) -> BTreeMap<(String, String), ProjectedType> {
    fn argument_type(arg: &TlaExpr, spec: &ProjectedSpec) -> Option<ProjectedType> {
        let name = match arg {
            // `log[i]` -- one node's slice of a per-node variable.
            TlaExpr::FnApply { func, .. } => match &**func {
                TlaExpr::Ident(name) => name,
                _ => return None,
            },
            TlaExpr::Ident(name) => name,
            _ => return None,
        };
        spec.state_fields
            .iter()
            .find(|f| f.source_name == *name)
            .map(|f| f.ty.clone())
    }

    fn walk(
        expr: &TlaExpr,
        module: &TlaModule,
        spec: &ProjectedSpec,
        out: &mut BTreeMap<(String, String), ProjectedType>,
    ) {
        if let TlaExpr::OpApply { op, args } = expr {
            if let TlaExpr::Ident(callee) = &**op {
                if let Some(target) = module.operators.iter().find(|o| o.name == *callee) {
                    for (param, arg) in target.params.iter().zip(args.iter()) {
                        if let Some(ty) = argument_type(arg, spec) {
                            out.insert((callee.clone(), param.name.clone()), ty);
                        }
                    }
                }
            }
        }
        for child in children(expr) {
            walk(child, module, spec, out);
        }
    }

    let mut out = BTreeMap::new();
    for op in &module.operators {
        walk(&op.body, module, spec, &mut out);
    }
    out
}

fn helper_param_type(op: &crate::tla::ast::TlaOperator, param: &str) -> &'static str {
    fn counted(expr: &TlaExpr, param: &str) -> bool {
        if let TlaExpr::OpApply { op, args } = expr {
            if matches!(&**op, TlaExpr::Ident(n) if n == "Cardinality")
                && args
                    .iter()
                    .any(|a| matches!(a, TlaExpr::Ident(n) if n == param))
            {
                return true;
            }
        }
        children(expr).into_iter().any(|c| counted(c, param))
    }
    fn measured(expr: &TlaExpr, param: &str) -> bool {
        if let TlaExpr::OpApply { op, args } = expr {
            if matches!(&**op, TlaExpr::Ident(n) if n == "Len")
                && args
                    .iter()
                    .any(|a| matches!(a, TlaExpr::Ident(n) if n == param))
            {
                return true;
            }
        }
        children(expr).into_iter().any(|c| measured(c, param))
    }
    if counted(&op.body, param) {
        "Set<int>"
    } else if measured(&op.body, param) {
        "Seq<int>"
    } else {
        "int"
    }
}

/// The set each action parameter is drawn from in `Next`.
///
/// `Next == \E a \in Acceptor : \E b \in Ballot : Phase1a(a, b)` says `b`
/// ranges over `Ballot`. The action body does not repeat that, so without this
/// the projected `LNext` quantifies over every integer and admits ballots the
/// source spec has no state for.
fn action_param_bounds(module: &TlaModule) -> BTreeMap<(String, String), TlaExpr> {
    fn walk(
        expr: &TlaExpr,
        scope: &BTreeMap<String, TlaExpr>,
        module: &TlaModule,
        out: &mut BTreeMap<(String, String), TlaExpr>,
    ) {
        match expr {
            TlaExpr::Exists { vars, body } | TlaExpr::Forall { vars, body } => {
                let mut inner = scope.clone();
                for bound in vars {
                    match &bound.set {
                        Some(set) => {
                            inner.insert(bound.var.clone(), set.clone());
                        }
                        None => {
                            inner.remove(&bound.var);
                        }
                    }
                }
                walk(body, &inner, module, out);
                return;
            }
            TlaExpr::OpApply { op, args } => {
                if let TlaExpr::Ident(callee) = &**op {
                    if let Some(target) = module.operators.iter().find(|o| o.name == *callee) {
                        for (param, arg) in target.params.iter().zip(args.iter()) {
                            if let TlaExpr::Ident(binder) = arg {
                                if let Some(set) = scope.get(binder) {
                                    out.insert((callee.clone(), param.name.clone()), set.clone());
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        for child in children(expr) {
            walk(child, scope, module, out);
        }
    }

    let mut out = BTreeMap::new();
    if let Some(next) = module.operators.iter().find(|o| o.name == "Next") {
        walk(&next.body, &BTreeMap::new(), module, &mut out);
    }
    out
}

/// Whether an expression reads any per-node state, i.e. whether the projected
/// helper needs an `s` parameter at all.
fn reads_state(expr: &TlaExpr, spec: &ProjectedSpec) -> bool {
    if let TlaExpr::Ident(name) = expr {
        return spec.state_fields.iter().any(|f| f.source_name == *name);
    }
    children(expr).into_iter().any(|c| reads_state(c, spec))
}

/// Project every action of a module that the linter accepted.
pub fn project_actions(module: &TlaModule, spec: &ProjectedSpec) -> Vec<ProjectedAction> {
    let receives = receive_handlers(module, spec.network_variable.as_deref());
    let bounds = action_param_bounds(module);
    let mut actions = Vec::new();

    for (op_name, node_param) in node_parameterized_operators(module) {
        let Some(op) = module.operators.iter().find(|o| o.name == op_name) else {
            continue;
        };
        // Helper predicates (no primed state) are not actions; they are
        // translated as ordinary spec functions elsewhere.
        if !mentions_prime(&op.body) {
            continue;
        }

        let msg_param = receives.get(&op_name).cloned();
        let mut ctx = ActionContext {
            spec,
            param_types: Default::default(),
            msg_tag: None,
            node_param: node_param.clone(),
            msg_param: msg_param.clone(),
            network: spec.network_variable.clone(),
        };
        // Which variant the action handles is settled by its `m.type = ...`
        // guard, and it has to be known *before* the body is projected: the
        // variant is what gives `m.field` a type, and a field's type is what
        // decides how indexing it projects.
        ctx.msg_tag = ctx.message_tag(&op.body);
        let ctx = ctx;

        let mut conjuncts = Vec::new();
        let mut gaps = Vec::new();
        let mut updated: Vec<String> = Vec::new();
        let mut sends_seen = false;

        let mut handles_tag = None;
        for conjunct in flatten_conjunction(&op.body) {
            match ctx.project_conjunct(conjunct, &mut updated, &mut sends_seen) {
                Ok(text) => {
                    if let Some(tag) = text.strip_prefix(DISPATCH_PREFIX) {
                        if !tag.is_empty() {
                            handles_tag = Some(tag.to_string());
                        }
                    } else if !text.is_empty() {
                        conjuncts.push(text);
                    }
                }
                Err(gap) => gaps.push(gap),
            }
        }

        // P5: state the action leaves alone.
        let mut frame = Vec::new();
        for field in &spec.state_fields {
            if !updated.contains(&field.name) {
                frame.push(format!("s_.{} == s.{}", field.name, field.name));
            }
        }
        // An action that sends nothing still has to say so, or `sent_packets`
        // would be unconstrained and the action would permit any output.
        if !sends_seen {
            frame.push("sent_packets == Set::<LPacket>::empty()".to_string());
        }

        // A receive's parameters are the sender plus the payload of the variant
        // it handles: the message itself does not survive projection, so every
        // field the action reads has to arrive as a parameter.
        let params = if msg_param.is_some() {
            // The sender is passed only when the handler uses it. The framework
            // always knows it; declaring it unused would put a parameter in the
            // spec that the spec does not talk about.
            let uses_src = conjuncts.iter().any(|c| {
                c.split(|ch: char| !ch.is_alphanumeric() && ch != '_')
                    .any(|w| w == "src")
            });
            let mut params = if uses_src {
                vec!["src: int".to_string()]
            } else {
                Vec::new()
            };
            if let Some(tag) = &handles_tag {
                if let Some(variant) = spec.messages.iter().find(|m| m.tag == *tag) {
                    params.extend(
                        variant
                            .fields
                            .iter()
                            .map(|(name, ty)| format!("{name}: {}", ty.render())),
                    );
                }
            }
            params
        } else {
            // A local action's own parameters survive, minus the node: the
            // source's `Phase1a(a, b)` is this node starting ballot `b`.
            op.params
                .iter()
                .filter(|p| p.name != node_param)
                .map(|p| format!("{}: int", to_snake_case(&p.name)))
                .collect()
        };

        // A receive's parameters are message fields, which the framework
        // types; only a local action's own binders carry a set.
        let param_bounds = if msg_param.is_some() {
            vec![None; params.len()]
        } else {
            op.params
                .iter()
                .filter(|p| p.name != node_param)
                .map(|p| {
                    let set = bounds.get(&(op_name.clone(), p.name.clone()))?;
                    ctx.project_expr(&TlaExpr::BinOp {
                        op: TlaBinOp::In,
                        left: Box::new(TlaExpr::Ident(p.name.clone())),
                        right: Box::new(set.clone()),
                    })
                    .ok()
                })
                .collect()
        };

        actions.push(ProjectedAction {
            name: format!("L{op_name}"),
            source_name: op_name.clone(),
            kind: if msg_param.is_some() {
                ActionKind::Receive
            } else {
                ActionKind::Local
            },
            params,
            param_bounds,
            conjuncts,
            frame,
            handles_tag,
            gaps,
        });
    }

    // Source order, not alphabetical: the output is meant to be read beside the
    // spec it came from.
    actions.sort_by_key(|a| {
        module
            .operators
            .iter()
            .position(|o| o.name == a.source_name)
            .unwrap_or(usize::MAX)
    });
    actions
}

struct ActionContext<'a> {
    spec: &'a ProjectedSpec,
    /// Types of the operator's own parameters, as far as they are known. A
    /// parameter's type decides whether indexing it is 1-based (a sequence) or
    /// a key lookup (a map), which is not recoverable from its spelling.
    param_types: BTreeMap<String, ProjectedType>,
    /// The message tag this action handles, which names the message variant
    /// whose field types apply to `m.field`.
    msg_tag: Option<String>,
    /// The name the acting node goes by inside this action (`self`, `p`).
    node_param: String,
    /// The name the received message goes by, when this is a receive.
    msg_param: Option<String>,
    network: Option<String>,
}

impl ActionContext<'_> {
    fn state_field(&self, var: &str) -> Option<&str> {
        self.spec
            .state_fields
            .iter()
            .find(|f| f.source_name == var)
            .map(|f| f.name.as_str())
    }

    /// The projected type of a state field.
    fn field_type(&self, field: &str) -> Option<&crate::tla::projection::ProjectedType> {
        self.spec
            .state_fields
            .iter()
            .find(|f| f.name == field)
            .map(|f| &f.ty)
    }

    /// A string literal assigned to an enum-typed field names a variant, and
    /// Verus spells that `x is Variant` rather than an equality.
    fn enum_variant(&self, field: &str, expr: &TlaExpr) -> Option<String> {
        let ProjectedType::Enum { variants, .. } = self.field_type(field)? else {
            return None;
        };
        // The source may name the label rather than spelling it.
        let literal = match expr {
            TlaExpr::String(literal) => literal.clone(),
            TlaExpr::Ident(_) => self.resolve_tag(expr)?,
            _ => return None,
        };
        let wanted = variant_name(&literal);
        variants.iter().find(|v| **v == wanted).cloned()
    }

    /// Render a value in a position whose type is known, which is what makes
    /// `Set::<int>::empty()` and the `int` suffix inside a `Map::new` closure
    /// possible -- Verus cannot infer either from the expression alone.
    fn typed_value(
        &self,
        ty: &crate::tla::projection::ProjectedType,
        expr: &TlaExpr,
    ) -> Option<String> {
        use crate::tla::projection::ProjectedType;
        match (ty, expr) {
            (ProjectedType::Set(inner), TlaExpr::SetEnum(items)) if items.is_empty() => {
                Some(format!("Set::<{}>::empty()", inner.render()))
            }
            (ProjectedType::Seq(inner), TlaExpr::Tuple(items)) if items.is_empty() => {
                Some(format!("Seq::<{}>::empty()", inner.render()))
            }
            (ProjectedType::Map(_, value_ty), TlaExpr::FnConstruct { var, domain, body }) => {
                let set = self.project_node_set(domain).ok()?;
                let inner = ActionContext {
                    spec: self.spec,
                    param_types: Default::default(),
                    msg_tag: None,
                    node_param: self.node_param.clone(),
                    msg_param: self.msg_param.clone(),
                    network: self.network.clone(),
                };
                let value = inner.project_expr_with_binder(body, var).ok()?;
                // A bare integer literal in a closure body has no type to infer
                // from; the suffix is what makes the map's value type explicit.
                let value = if matches!(**body, TlaExpr::Number(_))
                    && matches!(**value_ty, ProjectedType::Int)
                {
                    format!("{value}int")
                } else {
                    value
                };
                Some(format!("Map::new({set}, |{var}: int| {value})"))
            }
            _ => None,
        }
    }

    fn is_network(&self, var: &str) -> bool {
        self.network.as_deref() == Some(var)
    }

    /// Classify and project one conjunct of an action body.
    fn project_conjunct(
        &self,
        expr: &TlaExpr,
        updated: &mut Vec<String>,
        sends_seen: &mut bool,
    ) -> Result<String, String> {
        // `x' = e`
        if let TlaExpr::BinOp {
            op: TlaBinOp::Eq,
            left,
            right,
        } = expr
        {
            if let TlaExpr::Prime(inner) = &**left {
                if let TlaExpr::Ident(var) = &**inner {
                    if self.is_network(var) {
                        *sends_seen = true;
                        return self.project_send(right);
                    }
                    let Some(field) = self.state_field(var) else {
                        return Err(format!("update of unknown variable `{var}`"));
                    };
                    // `x' = x` is a frame conjunct written the other way --
                    // PlusCal-generated specs use it instead of UNCHANGED.
                    // P5 regenerates the frame, so it is dropped like UNCHANGED.
                    if matches!(&**right, TlaExpr::Ident(rhs) if rhs == var) {
                        return Ok(String::new());
                    }
                    updated.push(field.to_string());
                    // The value actually assigned to this node's component: for
                    // `[x EXCEPT ![self] = v]` that is `v`, not the EXCEPT
                    // wrapped around it. Typed rendering needs the value.
                    let assigned = assigned_value(right, |e| self.is_node_index(e));
                    if let Some(variant) = self.enum_variant(field, assigned) {
                        return Ok(format!("s_.{field} is {variant}"));
                    }
                    if let Some(ty) = self.field_type(field).cloned() {
                        if let Some(text) = self.typed_value(&ty, assigned) {
                            return Ok(format!("s_.{field} == {text}"));
                        }
                    }
                    return Ok(format!(
                        "s_.{field} == {}",
                        self.project_update(var, right)?
                    ));
                }
            }
        }

        // `IF c THEN /\ x' = a /\ y' = b  ELSE /\ x' = a2 /\ y' = b2`.
        //
        // A very common TLA+ shape, and one that cannot be read as a guard:
        // the branches assign, so each assigned variable becomes a single
        // conjunct whose value is the conditional. Both branches must assign
        // the same variables, which is what makes that rewrite sound.
        if let TlaExpr::IfThenElse {
            cond,
            then_expr,
            else_expr,
        } = expr
        {
            let then_updates = self.branch_updates(then_expr);
            let else_updates = self.branch_updates(else_expr);
            if !then_updates.is_empty() && then_updates.len() == else_updates.len() {
                let mut rendered = Vec::new();
                for (var, then_value) in &then_updates {
                    let Some((_, else_value)) = else_updates.iter().find(|(v, _)| v == var) else {
                        return Err(format!(
                            "conditional assigns `{var}` in one branch only; both \
                             branches must assign the same variables"
                        ));
                    };
                    // A conditional that sends in both branches is a send whose
                    // value is the conditional.
                    if self.is_network(var) {
                        *sends_seen = true;
                        rendered.push(format!(
                            "sent_packets == if {} {{ {} }} else {{ {} }}",
                            self.project_expr(cond)?,
                            self.collect_sent_or_empty(then_value)?,
                            self.collect_sent_or_empty(else_value)?
                        ));
                        continue;
                    }
                    let Some(_) = else_updates.iter().find(|(v, _)| v == var) else {
                        return Err(format!(
                            "conditional assigns `{var}` in one branch only; both \
                             branches must assign the same variables"
                        ));
                    };
                    let Some(field) = self.state_field(var) else {
                        return Err(format!("conditional update of unknown variable `{var}`"));
                    };
                    updated.push(field.to_string());
                    rendered.push(format!(
                        "s_.{field} == if {} {{ {} }} else {{ {} }}",
                        self.project_expr(cond)?,
                        self.project_branch_value(var, then_value)?,
                        self.project_branch_value(var, else_value)?
                    ));
                }
                return Ok(rendered.join("\n        &&& "));
            }
        }

        // Guards the dispatch already enforces. `m.dst = self` is guaranteed
        // by the framework once delivery is its job, and `m.type = "req"` is
        // what selects the variant in the generated `match`. Emitting them
        // again would restate in the action what the caller has established.
        if let Some(tag) = self.dispatch_guard(expr) {
            return Ok(DISPATCH_PREFIX.to_string() + &tag);
        }

        // `UNCHANGED <<a, b>>` -- the source's own frame conjuncts. They are
        // dropped, because P5 regenerates the frame from what the action
        // actually updates; keeping both would state it twice.
        if matches!(expr, TlaExpr::Unchanged(_)) {
            return Ok(String::new());
        }

        // Anything else is a guard.
        self.project_expr(expr)
    }

    /// Whether a conjunct is a guard the message dispatch already enforces:
    /// `m.dst = self` (delivery) or `m.type = "tag"` (variant selection).
    /// Returns the tag when it is a variant selection, so the caller can route
    /// the action, and an empty string for the delivery guard.
    fn dispatch_guard(&self, expr: &TlaExpr) -> Option<String> {
        let msg = self.msg_param.as_deref()?;
        let TlaExpr::BinOp {
            op: TlaBinOp::Eq,
            left,
            right,
        } = expr
        else {
            return None;
        };
        let TlaExpr::RecordAccess { record, field } = &**left else {
            return None;
        };
        if !matches!(&**record, TlaExpr::Ident(n) if n == msg) {
            return None;
        }
        // Which spellings a spec uses for "who is this for" and "what kind is
        // it" is style; the projection recognises the same set everywhere.
        if ROUTING_FIELDS.contains(&field.as_str())
            && matches!(&**right, TlaExpr::Ident(n) if *n == self.node_param)
        {
            return Some(String::new());
        }
        if TAG_FIELDS.contains(&field.as_str()) {
            return self.resolve_tag(right);
        }
        None
    }

    /// `net' = net \cup S` (possibly with a `\ {m}` for the consumed message).
    fn project_send(&self, rhs: &TlaExpr) -> Result<String, String> {
        let sent = self.collect_sent(rhs)?;
        if sent.is_empty() {
            // The action only consumed the message it was handling.
            return Ok("sent_packets == Set::<LPacket>::empty()".to_string());
        }
        Ok(format!("sent_packets == {sent}"))
    }

    /// The packets a network update adds, or an explicit empty set.
    fn collect_sent_or_empty(&self, expr: &TlaExpr) -> Result<String, String> {
        let sent = self.collect_sent(expr)?;
        if sent.is_empty() {
            Ok("Set::<LPacket>::empty()".to_string())
        } else {
            Ok(sent)
        }
    }

    /// Pull the *added* messages out of a network update, ignoring the removal
    /// of the message being consumed -- after projection the framework owns
    /// delivery, so consuming is not something the node states.
    fn collect_sent(&self, expr: &TlaExpr) -> Result<String, String> {
        match expr {
            // `network \ {m}` -- consumption only, nothing sent.
            TlaExpr::BinOp {
                op: TlaBinOp::Setminus,
                left,
                ..
            } => self.collect_sent(left),
            TlaExpr::BinOp {
                op: TlaBinOp::Cup,
                left,
                right,
            } => {
                let l = self.collect_sent(left)?;
                let r = self.collect_sent(right)?;
                match (l.as_str(), r.as_str()) {
                    ("", other) | (other, "") => Ok(other.to_string()),
                    (a, b) => Ok(format!("{a}.union({b})")),
                }
            }
            // The network variable itself contributes nothing to what is sent.
            TlaExpr::Ident(name) if self.is_network(name) => Ok(String::new()),
            // `{Ctor(args)}` -- a singleton send.
            TlaExpr::SetEnum(items) if items.len() == 1 => {
                Ok(format!("set![{}]", self.project_packet(&items[0])?))
            }
            // `BroadcastX(args)` -- an operator whose body is a set
            // comprehension over the peers.
            TlaExpr::OpApply { .. } => self.project_broadcast(expr),
            _ => Err(format!(
                "send expression not yet projectable: {}",
                render_source(expr)
            )),
        }
    }

    /// Resolve a message-constructor application into an `LPacket`.
    ///
    /// A clean spec builds messages through operators like
    /// `ReqMessage(s, d, c) == [type |-> "req", src |-> s, dst |-> d, clock |-> c]`.
    /// The constructor is inlined -- its parameters substituted by the call's
    /// arguments -- and the resulting record split into the packet's `dst` and
    /// the message variant's payload.
    fn project_packet(&self, expr: &TlaExpr) -> Result<String, String> {
        let record = self.inline_record(expr)?;

        let mut dst = None;
        let mut tag = None;
        let mut fields = Vec::new();
        for (name, value) in &record {
            match name.as_str() {
                "dst" | "mdest" => dst = Some(self.project_expr(value)?),
                "type" | "kind" | "tag" | "mtype" => match self.resolve_tag(value) {
                    Some(t) => tag = Some(t),
                    None => {
                        return Err(format!(
                            "message tag {} is not a literal",
                            render_source(value)
                        ))
                    }
                },
                // `src` is the sender: after projection that is this node, and
                // the framework stamps it on the packet.
                "src" | "source" | "sender" | "msource" => {}
                // The variant declaration decides which fields a message
                // carries. Deciding it again here -- "this argument happens to
                // be a literal, so drop it" -- would leave a construction that
                // does not fill the variant it names.
                other if !self.variant_carries(&tag, other) => {}
                other => fields.push((to_snake_case(other), self.project_expr(value)?)),
            }
        }

        let (Some(dst), Some(tag)) = (dst, tag) else {
            return Err(format!(
                "message {} has no destination or no tag",
                render_source(expr)
            ));
        };
        let variant = variant_name(&tag);
        let payload = if fields.is_empty() {
            String::new()
        } else {
            format!(
                " {{ {} }}",
                fields
                    .iter()
                    .map(|(n, v)| format!("{n}: {v}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        Ok(format!(
            "LPacket {{ dst: {dst}, msg: LMessage::{variant}{payload} }}"
        ))
    }

    /// A broadcast operator: `Broadcast(s, ..) == { Ctor(s, d, ..) : d \in Node \ {s} }`.
    fn project_broadcast(&self, expr: &TlaExpr) -> Result<String, String> {
        let TlaExpr::SetMap {
            expr: body,
            var,
            set,
        } = self.inline_call(expr)?
        else {
            return Err(format!(
                "send expression not yet projectable: {}",
                render_source(expr)
            ));
        };
        // The comprehension ranges over the peers; the projected form maps the
        // peer set to packets.
        let peers = self.project_peer_set(&set)?;
        let packet = ActionContext {
            spec: self.spec,
            param_types: Default::default(),
            msg_tag: None,
            node_param: self.node_param.clone(),
            msg_param: self.msg_param.clone(),
            network: self.network.clone(),
        }
        .project_packet_with_binder(&body, &var)?;
        Ok(format!("{peers}.map(|{var}: int| {packet})"))
    }

    /// `Proc \ {self}` -> `c.procs.remove(c.node_id)`.
    fn project_peer_set(&self, expr: &TlaExpr) -> Result<String, String> {
        match expr {
            TlaExpr::BinOp {
                op: TlaBinOp::Setminus,
                left,
                right,
            } => {
                let base = self.project_node_set(left)?;
                if let TlaExpr::SetEnum(items) = &**right {
                    if items.len() == 1 && self.is_node_index(&items[0]) {
                        return Ok(format!("{base}.remove(c.node_id)"));
                    }
                }
                Err(format!("peer set {}", render_source(expr)))
            }
            other => self.project_node_set(other),
        }
    }

    fn project_node_set(&self, expr: &TlaExpr) -> Result<String, String> {
        let rendered = render_source(expr);
        if rendered == self.spec.node_set {
            let name = self
                .spec
                .constants
                .iter()
                .find(|(_, ty)| matches!(ty, ProjectedType::Set(_)))
                .map(|(n, _)| n.clone())
                .unwrap_or_else(|| "procs".to_string());
            Ok(format!("c.{name}"))
        } else {
            Err(format!("node set {rendered}"))
        }
    }

    /// Like `project_packet`, but with a comprehension binder in scope so
    /// `d` resolves to the loop variable rather than to a constant.
    fn project_packet_with_binder(&self, expr: &TlaExpr, binder: &str) -> Result<String, String> {
        let record = self.inline_record(expr)?;
        let mut dst = None;
        let mut tag = None;
        let mut fields = Vec::new();
        for (name, value) in &record {
            let projected = |v: &TlaExpr| -> Result<String, String> {
                if matches!(v, TlaExpr::Ident(n) if n == binder) {
                    Ok(binder.to_string())
                } else {
                    self.project_expr_with_binder(v, binder)
                }
            };
            match name.as_str() {
                "dst" | "mdest" => dst = Some(projected(value)?),
                "type" | "kind" | "tag" | "mtype" => match self.resolve_tag(value) {
                    Some(t) => tag = Some(t),
                    None => {
                        return Err(format!(
                            "message tag {} is not a literal",
                            render_source(value)
                        ))
                    }
                },
                "src" | "source" | "sender" | "msource" => {}
                other if !self.variant_carries(&tag, other) => {}
                other => fields.push((to_snake_case(other), projected(value)?)),
            }
        }
        let (Some(dst), Some(tag)) = (dst, tag) else {
            return Err("broadcast message has no destination or no tag".to_string());
        };
        let variant = variant_name(&tag);
        let payload = if fields.is_empty() {
            String::new()
        } else {
            format!(
                " {{ {} }}",
                fields
                    .iter()
                    .map(|(n, v)| format!("{n}: {v}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        Ok(format!(
            "LPacket {{ dst: {dst}, msg: LMessage::{variant}{payload} }}"
        ))
    }

    fn project_expr_with_binder(&self, expr: &TlaExpr, binder: &str) -> Result<String, String> {
        // Reads indexed by the comprehension binder: `sendSeq[s][d]` -> the
        // node's table at `d`.
        if let TlaExpr::FnApply { func, arg } = expr {
            if matches!(arg.as_ref(), TlaExpr::Ident(n) if n == binder) {
                if let TlaExpr::FnApply {
                    func: inner,
                    arg: outer,
                } = &**func
                {
                    if let TlaExpr::Ident(var) = &**inner {
                        if let (Some(field), true) =
                            (self.state_field(var), self.is_node_index(outer))
                        {
                            return Ok(format!("s.{field}[{binder}]"));
                        }
                    }
                }
            }
        }
        self.project_expr(expr)
    }

    /// Inline a call to a 1-body operator, substituting its parameters.
    fn inline_call(&self, expr: &TlaExpr) -> Result<TlaExpr, String> {
        let TlaExpr::OpApply { op, args } = expr else {
            return Ok(expr.clone());
        };
        let TlaExpr::Ident(name) = &**op else {
            return Err(format!("call {}", render_source(expr)));
        };
        let Some((params, body)) = self.spec.operator_bodies.get(name.as_str()).cloned() else {
            return Err(format!("unknown operator `{name}`"));
        };
        if params.len() != args.len() {
            return Err(format!("arity mismatch calling `{name}`"));
        }
        let mut result = body;
        for (param, arg) in params.iter().zip(args.iter()) {
            result = substitute(&result, param, arg);
        }
        Ok(result)
    }

    /// Inline a constructor call and require the result to be a record.
    fn inline_record(&self, expr: &TlaExpr) -> Result<Vec<(String, TlaExpr)>, String> {
        match self.inline_call(expr)? {
            TlaExpr::Record(fields) => Ok(fields),
            other => Err(format!("message expression {}", render_source(&other))),
        }
    }

    /// The `x' = e` assignments in one branch of a conditional.
    fn branch_updates<'e>(&self, expr: &'e TlaExpr) -> Vec<(String, &'e TlaExpr)> {
        let mut out = Vec::new();
        for conjunct in flatten_conjunction(expr) {
            if let TlaExpr::BinOp {
                op: TlaBinOp::Eq,
                left,
                right,
            } = conjunct
            {
                if let TlaExpr::Prime(inner) = &**left {
                    if let TlaExpr::Ident(var) = &**inner {
                        out.push((var.clone(), &**right));
                    }
                }
            }
        }
        out
    }

    /// The value a branch assigns, projected. A branch that re-assigns the
    /// variable to itself (`promiseBal' = promiseBal`) means "leave it", which
    /// after projection is this node's current value.
    fn project_branch_value(&self, var: &str, value: &TlaExpr) -> Result<String, String> {
        if matches!(value, TlaExpr::Ident(name) if name == var) {
            let field = self
                .state_field(var)
                .ok_or_else(|| format!("unknown variable `{var}`"))?;
            return Ok(format!("s.{field}"));
        }
        self.project_update(var, value)
    }

    /// The right-hand side of `x' = ...`, projected to the new value of the
    /// node's field.
    fn project_update(&self, var: &str, rhs: &TlaExpr) -> Result<String, String> {
        let Some(field) = self.state_field(var) else {
            return Err(format!("update of unknown variable `{var}`"));
        };

        match rhs {
            // `[x EXCEPT ![self] = e]` -- the node's own entry.
            TlaExpr::FnExcept { func, updates } => {
                if !matches!(&**func, TlaExpr::Ident(name) if name == var) {
                    return Err(format!("EXCEPT over `{}`", render_source(func)));
                }
                if updates.len() != 1 {
                    return Err(format!(
                        "EXCEPT with {} updates is not yet projectable",
                        updates.len()
                    ));
                }
                let update = &updates[0];
                // `@` inside an EXCEPT is the component's old value. What that
                // is depends on the path, so it is substituted before the value
                // is projected.
                let old_value = match update.path.as_slice() {
                    [TlaExceptPath::Index(index)] if self.is_node_index(index) => {
                        TlaExpr::Ident(format!("{PROJECTED_MARK}s.{field}"))
                    }
                    [TlaExceptPath::Index(outer), TlaExceptPath::Index(inner)]
                        if self.is_node_index(outer) =>
                    {
                        TlaExpr::FnApply {
                            func: Box::new(TlaExpr::Ident(format!("{PROJECTED_MARK}s.{field}"))),
                            arg: Box::new(inner.clone()),
                        }
                    }
                    _ => TlaExpr::Ident("@".to_string()),
                };
                let value_expr = substitute(&update.value, "@", &old_value);
                let value = self.project_expr(&value_expr)?;
                match update.path.as_slice() {
                    // `![self] = e` -- one index, the acting node: the whole
                    // projected field becomes `e`.
                    [TlaExceptPath::Index(index)] if self.is_node_index(index) => Ok(value),
                    // `![self][q] = e` -- the outer index is the node and goes,
                    // the inner one indexes the projected table.
                    [TlaExceptPath::Index(outer), TlaExceptPath::Index(inner)]
                        if self.is_node_index(outer) =>
                    {
                        let key = self.project_expr(inner)?;
                        Ok(format!("s.{field}.insert({key}, {value})"))
                    }
                    other => Err(format!(
                        "EXCEPT path with {} components is not yet projectable",
                        other.len()
                    )),
                }
            }
            // `x' = IF c THEN x ELSE [x EXCEPT ...]`. Each branch is an assigned
            // value in its own right, so a branch naming the variable means
            // "leave it alone" rather than being a bare cross-node read.
            TlaExpr::IfThenElse {
                cond,
                then_expr,
                else_expr,
            } => Ok(format!(
                "if {} {{ {} }} else {{ {} }}",
                self.project_expr(cond)?,
                self.project_branch_value(var, then_expr)?,
                self.project_branch_value(var, else_expr)?
            )),
            other => self.project_expr(other),
        }
    }

    /// A message tag as a string, following a 0-ary operator when the spec
    /// names its tags (`RequestVoteRequest == "rvq"`), which is the usual style.
    fn resolve_tag(&self, expr: &TlaExpr) -> Option<String> {
        match expr {
            TlaExpr::String(t) => Some(t.clone()),
            TlaExpr::Ident(name) => match self.spec.operator_bodies.get(name.as_str()) {
                Some((params, TlaExpr::String(t))) if params.is_empty() => Some(t.clone()),
                _ => None,
            },
            _ => None,
        }
    }

    /// The bounds of an integer range, following a name to its definition:
    /// a spec writes `\E b \in Ballot` and defines `Ballot == 0 .. MaxBallot`
    /// rather than spelling the range at the binder.
    fn as_range(&self, expr: &TlaExpr) -> Option<(TlaExpr, TlaExpr)> {
        match expr {
            TlaExpr::BinOp {
                op: TlaBinOp::DotDot,
                left,
                right,
            } => Some(((**left).clone(), (**right).clone())),
            TlaExpr::Ident(name) => match self.spec.operator_bodies.get(name.as_str()) {
                Some((params, body)) if params.is_empty() => self.as_range(&body.clone()),
                _ => None,
            },
            _ => None,
        }
    }

    /// The variants a set literal names, when the left-hand side is an
    /// enum-typed field and every element resolves to one of its labels.
    fn enum_variants_of(&self, left: &TlaExpr, right: &TlaExpr) -> Option<Vec<String>> {
        let field = self
            .project_expr(left)
            .ok()?
            .strip_prefix("s.")?
            .to_string();
        let TlaExpr::SetEnum(items) = right else {
            return None;
        };
        if items.is_empty() {
            return None;
        }
        items
            .iter()
            .map(|item| self.enum_variant(&field, item))
            .collect()
    }

    /// The type of a value expression, as far as the projection can tell.
    /// Unlike `type_of` this also recognises the expression *forms* that are
    /// boolean or numeric regardless of what they mention.
    fn value_type(&self, expr: &TlaExpr) -> Option<ProjectedType> {
        match expr {
            TlaExpr::Bool(_) | TlaExpr::Forall { .. } | TlaExpr::Exists { .. } => {
                Some(ProjectedType::Bool)
            }
            TlaExpr::UnaryOp {
                op: TlaUnaryOp::Not,
                ..
            } => Some(ProjectedType::Bool),
            TlaExpr::BinOp { op, .. } => match op {
                TlaBinOp::And
                | TlaBinOp::Or
                | TlaBinOp::Implies
                | TlaBinOp::Iff
                | TlaBinOp::In
                | TlaBinOp::NotIn
                | TlaBinOp::Subseteq
                | TlaBinOp::Eq
                | TlaBinOp::Neq
                | TlaBinOp::Lt
                | TlaBinOp::Gt
                | TlaBinOp::Leq
                | TlaBinOp::Geq => Some(ProjectedType::Bool),
                TlaBinOp::Plus
                | TlaBinOp::Minus
                | TlaBinOp::Times
                | TlaBinOp::Div
                | TlaBinOp::Mod
                | TlaBinOp::Caret => Some(ProjectedType::Int),
                _ => None,
            },
            TlaExpr::Number(_) => Some(ProjectedType::Int),
            // A conditional has the type of whichever branch says something.
            // `IF Len(l) = 0 THEN 0 ELSE l[Len(l)].term` is an int by both.
            TlaExpr::IfThenElse {
                then_expr,
                else_expr,
                ..
            } => self
                .value_type(then_expr)
                .or_else(|| self.value_type(else_expr)),
            other => self.type_of(other),
        }
    }

    /// Whether the variant for `tag` declares `field`. A record set lists the
    /// union of every message's fields, so a given variant carries only some
    /// of them.
    fn variant_carries(&self, tag: &Option<String>, field: &str) -> bool {
        let field = to_snake_case(field);
        match tag
            .as_deref()
            .and_then(|t| self.spec.messages.iter().find(|m| m.tag == t))
        {
            Some(variant) => variant.fields.iter().any(|(f, _)| *f == field),
            // The tag is read from the same record, and a well-formed spec puts
            // it first; if it has not been seen yet, keep the field rather than
            // silently dropping it.
            None => true,
        }
    }

    /// The message variant an action handles, read off its `m.type = "aeq"`
    /// guard.
    fn message_tag(&self, body: &TlaExpr) -> Option<String> {
        let msg = self.msg_param.as_deref()?;
        for conjunct in flatten_conjunction(body) {
            if let TlaExpr::BinOp {
                op: TlaBinOp::Eq,
                left,
                right,
            } = conjunct
            {
                if let TlaExpr::RecordAccess { record, field } = &**left {
                    if TAG_FIELDS.contains(&field.as_str())
                        && matches!(&**record, TlaExpr::Ident(n) if n == msg)
                    {
                        if let Some(tag) = self.resolve_tag(right) {
                            return Some(tag);
                        }
                    }
                }
            }
        }
        None
    }

    /// The projected type of an expression, where the projection knows it.
    /// Used to decide index arithmetic, which is not recoverable from the
    /// expression's spelling.
    fn type_of(&self, expr: &TlaExpr) -> Option<ProjectedType> {
        match expr {
            TlaExpr::Ident(name) => self.param_types.get(name.as_str()).cloned(),
            TlaExpr::RecordAccess { record, field } => {
                let field = to_snake_case(field);
                if matches!(&**record, TlaExpr::Ident(n) if Some(n) == self.msg_param.as_ref()) {
                    let tag = self.msg_tag.as_deref()?;
                    let variant = self.spec.messages.iter().find(|m| m.tag == tag)?;
                    return variant
                        .fields
                        .iter()
                        .find(|(f, _)| *f == field)
                        .map(|(_, t)| t.clone());
                }
                match self.type_of(record)? {
                    ProjectedType::Record { fields, .. } => fields
                        .iter()
                        .find(|(f, _)| *f == field)
                        .map(|(_, t)| t.clone()),
                    _ => None,
                }
            }
            TlaExpr::FnApply { func, arg } => {
                // `x[self]` is the whole projected field.
                if let TlaExpr::Ident(var) = &**func {
                    if self.is_node_index(arg) {
                        if let Some(f) = self
                            .spec
                            .state_fields
                            .iter()
                            .find(|f| f.source_name == *var)
                        {
                            return Some(f.ty.clone());
                        }
                    }
                }
                match self.type_of(func)? {
                    ProjectedType::Seq(elem) => Some(*elem),
                    ProjectedType::Map(_, value) => Some(*value),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// A TLA+ sequence index, projected. TLA+ counts from 1 and Verus's `Seq`
    /// from 0, so the index loses one; a literal is folded so the common case
    /// reads naturally.
    fn seq_index(&self, index: &TlaExpr) -> Result<String, String> {
        if let TlaExpr::Number(n) = index {
            if let Some(v) = n.to_i64() {
                return Ok((v - 1).to_string());
            }
        }
        Ok(format!("{} - 1", self.parenthesised(index, 7)?))
    }

    /// Project an index into a state field.
    ///
    /// **TLA+ sequences are 1-indexed and Verus's `Seq` is 0-indexed.** An
    /// index into a sequence therefore loses one; an index into a map is a key
    /// and must not be touched. Getting this wrong produces an off-by-one that
    /// still verifies, which is why it is decided from the field's projected
    /// type rather than guessed.
    fn project_index(&self, field: &str, index: &TlaExpr) -> Result<String, String> {
        let text = self.project_expr(index)?;
        match self.field_type(field) {
            Some(ProjectedType::Seq(_)) => {
                // A literal is folded so the common case reads naturally.
                if let TlaExpr::Number(n) = index {
                    if let Some(v) = n.to_i64() {
                        return Ok((v - 1).to_string());
                    }
                }
                Ok(format!("{text} - 1"))
            }
            _ => Ok(text),
        }
    }

    /// Whether an index expression denotes the acting node.
    fn is_node_index(&self, expr: &TlaExpr) -> bool {
        matches!(expr, TlaExpr::Ident(name) if *name == self.node_param)
    }

    /// Project an expression to Verus text.
    fn project_expr(&self, expr: &TlaExpr) -> Result<String, String> {
        match expr {
            // `x[self]` -- this node's field; `x[self][q]` -- into its table.
            TlaExpr::FnApply { func, arg } => {
                if let TlaExpr::Ident(var) = &**func {
                    if let Some(field) = self.state_field(var) {
                        if self.is_node_index(arg) {
                            return Ok(format!("s.{field}"));
                        }
                        return Err(format!(
                            "read of `{var}` at a node other than the acting one"
                        ));
                    }
                }
                if let TlaExpr::FnApply {
                    func: inner_func,
                    arg: outer_index,
                } = &**func
                {
                    if let TlaExpr::Ident(var) = &**inner_func {
                        if let Some(field) = self.state_field(var) {
                            if self.is_node_index(outer_index) {
                                let field = field.to_string();
                                return Ok(format!(
                                    "s.{field}[{}]",
                                    self.project_index(&field, arg)?
                                ));
                            }
                        }
                    }
                }
                // Anything else whose type the projection knows: a helper's
                // own parameter, a sequence-valued message field. The type is
                // what decides whether the index loses one, so an expression
                // of unknown type is a gap rather than a guess.
                match self.type_of(func) {
                    Some(ProjectedType::Seq(_)) => Ok(format!(
                        "{}[{}]",
                        self.parenthesised(func, 9)?,
                        self.seq_index(arg)?
                    )),
                    Some(ProjectedType::Map(..)) => Ok(format!(
                        "{}[{}]",
                        self.parenthesised(func, 9)?,
                        self.project_expr(arg)?
                    )),
                    _ => Err(format!("application {}", render_source(expr))),
                }
            }
            // The acting node's own identity.
            TlaExpr::Ident(name) if *name == self.node_param => Ok("c.node_id".to_string()),
            // Text the projector itself substituted in (the old value of an
            // EXCEPT component); it is already projected.
            TlaExpr::Ident(name) if name.starts_with(PROJECTED_MARK) => {
                Ok(name.trim_start_matches(PROJECTED_MARK).to_string())
            }
            TlaExpr::Ident(name) => {
                if self
                    .spec
                    .constants
                    .iter()
                    .any(|(c, _)| *c == to_snake_case(name))
                {
                    Ok(format!("c.{}", to_snake_case(name)))
                } else if let Some((params, body)) = self
                    .spec
                    .operator_bodies
                    .get(name.as_str())
                    .filter(|(params, _)| params.is_empty())
                {
                    // A 0-ary value operator (`None == -1`) is inlined: the name
                    // does not survive projection, and emitting it would collide
                    // with Rust's own `None`.
                    let _ = params;
                    let body = body.clone();
                    self.project_expr(&body)
                } else if self.state_field(name).is_some() {
                    Err(format!(
                        "bare reference to per-node variable `{name}`; it must be \
                         indexed at the acting node"
                    ))
                } else {
                    Ok(name.clone())
                }
            }
            // `m.field` -- a field of the received message, which is a parameter.
            TlaExpr::RecordAccess { record, field } => {
                if matches!(&**record, TlaExpr::Ident(n) if Some(n) == self.msg_param.as_ref()) {
                    // Routing does not survive into the payload: the framework
                    // delivers, so the sender is the dispatch's `src` and the
                    // destination is this node by construction.
                    return Ok(match field.as_str() {
                        "src" | "source" | "sender" | "msource" => "src".to_string(),
                        "dst" | "dest" | "receiver" | "mdest" => "c.node_id".to_string(),
                        other => to_snake_case(other),
                    });
                } else {
                    // A field of something else -- a log entry, say. The base
                    // has to project first; if it does not, the error names it.
                    Ok(format!(
                        "{}.{}",
                        self.project_expr(record)?,
                        to_snake_case(field)
                    ))
                }
            }
            TlaExpr::Number(n) => Ok(n.to_i64().map(|v| v.to_string()).unwrap_or_default()),
            TlaExpr::Bool(b) => Ok(b.to_string()),
            TlaExpr::String(s) => Ok(format!("\"{s}\"")),
            // A conjunction may carry dispatch guards in from an inlined
            // helper (`Deliverable(p, m)` expands to a `dst` check and a
            // sequence check); the `dst` half is the framework's, as it is at
            // the top level of an action.
            TlaExpr::BinOp {
                op: TlaBinOp::And,
                left,
                right,
            } if self.dispatch_guard(left).is_some() || self.dispatch_guard(right).is_some() => {
                if self.dispatch_guard(left).is_some() {
                    self.project_expr(right)
                } else {
                    self.project_expr(left)
                }
            }
            // A comparison of an enum-typed field against a literal is a
            // variant test, which Verus spells `x is Variant`.
            TlaExpr::BinOp {
                op: TlaBinOp::Eq,
                left,
                right,
            } if self
                .project_expr(left)
                .ok()
                .and_then(|l| l.strip_prefix("s.").map(str::to_string))
                .and_then(|f| self.enum_variant(&f, right))
                .is_some() =>
            {
                let l = self.project_expr(left)?;
                let field = l.trim_start_matches("s.").to_string();
                let variant = self.enum_variant(&field, right).unwrap();
                Ok(format!("{l} is {variant}"))
            }
            // `b \in a .. z` is a range test, not a set membership: the
            // projection has no value for the range itself.
            TlaExpr::BinOp {
                op: TlaBinOp::In,
                left,
                right,
            } if self.as_range(right).is_some() => {
                let range = self.as_range(right).expect("guarded above");
                let (low, high) = range;
                let x = self.parenthesised(left, precedence(&TlaBinOp::Leq))?;
                Ok(format!(
                    "{} <= {x} && {x} <= {}",
                    self.parenthesised(&low, precedence(&TlaBinOp::Leq))?,
                    self.parenthesised(&high, precedence(&TlaBinOp::Leq))?
                ))
            }
            // `state[i] \in {Follower, Candidate}` on an enum-typed field is a
            // choice between variant tests, not a set membership: the labels
            // do not survive projection as values.
            TlaExpr::BinOp {
                op: TlaBinOp::In,
                left,
                right,
            } if matches!(&**right, TlaExpr::SetEnum(_))
                && self.enum_variants_of(left, right).is_some() =>
            {
                let l = self.project_expr(left)?;
                let variants = self.enum_variants_of(left, right).unwrap();
                Ok(variants
                    .iter()
                    .map(|v| format!("{l} is {v}"))
                    .collect::<Vec<_>>()
                    .join(" || "))
            }
            TlaExpr::BinOp { op, left, right } => {
                // Parenthesise an operand that binds more loosely than this
                // operator. Without it `(i - 1) % N` renders as
                // `i - 1 % N`, which is a different expression.
                let l = self.parenthesised(left, precedence(op))?;
                let r = self.parenthesised(right, precedence(op))?;
                let rendered = match op {
                    TlaBinOp::Eq => format!("{l} == {r}"),
                    TlaBinOp::Neq => format!("{l} != {r}"),
                    TlaBinOp::Lt => format!("{l} < {r}"),
                    TlaBinOp::Gt => format!("{l} > {r}"),
                    TlaBinOp::Leq => format!("{l} <= {r}"),
                    TlaBinOp::Geq => format!("{l} >= {r}"),
                    TlaBinOp::Plus => format!("{l} + {r}"),
                    TlaBinOp::Minus => format!("{l} - {r}"),
                    TlaBinOp::Times => format!("{l} * {r}"),
                    TlaBinOp::Div => format!("{l} / {r}"),
                    TlaBinOp::Mod => format!("{l} % {r}"),
                    TlaBinOp::And => format!("{l} && {r}"),
                    TlaBinOp::Or => format!("{l} || {r}"),
                    TlaBinOp::Implies => format!("{l} ==> {r}"),
                    TlaBinOp::In => format!("{r}.contains({l})"),
                    TlaBinOp::NotIn => format!("!{r}.contains({l})"),
                    TlaBinOp::Cup => format!("{l}.union({r})"),
                    TlaBinOp::Cap => format!("{l}.intersect({r})"),
                    TlaBinOp::Setminus => format!("{l}.difference({r})"),
                    other => return Err(format!("operator {other:?}")),
                };
                Ok(rendered)
            }
            TlaExpr::UnaryOp {
                op: TlaUnaryOp::Not,
                operand,
            } => Ok(format!("!({})", self.project_expr(operand)?)),
            TlaExpr::UnaryOp {
                op: TlaUnaryOp::Neg,
                operand,
            } => Ok(format!("-{}", self.parenthesised(operand, 7)?)),
            TlaExpr::IfThenElse {
                cond,
                then_expr,
                else_expr,
            } => Ok(format!(
                "if {} {{ {} }} else {{ {} }}",
                self.project_expr(cond)?,
                self.project_expr(then_expr)?,
                self.project_expr(else_expr)?
            )),
            // A record value. The struct it belongs to is found by matching the
            // field names against the structs the projection introduced --
            // TLA+ records are structural, so the names are what identify one.
            TlaExpr::Record(fields) => {
                let names: Vec<String> = fields.iter().map(|(n, _)| to_snake_case(n)).collect();
                let Some((struct_name, _)) = self.spec.records.iter().find(|(_, fs)| {
                    fs.len() == names.len() && fs.iter().all(|(f, _)| names.contains(f))
                }) else {
                    return Err(format!(
                        "record value with fields {names:?} matches no declared record type"
                    ));
                };
                let rendered: Result<Vec<String>, String> = fields
                    .iter()
                    .map(|(n, v)| Ok(format!("{}: {}", to_snake_case(n), self.project_expr(v)?)))
                    .collect();
                Ok(format!("{struct_name} {{ {} }}", rendered?.join(", ")))
            }
            TlaExpr::SetEnum(items) if items.is_empty() => Ok("Set::empty()".to_string()),
            TlaExpr::Tuple(items) if items.is_empty() => Ok("Seq::empty()".to_string()),
            TlaExpr::SetEnum(items) => {
                let rendered: Result<Vec<String>, String> =
                    items.iter().map(|i| self.project_expr(i)).collect();
                Ok(format!("set![{}]", rendered?.join(", ")))
            }
            // `\A q \in Node \ {self} : P` -- a statement about every peer.
            TlaExpr::Forall { vars, body } | TlaExpr::Exists { vars, body } if vars.len() == 1 => {
                let bound = &vars[0];
                let Some(set) = &bound.set else {
                    return Err("unbounded quantifier".to_string());
                };
                let domain = self.project_quantifier_domain(&bound.var, set)?;
                let inner = self.project_expr(body)?;
                let keyword = if matches!(expr, TlaExpr::Forall { .. }) {
                    "forall"
                } else {
                    "exists"
                };
                let joiner = if keyword == "forall" { "==>" } else { "&&" };
                Ok(format!(
                    "{keyword}|{}: int| {domain} {joiner} {inner}",
                    bound.var
                ))
            }
            // TLA+ sequence operators. `Len` and `Append` map directly;
            // `SubSeq(s, a, b)` is 1-based and inclusive at both ends, while
            // Verus's `subrange` is 0-based and exclusive at the end, so the
            // start moves back one and the end stays put.
            TlaExpr::OpApply { op, args }
                if matches!(&**op, TlaExpr::Ident(n) if n == "Len") && args.len() == 1 =>
            {
                // `len()` is a `nat` and TLA+ has one number type, which the
                // projection spells `int`. Without the coercion an arithmetic
                // comparison against any other projected number is a type
                // error, and a message field holding a length does not typecheck.
                Ok(format!("({}.len() as int)", self.project_expr(&args[0])?))
            }
            TlaExpr::OpApply { op, args }
                if matches!(&**op, TlaExpr::Ident(n) if n == "Append") && args.len() == 2 =>
            {
                Ok(format!(
                    "{}.push({})",
                    self.project_expr(&args[0])?,
                    self.project_expr(&args[1])?
                ))
            }
            TlaExpr::OpApply { op, args }
                if matches!(&**op, TlaExpr::Ident(n) if n == "SubSeq") && args.len() == 3 =>
            {
                Ok(format!(
                    "{}.subrange({} - 1, {})",
                    self.project_expr(&args[0])?,
                    self.parenthesised(&args[1], 7)?,
                    self.project_expr(&args[2])?
                ))
            }
            // `Cardinality(S)` -- the counting half of P4. A quorum written as
            // a cardinality comparison is what a node can actually evaluate.
            TlaExpr::OpApply { op, args }
                if matches!(&**op, TlaExpr::Ident(n) if n == "Cardinality") && args.len() == 1 =>
            {
                Ok(format!("({}.len() as int)", self.project_expr(&args[0])?))
            }
            // A call to a user-defined operator: either a helper the projected
            // spec keeps, or one that must be inlined because it was handed the
            // received message.
            TlaExpr::OpApply { op, args } => {
                let TlaExpr::Ident(name) = &**op else {
                    return Err(format!("call {}", render_source(expr)));
                };
                let takes_message = self.msg_param.as_deref().is_some_and(|msg| {
                    args.iter()
                        .any(|a| matches!(a, TlaExpr::Ident(v) if v == msg))
                });
                if takes_message {
                    // The message is destructured into parameters after
                    // projection, so the helper's signature cannot survive.
                    let inlined = self.inline_call(expr)?;
                    return self.project_expr(&inlined);
                }
                let Some((params, body)) = self.spec.operator_bodies.get(name.as_str()) else {
                    return Err(format!("unknown operator `{name}`"));
                };
                let mut rendered = Vec::new();
                if reads_state(body, self.spec) {
                    rendered.push("s".to_string());
                }
                rendered.push("c".to_string());
                for arg in args.iter() {
                    // The acting node disappears from the argument list: the
                    // projected helper is already about this node. It is the
                    // *argument* that identifies it, not the parameter name --
                    // the helper may call its own parameter something else.
                    if self.is_node_index(arg) {
                        continue;
                    }
                    rendered.push(self.project_expr(arg)?);
                }
                let _ = params;
                Ok(format!("L{name}({})", rendered.join(", ")))
            }
            // `[x EXCEPT ![self] ...]` used as a value, which is how a helper
            // that returns an updated table is written.
            TlaExpr::FnExcept { func, .. } => {
                let TlaExpr::Ident(var) = &**func else {
                    return Err(format!("EXCEPT over {}", render_source(func)));
                };
                self.project_update(var, expr)
            }
            // `[d \in Node |-> e]` -- a table built over the peers.
            TlaExpr::FnConstruct { var, domain, body } => {
                let set = self.project_node_set(domain)?;
                let value = self.project_expr_with_binder(body, var)?;
                Ok(format!("Map::new({set}, |{var}: int| {value})"))
            }
            other => Err(format!("expression {}", render_source(other))),
        }
    }

    /// Project an operand, wrapping it when it binds more loosely than the
    /// operator it sits under.
    fn parenthesised(&self, expr: &TlaExpr, parent: u8) -> Result<String, String> {
        let text = self.project_expr(expr)?;
        if let TlaExpr::BinOp { op, .. } = expr {
            if precedence(op) < parent {
                return Ok(format!("({text})"));
            }
        }
        Ok(text)
    }

    /// `q \in Node \ {self}` -> `c.procs.contains(q) && q != c.node_id`.
    fn project_quantifier_domain(&self, var: &str, set: &TlaExpr) -> Result<String, String> {
        match set {
            TlaExpr::BinOp {
                op: TlaBinOp::Setminus,
                left,
                right,
            } => {
                let base = self.project_node_set(left)?;
                if let TlaExpr::SetEnum(items) = &**right {
                    if items.len() == 1 && self.is_node_index(&items[0]) {
                        return Ok(format!("{base}.contains({var}) && {var} != c.node_id"));
                    }
                }
                Err(format!("quantifier domain {}", render_source(set)))
            }
            other => Ok(format!("{}.contains({var})", self.project_node_set(other)?)),
        }
    }
}

/// Handlers invoked as `\E m \in <network> : Handler(node, m)` in `Next`,
/// mapped to the name the message goes by inside them.
fn receive_handlers(module: &TlaModule, network: Option<&str>) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    let (Some(network), Some(next)) = (network, module.operators.iter().find(|o| o.name == "Next"))
    else {
        return out;
    };
    collect_receive_handlers(&next.body, network, module, &mut out);
    out
}

fn collect_receive_handlers(
    expr: &TlaExpr,
    network: &str,
    module: &TlaModule,
    out: &mut BTreeMap<String, String>,
) {
    if let TlaExpr::Exists { vars, body } = expr {
        if let Some(bound) = vars
            .iter()
            .find(|b| matches!(&b.set, Some(TlaExpr::Ident(n)) if n == network))
        {
            collect_calls_with(body, &bound.var, module, out);
        }
    }
    for child in children(expr) {
        collect_receive_handlers(child, network, module, out);
    }
}

fn collect_calls_with(
    expr: &TlaExpr,
    msg_var: &str,
    module: &TlaModule,
    out: &mut BTreeMap<String, String>,
) {
    if let TlaExpr::OpApply { op, args } = expr {
        if let TlaExpr::Ident(name) = &**op {
            if let Some(index) = args
                .iter()
                .position(|a| matches!(a, TlaExpr::Ident(v) if v == msg_var))
            {
                if let Some(callee) = module.operators.iter().find(|o| o.name == *name) {
                    if let Some(param) = callee.params.get(index) {
                        out.insert(name.clone(), param.name.clone());
                    }
                }
            }
        }
    }
    for child in children(expr) {
        collect_calls_with(child, msg_var, module, out);
    }
}

fn flatten_conjunction(expr: &TlaExpr) -> Vec<&TlaExpr> {
    match expr {
        TlaExpr::BinOp {
            op: TlaBinOp::And,
            left,
            right,
        } => {
            let mut out = flatten_conjunction(left);
            out.extend(flatten_conjunction(right));
            out
        }
        other => vec![other],
    }
}

fn mentions_prime(expr: &TlaExpr) -> bool {
    if matches!(expr, TlaExpr::Prime(_)) {
        return true;
    }
    children(expr).into_iter().any(mentions_prime)
}

/// Binding power, used only to decide parenthesisation. Higher binds tighter.
fn precedence(op: &TlaBinOp) -> u8 {
    match op {
        TlaBinOp::Implies | TlaBinOp::Iff => 1,
        TlaBinOp::Or => 2,
        TlaBinOp::And => 3,
        TlaBinOp::Eq
        | TlaBinOp::Neq
        | TlaBinOp::Lt
        | TlaBinOp::Gt
        | TlaBinOp::Leq
        | TlaBinOp::Geq
        | TlaBinOp::In
        | TlaBinOp::NotIn
        | TlaBinOp::Subseteq => 4,
        TlaBinOp::Plus | TlaBinOp::Minus | TlaBinOp::Cup | TlaBinOp::Cap | TlaBinOp::Setminus => 5,
        TlaBinOp::Times | TlaBinOp::Div | TlaBinOp::Mod | TlaBinOp::Slash => 6,
        _ => 7,
    }
}

/// For `[x EXCEPT ![self] = v]`, the value `v`; otherwise the expression
/// itself. Used where the *assigned* value's type matters.
fn assigned_value(expr: &TlaExpr, is_node: impl Fn(&TlaExpr) -> bool) -> &TlaExpr {
    if let TlaExpr::FnExcept { updates, .. } = expr {
        if updates.len() == 1 {
            if let [TlaExceptPath::Index(index)] = updates[0].path.as_slice() {
                if is_node(index) {
                    return &updates[0].value;
                }
            }
        }
    }
    expr
}


/// `"req"` -> `Req`.
fn variant_name(tag: &str) -> String {
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

/// Replace every free occurrence of `param` with `value`.
fn substitute(expr: &TlaExpr, param: &str, value: &TlaExpr) -> TlaExpr {
    match expr {
        TlaExpr::Ident(name) if name == param => value.clone(),
        TlaExpr::BinOp { op, left, right } => TlaExpr::BinOp {
            op: *op,
            left: Box::new(substitute(left, param, value)),
            right: Box::new(substitute(right, param, value)),
        },
        TlaExpr::UnaryOp { op, operand } => TlaExpr::UnaryOp {
            op: *op,
            operand: Box::new(substitute(operand, param, value)),
        },
        TlaExpr::OpApply { op, args } => TlaExpr::OpApply {
            op: Box::new(substitute(op, param, value)),
            args: args.iter().map(|a| substitute(a, param, value)).collect(),
        },
        TlaExpr::FnApply { func, arg } => TlaExpr::FnApply {
            func: Box::new(substitute(func, param, value)),
            arg: Box::new(substitute(arg, param, value)),
        },
        TlaExpr::Record(fields) => TlaExpr::Record(
            fields
                .iter()
                .map(|(n, v)| (n.clone(), substitute(v, param, value)))
                .collect(),
        ),
        TlaExpr::SetEnum(items) => {
            TlaExpr::SetEnum(items.iter().map(|i| substitute(i, param, value)).collect())
        }
        TlaExpr::SetMap { expr, var, set } if var != param => TlaExpr::SetMap {
            expr: Box::new(substitute(expr, param, value)),
            var: var.clone(),
            set: Box::new(substitute(set, param, value)),
        },
        TlaExpr::RecordAccess { record, field } => TlaExpr::RecordAccess {
            record: Box::new(substitute(record, param, value)),
            field: field.clone(),
        },
        TlaExpr::IfThenElse {
            cond,
            then_expr,
            else_expr,
        } => TlaExpr::IfThenElse {
            cond: Box::new(substitute(cond, param, value)),
            then_expr: Box::new(substitute(then_expr, param, value)),
            else_expr: Box::new(substitute(else_expr, param, value)),
        },
        other => other.clone(),
    }
}

fn render_source(expr: &TlaExpr) -> String {
    use crate::verus2tla::TlaPrinter;
    TlaPrinter::new()
        .print_expr(expr, 0)
        .trim()
        .replace('\n', " ")
}

/// Direct sub-expressions. Kept local to this module so the walk can stay
/// simple; the linter has its own for the same reason.
pub(crate) fn children(expr: &TlaExpr) -> Vec<&TlaExpr> {
    match expr {
        TlaExpr::Prime(inner)
        | TlaExpr::UnaryOp { operand: inner, .. }
        | TlaExpr::Enabled(inner)
        | TlaExpr::Always(inner)
        | TlaExpr::Eventually(inner) => vec![inner],
        TlaExpr::BinOp { left, right, .. } | TlaExpr::LeadsTo { left, right } => vec![left, right],
        TlaExpr::OpApply { op, args } => {
            let mut out = vec![&**op];
            out.extend(args.iter());
            out
        }
        TlaExpr::FnApply { func, arg } => vec![func, arg],
        TlaExpr::SetEnum(items) | TlaExpr::Tuple(items) | TlaExpr::Unchanged(items) => {
            items.iter().collect()
        }
        TlaExpr::SetFilter { set, filter, .. } => vec![set, filter],
        TlaExpr::SetMap { expr, set, .. } => vec![expr, set],
        TlaExpr::FnConstruct { domain, body, .. } => vec![domain, body],
        TlaExpr::FnExcept { func, updates } => {
            let mut out = vec![&**func];
            for update in updates {
                for step in &update.path {
                    if let TlaExceptPath::Index(index) = step {
                        out.push(index);
                    }
                }
                out.push(&update.value);
            }
            out
        }
        TlaExpr::FnSet { domain, range } => vec![domain, range],
        TlaExpr::Record(fields) | TlaExpr::RecordSet(fields) => {
            fields.iter().map(|(_, v)| v).collect()
        }
        TlaExpr::RecordAccess { record, .. } => vec![record],
        TlaExpr::Forall { vars, body } | TlaExpr::Exists { vars, body } => {
            let mut out: Vec<&TlaExpr> = vars.iter().filter_map(|v| v.set.as_ref()).collect();
            out.push(body);
            out
        }
        TlaExpr::Choose { set, body, .. } => {
            let mut out = Vec::new();
            if let Some(set) = set {
                out.push(&**set);
            }
            out.push(body);
            out
        }
        TlaExpr::IfThenElse {
            cond,
            then_expr,
            else_expr,
        } => vec![cond, then_expr, else_expr],
        TlaExpr::Case { arms, other } => {
            let mut out = Vec::new();
            for (cond, result) in arms {
                out.push(cond);
                out.push(result);
            }
            if let Some(other) = other {
                out.push(other);
            }
            out
        }
        TlaExpr::LetIn { defs, body } => {
            let mut out: Vec<&TlaExpr> = defs.iter().map(|d| &d.body).collect();
            out.push(body);
            out
        }
        TlaExpr::WeakFairness { vars, action } | TlaExpr::StrongFairness { vars, action } => {
            vec![vars, action]
        }
        _ => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::project_helpers;
    use super::*;
    use crate::tla::parse_module;
    use crate::tla::projection::project_module;

    fn actions(source: &str) -> Vec<ProjectedAction> {
        let module = parse_module(source).expect("test spec must parse");
        let spec = project_module(&module).expect("test spec must be clean");
        project_actions(&module, &spec)
    }

    fn action<'a>(actions: &'a [ProjectedAction], name: &str) -> &'a ProjectedAction {
        actions
            .iter()
            .find(|a| a.source_name == name)
            .unwrap_or_else(|| panic!("no action `{name}`"))
    }

    const SIMPLE: &str = r#"---- MODULE Test ----
VARIABLES x, y, pc, network
Message == [type: {"read", "val"}, src: Proc, dst: Proc, val: Nat]
TypeOK == /\ x \in [Proc -> Nat]
          /\ y \in [Proc -> Nat]
          /\ pc \in [Proc -> {"a", "b"}]
a(self) == /\ pc[self] = "a"
           /\ x' = [x EXCEPT ![self] = 1]
           /\ pc' = [pc EXCEPT ![self] = "b"]
Recv(self, m) == /\ m.type = "val"
                 /\ y' = [y EXCEPT ![self] = m.val]
                 /\ network' = network \ {m}
Next == \E self \in Proc :
            \/ a(self)
            \/ \E m \in network : Recv(self, m)
===="#;

    #[test]
    fn projects_reads_and_updates_of_the_acting_node() {
        let acts = actions(SIMPLE);
        let a = action(&acts, "a");
        assert_eq!(a.kind, ActionKind::Local);
        assert!(
            a.conjuncts.contains(&"s.pc is A".to_string()),
            "a guard comparing an enum-typed field to a literal is a variant \
             test, which Verus spells `is`: {:?}",
            a.conjuncts
        );
        assert!(
            a.conjuncts.contains(&"s_.x == 1".to_string()),
            "update should assign this node's x: {:?}",
            a.conjuncts
        );
        assert!(a.gaps.is_empty(), "unexpected gaps: {:?}", a.gaps);
    }

    #[test]
    fn generates_frame_conditions_for_untouched_fields() {
        let acts = actions(SIMPLE);
        let a = action(&acts, "a");
        assert!(
            a.frame.contains(&"s_.y == s.y".to_string()),
            "P5 must state what the action leaves alone: {:?}",
            a.frame
        );
        assert!(
            !a.frame.iter().any(|f| f.starts_with("s_.x ")),
            "a field the action updates must not also be framed: {:?}",
            a.frame
        );
    }

    #[test]
    fn an_action_that_sends_nothing_says_so() {
        // Without this conjunct `sent_packets` is unconstrained and the action
        // would permit the node to emit anything.
        let acts = actions(SIMPLE);
        assert!(
            action(&acts, "a")
                .frame
                .contains(&"sent_packets == Set::<LPacket>::empty()".to_string()),
            "got {:?}",
            action(&acts, "a").frame
        );
    }

    #[test]
    fn a_receive_takes_the_message_fields_as_parameters() {
        let acts = actions(SIMPLE);
        let recv = action(&acts, "Recv");
        assert_eq!(recv.kind, ActionKind::Receive);
        assert!(
            recv.conjuncts.contains(&"s_.y == val".to_string()),
            "the message field becomes a parameter, not a field access: {:?}",
            recv.conjuncts
        );
    }

    #[test]
    fn consuming_a_message_is_not_a_send() {
        // `network' = network \ {m}` removes the message being handled. After
        // projection the framework owns delivery, so the node states nothing.
        let acts = actions(SIMPLE);
        let recv = action(&acts, "Recv");
        assert!(
            recv.conjuncts
                .contains(&"sent_packets == Set::<LPacket>::empty()".to_string()),
            "consumption should project to an empty send, got {:?}",
            recv.conjuncts
        );
    }

    #[test]
    fn helper_predicates_are_not_actions() {
        let source = r#"---- MODULE Test ----
VARIABLES x
TypeOK == x \in [Proc -> Nat]
beats(self, q) == x[self] < 5
Step(self) == /\ beats(self, 1)
              /\ x' = [x EXCEPT ![self] = 1]
Next == \E self \in Proc : Step(self)
===="#;
        let acts = actions(source);
        assert!(
            acts.iter().all(|a| a.source_name != "beats"),
            "a predicate with no primed state is not an action: {:?}",
            acts.iter().map(|a| &a.source_name).collect::<Vec<_>>()
        );
    }

    #[test]
    fn reports_an_unprojectable_conjunct_instead_of_dropping_it() {
        let source = r#"---- MODULE Test ----
VARIABLES x
TypeOK == x \in [Proc -> Nat]
Step(self) == /\ x' = [x EXCEPT ![self] = CHOOSE v \in Nat : v > 0]
Next == \E self \in Proc : Step(self)
===="#;
        let acts = actions(source);
        let step = action(&acts, "Step");
        assert!(
            !step.gaps.is_empty(),
            "an unprojectable conjunct must be reported, not silently dropped"
        );
    }

    #[test]
    fn inlines_a_message_constructor_into_a_packet() {
        let source = r#"---- MODULE Test ----
VARIABLES x, network
Message == [type: {"ping"}, src: Proc, dst: Proc, val: Nat]
Ping(s, d, v) == [type |-> "ping", src |-> s, dst |-> d, val |-> v]
TypeOK == x \in [Proc -> Nat]
Send(self) == /\ network' = network \cup {Ping(self, 1, x[self])}
              /\ x' = [x EXCEPT ![self] = 0]
Recv(self, m) == /\ m.type = "ping"
                 /\ x' = [x EXCEPT ![self] = m.val]
                 /\ network' = network \ {m}
Next == \E self \in Proc : Send(self) \/ \E m \in network : Recv(self, m)
===="#;
        let acts = actions(source);
        let send = action(&acts, "Send");
        assert!(
            send.conjuncts.iter().any(|c| c
                == "sent_packets == set![LPacket { dst: 1, msg: LMessage::Ping { val: s.x } }]"),
            "the constructor should be inlined into a packet, got {:?}",
            send.conjuncts
        );
    }

    #[test]
    fn a_receives_tag_moves_to_the_dispatch() {
        // `m.type = "ping"` selects the variant in the generated match; the
        // action does not restate it.
        let source = r#"---- MODULE Test ----
VARIABLES x, network
Message == [type: {"ping"}, src: Proc, dst: Proc, val: Nat]
TypeOK == x \in [Proc -> Nat]
Recv(self, m) == /\ m.dst = self
                 /\ m.type = "ping"
                 /\ x' = [x EXCEPT ![self] = m.val]
                 /\ network' = network \ {m}
Next == \E self \in Proc : \E m \in network : Recv(self, m)
===="#;
        let acts = actions(source);
        let recv = action(&acts, "Recv");
        assert_eq!(recv.handles_tag.as_deref(), Some("ping"));
        assert!(
            !recv.conjuncts.iter().any(|c| c.contains("dst")),
            "the delivery guard is the framework's, not the action's: {:?}",
            recv.conjuncts
        );
    }

    #[test]
    fn keeps_a_state_helper_as_its_own_function() {
        // Preserving the source's factoring is what lets a human match output
        // against input concept by concept.
        let source = r#"---- MODULE Test ----
VARIABLES req
TypeOK == req \in [Proc -> [Proc -> Nat]]
beats(p, q) == req[p][q] = 0
Step(p) == /\ beats(p, 1)
           /\ req' = [req EXCEPT ![p][p] = 1]
Next == \E p \in Proc : Step(p)
===="#;
        let module = parse_module(source).unwrap();
        let spec = project_module(&module).unwrap();
        let acts = project_actions(&module, &spec);
        assert!(
            action(&acts, "Step")
                .conjuncts
                .iter()
                .any(|c| c == "Lbeats(s, c, 1)"),
            "the helper should be called, not inlined: {:?}",
            action(&acts, "Step").conjuncts
        );
        let helpers = project_helpers(&module, &spec);
        let beats = helpers
            .iter()
            .find(|h| h.source_name == "beats")
            .expect("beats should be emitted");
        assert!(beats.reads_state);
        assert_eq!(beats.params, vec!["q: int".to_string()]);
        assert_eq!(beats.body, "s.req[q] == 0");
    }

    #[test]
    fn inlines_a_helper_that_takes_the_message() {
        // The message is destructured into parameters, so a helper's signature
        // over it cannot survive projection.
        let source = r#"---- MODULE Test ----
VARIABLES seen, network
Message == [type: {"ping"}, src: Proc, dst: Proc, n: Nat]
TypeOK == seen \in [Proc -> [Proc -> Nat]]
Deliverable(p, m) == m.n = seen[p][m.src]
Recv(p, m) == /\ Deliverable(p, m)
              /\ m.type = "ping"
              /\ seen' = [seen EXCEPT ![p][m.src] = m.n]
              /\ network' = network \ {m}
Next == \E p \in Proc : \E m \in network : Recv(p, m)
===="#;
        let module = parse_module(source).unwrap();
        let spec = project_module(&module).unwrap();
        let acts = project_actions(&module, &spec);
        let recv = action(&acts, "Recv");
        assert!(
            recv.conjuncts.iter().any(|c| c == "n == s.seen[src]"),
            "the helper should be inlined and projected: {:?}",
            recv.conjuncts
        );
        assert!(
            project_helpers(&module, &spec)
                .iter()
                .all(|h| h.source_name != "Deliverable"),
            "an inlined helper must not also be emitted as a function"
        );
    }

    #[test]
    fn projects_a_quantifier_over_the_peers() {
        let source = r#"---- MODULE Test ----
VARIABLES ok
TypeOK == ok \in [Proc -> BOOLEAN]
Step(p) == /\ \A q \in Proc \ {p} : ok[p]
           /\ ok' = [ok EXCEPT ![p] = FALSE]
Next == \E p \in Proc : Step(p)
===="#;
        let module = parse_module(source).unwrap();
        let spec = project_module(&module).unwrap();
        let acts = project_actions(&module, &spec);
        assert!(
            action(&acts, "Step")
                .conjuncts
                .iter()
                .any(|c| c.contains("forall|q: int|") && c.contains("q != c.node_id")),
            "got {:?}",
            action(&acts, "Step").conjuncts
        );
    }

    #[test]
    fn resolves_the_except_at_marker() {
        // `@` is the component's old value, and what that is depends on the
        // EXCEPT path.
        let source = r#"---- MODULE Test ----
VARIABLES ack
TypeOK == ack \in [Proc -> SUBSET Proc]
Step(p) == ack' = [ack EXCEPT ![p] = @ \union {p}]
Next == \E p \in Proc : Step(p)
===="#;
        let module = parse_module(source).unwrap();
        let spec = project_module(&module).unwrap();
        let acts = project_actions(&module, &spec);
        assert!(
            action(&acts, "Step")
                .conjuncts
                .iter()
                .any(|c| c == "s_.ack == s.ack.union(set![c.node_id])"),
            "got {:?}",
            action(&acts, "Step").conjuncts
        );
    }

    #[test]
    fn a_sequence_index_loses_one_but_a_map_key_does_not() {
        // TLA+ sequences are 1-indexed and Verus's Seq is 0-indexed, so an
        // index into a sequence must lose one. A map key must not: it is a
        // peer id, not a position. Getting this wrong is an off-by-one that
        // still verifies.
        let source = r#"---- MODULE Test ----
VARIABLES log, nextIndex
TypeOK == /\ log \in [Proc -> Seq(Nat)]
          /\ nextIndex \in [Proc -> [Proc -> Nat]]
Step(p, k) == /\ log[p][k] = 0
              /\ nextIndex[p][k] = 0
              /\ log' = log
Next == \E p \in Proc : \E k \in Proc : Step(p, k)
===="#;
        let module = parse_module(source).unwrap();
        let spec = project_module(&module).unwrap();
        let acts = project_actions(&module, &spec);
        let step = action(&acts, "Step");
        assert!(
            step.conjuncts.iter().any(|c| c == "s.log[k - 1] == 0"),
            "a sequence index must lose one: {:?}",
            step.conjuncts
        );
        assert!(
            step.conjuncts.iter().any(|c| c == "s.next_index[k] == 0"),
            "a map key must not be adjusted: {:?}",
            step.conjuncts
        );
    }

    #[test]
    fn projects_the_sequence_operators() {
        let source = r#"---- MODULE Test ----
VARIABLES log
TypeOK == log \in [Proc -> Seq(Nat)]
Step(p) == /\ Len(log[p]) < 5
           /\ log' = [log EXCEPT ![p] = Append(log[p], 1)]
Next == \E p \in Proc : Step(p)
===="#;
        let module = parse_module(source).unwrap();
        let spec = project_module(&module).unwrap();
        let acts = project_actions(&module, &spec);
        let step = action(&acts, "Step");
        assert!(
            step.conjuncts
                .iter()
                .any(|c| c == "(s.log.len() as int) < 5"),
            "{:?}",
            step.conjuncts
        );
        assert!(
            step.conjuncts
                .iter()
                .any(|c| c == "s_.log == s.log.push(1)"),
            "{:?}",
            step.conjuncts
        );
    }

    #[test]
    fn resolves_a_named_message_tag() {
        // Specs usually name their tags rather than writing the literal.
        let source = r#"---- MODULE Test ----
VARIABLES x, network
Ping == "ping"
Message == [mtype: {Ping}, msource: Proc, mdest: Proc, val: Nat]
Mk(i, j, v) == [mtype |-> Ping, msource |-> i, mdest |-> j, val |-> v]
TypeOK == x \in [Proc -> Nat]
Send(p) == /\ network' = network \cup {Mk(p, 1, x[p])}
           /\ x' = x
Recv(p, m) == /\ m.mdest = p
              /\ m.mtype = Ping
              /\ x' = [x EXCEPT ![p] = m.val]
              /\ network' = network
Next == \E p \in Proc : Send(p) \/ \E m \in network : Recv(p, m)
===="#;
        let module = parse_module(source).unwrap();
        let spec = project_module(&module).unwrap();
        assert_eq!(
            spec.messages
                .iter()
                .map(|m| m.name.clone())
                .collect::<Vec<_>>(),
            vec!["Ping".to_string()]
        );
        let acts = project_actions(&module, &spec);
        assert!(
            action(&acts, "Send")
                .conjuncts
                .iter()
                .any(|c| c.contains("LMessage::Ping")),
            "{:?}",
            action(&acts, "Send").conjuncts
        );
    }
}
