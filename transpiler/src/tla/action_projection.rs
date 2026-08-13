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

use crate::tla::ast::{
    TlaBinOp, TlaExceptPath, TlaExceptUpdate, TlaExpr, TlaModule, TlaQuantBound, TlaUnaryOp,
};
use crate::tla::clean_subset::node_parameterized_operators;
use crate::tla::projection::{
    to_pascal_case, to_snake_case, MessageVariant, ProjectedSpec, ProjectedType, ProjectionError,
    ROUTING_FIELDS, TAG_FIELDS,
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
    // `Init` is projected *before* pruning and counts towards it. Projecting
    // it afterwards let the node-set constant be pruned as unused -- the
    // actions did not mention it -- and then `Init`, which builds a table over
    // every peer, found no set constant and emitted a name for one that no
    // longer existed.
    let (init, init_gaps) = project_init(module, &spec);
    let init_texts: Vec<&String> = init.iter().collect();
    spec.constants.retain(|(name, _)| {
        name == "node_id"
            || texts.iter().any(|t| references_constant(t, name))
            || init_texts.iter().any(|t| references_constant(t, name))
    });

    // Declare the enums the binder domains introduced. `project_actions` names
    // them by the same formula it rendered them with, so the two agree without
    // threading state between the passes.
    for ((op_name, param), set) in action_param_bounds(module) {
        if let Some(variants) = literal_domain(&spec, &set) {
            let name = binder_enum_name(&spec, &op_name, &param, &variants);
            if !spec.enums.iter().any(|(n, _)| *n == name) {
                spec.enums.push((name, variants));
            }
        }
    }

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
                            .unwrap_or_else(|| match helper_param_type(op, &p.name) {
                                "Set<int>" => ProjectedType::Set(Box::new(ProjectedType::Int)),
                                "Seq<int>" => ProjectedType::Seq(Box::new(ProjectedType::Int)),
                                _ => ProjectedType::Int,
                            }),
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
            // The node parameter is deliberately left alone: it does not appear
            // in the signature -- it projects to `c.node_id` -- and renaming it
            // would only break `is_node_index`, which matches against the name
            // the source used. `AdvanceOne(s, d)`'s node parameter is `s`.
            if param.name == *node_param {
                continue;
            }
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
            name: format!("L{}", rust_ident(op_name)),
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
                if text.contains(&format!("L{}(", rust_ident(&op.name))) {
                    called.insert(op.name.clone());
                }
            }
        }
    }
    // Transitively: a helper may call another helper. EPaxos's `NextSeq` calls
    // `Max`, and emitting only the directly-called set produced a spec that
    // referenced `LMax` without defining it.
    loop {
        let mut added = false;
        for name in called.clone() {
            let Some(op) = module.operators.iter().find(|o| o.name == name) else {
                continue;
            };
            let mut names = Vec::new();
            collect_operator_calls(&op.body, &mut names);
            for callee in names {
                if module.operators.iter().any(|o| o.name == callee) && called.insert(callee) {
                    added = true;
                }
            }
        }
        if !added {
            break;
        }
    }
    called
}

/// Operator names applied in an expression.
fn collect_operator_calls(expr: &TlaExpr, out: &mut Vec<String>) {
    if let TlaExpr::OpApply { op, .. } = expr {
        if let TlaExpr::Ident(name) = &**op {
            out.push(name.clone());
        }
    }
    for child in children(expr) {
        collect_operator_calls(child, out);
    }
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
            // `m.mcmd` -- a field of the message being handled. As informative
            // as a state field and it was not being read: Jetpack's
            // `HasConflict(cmdPool[i], m.mcmd)` typed its second parameter
            // `int`, and the emitted helper then read `cmd.key` off an integer.
            // Payload field names are unique because the projection merges
            // every variant's record set into one list.
            TlaExpr::RecordAccess { field, .. } => {
                let field = to_snake_case(field);
                return spec
                    .messages
                    .iter()
                    .flat_map(|m| m.fields.iter())
                    .find(|(f, _)| *f == field)
                    .map(|(_, ty)| ty.clone());
            }
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
                    // A record constructor's parameters are typed by the fields
                    // they fill: `Rec(i, st, c, d, s)`'s `i` is whatever
                    // `LRecord.inst` is. The call sites cannot say, because the
                    // arguments are usually themselves parameters.
                    if let TlaExpr::Record(fields) = &target.body {
                        for (field, value) in fields {
                            let TlaExpr::Ident(param) = value else {
                                continue;
                            };
                            if !target.params.iter().any(|p| p.name == *param) {
                                continue;
                            }
                            let field = to_snake_case(field);
                            let found = spec.records.iter().find_map(|(_, fs)| {
                                fs.iter().find(|(f, _)| *f == field).map(|(_, t)| t.clone())
                            });
                            if let Some(ty) = found {
                                out.insert((target.name.clone(), param.clone()), ty);
                            }
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
    fn quantified(expr: &TlaExpr, param: &str) -> bool {
        let here = match expr {
            TlaExpr::Forall { vars, .. } | TlaExpr::Exists { vars, .. } => vars
                .iter()
                .any(|b| matches!(&b.set, Some(TlaExpr::Ident(n)) if n == param)),
            TlaExpr::Choose { set, .. } => {
                matches!(set, Some(s) if matches!(&**s, TlaExpr::Ident(n) if n == param))
            }
            _ => false,
        };
        here || children(expr).into_iter().any(|c| quantified(c, param))
    }
    if counted(&op.body, param) || quantified(&op.body, param) {
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
        seen: &mut std::collections::BTreeSet<String>,
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
                walk(body, &inner, module, out, seen);
                return;
            }
            TlaExpr::OpApply { op, args } => {
                if let TlaExpr::Ident(callee) = &**op {
                    if let Some(target) = module.operators.iter().find(|o| o.name == *callee) {
                        let mut inner = BTreeMap::new();
                        for (param, arg) in target.params.iter().zip(args.iter()) {
                            if let TlaExpr::Ident(binder) = arg {
                                if let Some(set) = scope.get(binder) {
                                    out.insert((callee.clone(), param.name.clone()), set.clone());
                                    inner.insert(param.name.clone(), set.clone());
                                }
                            }
                        }
                        // A composed spec groups its disjuncts behind an
                        // intermediate operator -- `Next` binds the node and
                        // calls `BaseAction(i)`, whose body holds the binders
                        // for the actions' *other* parameters. Stopping at the
                        // call left `\E op \in {ReconfigAdd, ReconfigRemove}`
                        // unseen, so `op` was typed `int` and the emitted spec
                        // compared it against a string.
                        if seen.insert(callee.clone()) {
                            walk(&target.body, &inner, module, out, seen);
                            seen.remove(callee);
                        }
                    }
                }
            }
            _ => {}
        }
        for child in children(expr) {
            walk(child, scope, module, out, seen);
        }
    }

    let mut out = BTreeMap::new();
    if let Some(next) = module.operators.iter().find(|o| o.name == "Next") {
        walk(
            &next.body,
            &BTreeMap::new(),
            module,
            &mut out,
            &mut std::collections::BTreeSet::new(),
        );
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
/// Whether `body` applies a function to exactly `var` -- `log[i][k]`.
///
/// The test for whether re-indexing a range binder buys anything: it does only
/// when the binder is used as an index, which is where the projection's `- 1`
/// would otherwise appear.
fn indexes_with(body: &TlaExpr, var: &str) -> bool {
    if let TlaExpr::FnApply { arg, .. } = body {
        if matches!(arg.as_ref(), TlaExpr::Ident(n) if n == var) {
            return true;
        }
    }
    children(body).into_iter().any(|c| indexes_with(c, var))
}

/// A source name as a Rust identifier: the INSTANCE qualifier removed and
/// nothing else touched.
///
/// `B!IsQuorumOf` is `IsQuorumOf` of the module instantiated as `B`, and `!` is
/// not a legal identifier character -- the tier4 composition emitted
/// `LB!IsQuorumOf`, which does not parse. Case is deliberately left alone: the
/// projected name is `L` plus the source's own spelling, so `beats` stays
/// `Lbeats` and a reader can match output against input by name.
fn rust_ident(name: &str) -> String {
    name.replace('!', "")
}

/// The name of the enum a binder over a set of string literals introduces.
///
/// `\E op \in {ReconfigAdd, ReconfigRemove} : RequestReconfig(i, op, t)` gives
/// `op` a type the source never named. Computed from the action and the
/// parameter so that the declaration and the use agree without threading state
/// between the two passes that need it.
fn binder_enum_name(
    spec: &ProjectedSpec,
    action: &str,
    param: &str,
    variants: &[String],
) -> String {
    // An enum with these variants already declared is the same type, and
    // minting a second name for it splits one type in two: `RequestReconfig`'s
    // `op` ranges over exactly the variants of `pendingReconfig`'s `op` field,
    // and a fresh `LBRequestReconfigOp` then would not typecheck against the
    // record it is assigned into.
    // A *subset* match, not equality: `RequestReconfig` binds `op` over two of
    // `pendingReconfig`'s three variants, and the parameter it feeds is that
    // record's field. The binder's own restriction survives as the action's
    // parameter bound, which is where a restriction belongs -- minting a second
    // enum for it would split one type in two and not typecheck.
    let covers = |vs: &Vec<String>| variants.iter().all(|v| vs.contains(v));
    if let Some((name, _)) = spec.enums.iter().find(|(_, vs)| covers(vs)) {
        return name.clone();
    }
    for (_, fields) in &spec.records {
        for (_, ty) in fields {
            if let ProjectedType::Enum { name, variants: vs } = ty {
                if !name.is_empty() && covers(vs) {
                    return name.clone();
                }
            }
        }
    }
    format!(
        "L{}{}",
        to_pascal_case(action),
        to_pascal_case(&to_snake_case(param))
    )
}

/// A binder's domain written as a record set -- `[cmd_id: CmdId, key: Key]` --
/// matched against the structs the projection declared.
///
/// Records are structural in TLA+, so the field names are what identify one;
/// this is the same match `project_expr`'s `Record` arm makes for a value.
fn record_set_type(spec: &ProjectedSpec, set: &TlaExpr) -> Option<ProjectedType> {
    let TlaExpr::RecordSet(fields) = set else {
        return None;
    };
    let names: Vec<String> = fields.iter().map(|(n, _)| to_snake_case(n)).collect();
    spec.records
        .iter()
        .find(|(_, fs)| fs.len() == names.len() && fs.iter().all(|(f, _)| names.contains(f)))
        .map(|(name, fields)| ProjectedType::Record {
            name: name.clone(),
            fields: fields.clone(),
        })
}

/// A binder's domain as a set of string literals, if that is what it is.
fn literal_domain(spec: &ProjectedSpec, set: &TlaExpr) -> Option<Vec<String>> {
    let items = match set {
        TlaExpr::SetEnum(items) => items,
        _ => return None,
    };
    if items.is_empty() {
        return None;
    }
    items
        .iter()
        .map(|item| match item {
            TlaExpr::String(literal) => Some(variant_name(literal)),
            TlaExpr::Ident(name) => match spec.operator_bodies.get(name.as_str()) {
                Some((params, TlaExpr::String(literal))) if params.is_empty() => {
                    Some(variant_name(literal))
                }
                _ => None,
            },
            _ => None,
        })
        .collect()
}

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
        // An action's own parameters are typed by the set their `Next` binder
        // ranges over, and the body has to be projected knowing that: without
        // it `type_of` returns nothing for `op`, `enum_test` declines, and the
        // guard `op = ReconfigAdd` emits `op == "add"` against an enum.
        let mut param_types: BTreeMap<String, ProjectedType> = BTreeMap::new();
        for p in op.params.iter().filter(|p| p.name != *node_param) {
            let Some(set) = bounds.get(&(op_name.clone(), p.name.clone())) else {
                continue;
            };
            let probe = ActionContext {
                spec,
                param_types: Default::default(),
                msg_tag: None,
                node_param: node_param.clone(),
                msg_param: msg_param.clone(),
                network: spec.network_variable.clone(),
            };
            let ty = if let Some(variants) = literal_domain(spec, set) {
                Some(ProjectedType::Enum {
                    name: binder_enum_name(spec, &op_name, &p.name, &variants),
                    variants,
                })
            } else if let Some(record) = record_set_type(spec, set) {
                // `\E cmd \in [cmd_id: CmdId, key: Key]` -- a binder over a
                // record set, which is a declared struct rather than an `int`.
                Some(record)
            } else {
                match probe.type_of(set) {
                    Some(ProjectedType::Set(elem)) if !elem.is_unresolved() => Some(*elem),
                    _ => None,
                }
            };
            if let Some(ty) = ty {
                param_types.insert(safe_param_name(&p.name), ty);
            }
        }
        let mut ctx = ActionContext {
            spec,
            param_types: param_types.clone(),
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

        // An action's parameters go into its signature through
        // `safe_param_name`, so its body has to agree -- EPaxos's
        // `Propose(i, c)` has a parameter literally called `c`, which is the
        // constants record in the projected spec.
        let mut body = op.body.clone();
        for param in &op.params {
            if param.name == *node_param {
                continue;
            }
            let safe = safe_param_name(&param.name);
            if safe != param.name {
                body = substitute(&body, &param.name, &TlaExpr::Ident(safe));
            }
        }
        let op = &crate::tla::ast::TlaOperator {
            name: op.name.clone(),
            params: op.params.clone(),
            body,
            ..op.clone()
        };

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
            if let Some(tags) = &handles_tag {
                // A handler that claims several tags can only take the fields
                // every one of those variants carries: each dispatch arm binds
                // its own variant's fields, so a field one of them lacks has
                // nothing to pass. Raft's `UpdateTerm` reads `mterm`, which all
                // four of its message types have.
                let claimed: Vec<&MessageVariant> = tags
                    .split(',')
                    .filter_map(|tag| spec.messages.iter().find(|m| m.tag == tag))
                    .collect();
                if let Some((first, rest)) = claimed.split_first() {
                    let common = first.fields.iter().filter(|(name, ty)| {
                        rest.iter()
                            .all(|v| v.fields.iter().any(|(n, t)| n == name && t == ty))
                    });
                    params.extend(common.map(|(name, ty)| format!("{name}: {}", ty.render())));
                }
            }
            params
        } else {
            // A local action's own parameters survive, minus the node: the
            // source's `Phase1a(a, b)` is this node starting ballot `b`.
            // A parameter's type comes from the set its `Next` binder ranges
            // over, not from an assumption that everything is a node id.
            // `RequestReconfig(i, op, target)` binds `op` over two string
            // literals and `ClientSendPreaccept(c, cmd)` binds `cmd` over a
            // record set; typing both `int` emitted `op == "add"` and
            // `s_.client_pending == cmd` against an `int`, which Verus rejects.
            op.params
                .iter()
                .filter(|p| p.name != node_param)
                .map(|p| {
                    let safe = safe_param_name(&p.name);
                    let ty = param_types
                        .get(&safe)
                        .map(|t| t.render())
                        .unwrap_or_else(|| "int".to_string());
                    format!("{safe}: {ty}")
                })
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
                    // The bound names the parameter as the *signature* spells
                    // it, which is the renamed form.
                    ctx.project_expr(&TlaExpr::BinOp {
                        op: TlaBinOp::In,
                        left: Box::new(TlaExpr::Ident(safe_param_name(&p.name))),
                        right: Box::new(set.clone()),
                    })
                    .ok()
                })
                .collect()
        };

        actions.push(ProjectedAction {
            name: format!("L{}", rust_ident(&op_name)),
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

impl<'a> ActionContext<'a> {
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

    /// The variant a literal names in a position whose type is an enum,
    /// qualified by the enum's own name.
    ///
    /// [`enum_variant`] answers the same question for a *state field*, where
    /// the caller already knows it is writing `s.f is Variant`. A record
    /// literal has no state field to look up -- the type comes from the record
    /// declaration -- and it needs the qualified `LEnum::Variant`, because the
    /// value sits in a struct-literal field rather than in an `is` test.
    fn enum_literal(&self, ty: &ProjectedType, expr: &TlaExpr) -> Option<String> {
        let ProjectedType::Enum { name, variants } = ty else {
            return None;
        };
        let literal = match expr {
            TlaExpr::String(literal) => literal.clone(),
            TlaExpr::Ident(_) => self.resolve_tag(expr)?,
            _ => return None,
        };
        let wanted = variant_name(&literal);
        variants
            .iter()
            .find(|v| **v == wanted)
            .map(|v| format!("{name}::{v}"))
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
            // A literal in an enum-typed position is a variant, not a `&str`.
            // The `is` test in a guard already went through `enum_variant`; a
            // *value* did not, so `ostate = IF .. THEN Follower ELSE NotMember`
            // emitted `s.ostate == if .. { "follower" } else { "notMember" }`
            // and Verus rejected `LOstate == &str`. IF/CASE are recursed into
            // because that is where the literal usually sits.
            (ProjectedType::Enum { .. }, TlaExpr::String(_) | TlaExpr::Ident(_)) => {
                self.enum_literal(ty, expr)
            }
            // A `CASE` in an enum-typed position folds to the `IF` chain the
            // arm below already knows how to render. Without this the fold ran
            // in `project_expr`, which has no target type, and the branches
            // came out as `&str` against an enum.
            (ProjectedType::Enum { .. }, TlaExpr::Case { arms, other }) => {
                let other = other.as_ref()?;
                self.typed_value(ty, &case_as_if_then_else(arms, other))
            }
            (
                ProjectedType::Enum { .. },
                TlaExpr::IfThenElse {
                    cond,
                    then_expr,
                    else_expr,
                },
            ) => {
                // A branch that is not a literal -- `ELSE jstate[i]`, the value
                // the field already has -- is projected normally. Requiring
                // both branches to be literals made the arm decline and the
                // whole `IF` fall back, so one branch stayed a `&str`.
                let branch = |e: &TlaExpr| {
                    self.typed_value(ty, e)
                        .or_else(|| self.project_expr(e).ok())
                };
                Some(format!(
                    "if {} {{ {} }} else {{ {} }}",
                    self.project_expr(cond).ok()?,
                    branch(then_expr)?,
                    branch(else_expr)?
                ))
            }
            // A bare integer literal has no type to infer from when the other
            // side of the `==` is an `int` and the literal sits inside an `if`.
            // The same reason the `Map::new` closure below takes a suffix.
            (
                ProjectedType::Int,
                TlaExpr::IfThenElse {
                    cond,
                    then_expr,
                    else_expr,
                },
            ) if matches!(**then_expr, TlaExpr::Number(_))
                || matches!(**else_expr, TlaExpr::Number(_)) =>
            {
                // The suffix goes on the literals *inside* the `if`, which is
                // where there is no type to infer from. A literal in a plain
                // `s_.x == 1` needs nothing and reads better without it.
                let branch = |e: &TlaExpr| match e {
                    TlaExpr::Number(_) => Some(format!("{}int", self.project_expr(e).ok()?)),
                    _ => self.project_expr(e).ok(),
                };
                Some(format!(
                    "if {} {{ {} }} else {{ {} }}",
                    self.project_expr(cond).ok()?,
                    branch(then_expr)?,
                    branch(else_expr)?
                ))
            }
            (ProjectedType::Set(inner), TlaExpr::SetEnum(items)) if items.is_empty() => {
                Some(format!("Set::<{}>::empty()", inner.render()))
            }
            (ProjectedType::Seq(inner), TlaExpr::Tuple(items)) if items.is_empty() => {
                Some(format!("Seq::<{}>::empty()", inner.render()))
            }
            (ProjectedType::Map(_, value_ty), TlaExpr::FnConstruct { var, domain, body }) => {
                let set = self.project_set_valued(domain).ok()?;
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
        if let Some(tags) = self.dispatch_guard_tags(expr) {
            return Ok(DISPATCH_PREFIX.to_string() + &tags.join(","));
        }

        // `\E rec \in cmdLog[i] : /\ ... /\ x' = ...` -- an action that picks
        // a record out of its own state and updates from it. The binder is
        // quantified in the projected conjunct, and the body's updates are the
        // action's updates, so `updated` has to be threaded through: otherwise
        // P5 would frame a field the action assigns.
        if let TlaExpr::Exists { vars, body } = expr {
            if vars.len() == 1 && mentions_prime(body) {
                let bound = &vars[0];
                // `\E k \in 1 .. Len(log[i])` re-indexed onto the sequence's own
                // 0-based domain, because otherwise the projected quantifier has
                // no legal Verus trigger.
                //
                // TLA+ counts sequences from 1 and Verus's `Seq` from 0, so
                // `log[i][k]` projects to `s.log[k - 1]` -- and Verus refuses to
                // infer a trigger from a term with arithmetic in it. Every other
                // term mentioning `k` is a comparison or has `k` captured inside
                // a closure, neither of which can be a trigger either, so the
                // whole action was rejected. Quantifying over `k` one lower and
                // writing `k + 1` wherever the source said `k` leaves `s.log[k]`
                // as the trigger and changes nothing about what is stated.
                //
                // The `- 1` is put there by the projection, not by the source,
                // which is why the fix belongs here.
                let reindexed = self.reindex_range_binder(bound, body);
                let (bound, body) = match &reindexed {
                    Some((b, e)) => (b, e),
                    None => (bound, body.as_ref()),
                };
                if let Some(set) = &bound.set {
                    let elem = match self.type_of(set) {
                        Some(ProjectedType::Set(elem)) => elem.render(),
                        _ => "int".to_string(),
                    };
                    let domain = self.project_quantifier_domain(&bound.var, set)?;
                    // The binder has to be *typed* inside the body, or a test
                    // like `rec.status = "pre-accepted"` cannot be seen as a
                    // variant test and emits a string comparison against an enum.
                    let inner = match self.type_of(set) {
                        Some(ProjectedType::Set(elem)) => self.clone_with_param(&bound.var, *elem),
                        _ => self.clone_with_param(&bound.var, ProjectedType::Int),
                    };
                    let mut parts = Vec::new();
                    for conjunct in flatten_conjunction(body) {
                        let text = inner.project_conjunct(conjunct, updated, sends_seen)?;
                        if !text.is_empty() && !text.starts_with(DISPATCH_PREFIX) {
                            parts.push(text);
                        }
                    }
                    let var = &bound.var;
                    let body_text = parts.join(" && ");
                    // NOTE, and the one thing about this spec that Verus still
                    // rejects: a range binder whose body indexes a sequence
                    // gives Verus no trigger. `log[k]` projects to
                    // `s.log[k - 1]` -- TLA+ counts from 1 -- and Verus will
                    // not infer a trigger from a term containing arithmetic,
                    // which CLAUDE.md records as a known workaround needing an
                    // extra binder. The workaround does not apply as written
                    // here: a trigger has to cover *every* bound variable, and
                    // after moving the offset to its own variable `k` itself
                    // appears only in comparisons. The real answer is to
                    // re-index the quantifier onto the sequence's own 0-based
                    // domain, which is a projection pass and not string
                    // surgery on the emitted text. Not done.
                    return Ok(format!("exists|{var}: {elem}| {domain} && {body_text}"));
                }
            }
        }

        // `LET a == e1  b == e2 IN /\ x' = .. /\ y' = ..` -- definitions shared
        // by several updates. The body is a conjunction of the action's own
        // conjuncts, so it is projected as one: `updated` and `sends_seen` are
        // threaded through, or P5 would frame a field the action assigns.
        //
        // The definitions are substituted rather than kept, which is what `LET`
        // means. TLA+ definitions are pure, so duplicating one is duplicating a
        // value, not a computation; the cost is only that a definition used
        // three times is written out three times.
        if let TlaExpr::LetIn { defs, body } = expr {
            let expanded = expand_let(defs, body)?;
            let mut parts = Vec::new();
            for conjunct in flatten_conjunction(&expanded) {
                let text = self.project_conjunct(conjunct, updated, sends_seen)?;
                // A `m.type = ..` guard inside the LET is still the framework's
                // to read; swallowing it here would leave the handler
                // unreachable from the dispatch.
                if let Some(tag) = text.strip_prefix(DISPATCH_PREFIX) {
                    if !tag.is_empty() {
                        return Err(format!(
                            "LET body states the message tag `{tag}`; the dispatch \
                             reads it from the action's own conjuncts"
                        ));
                    }
                    continue;
                }
                if !text.is_empty() {
                    parts.push(text);
                }
            }
            return Ok(parts.join("\n        &&& "));
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

    /// The tags a receive handler declares, for a guard that names more than
    /// one: `m.mtype \in TermCarrying`.
    ///
    /// Textbook Raft has exactly one action of this shape -- "a message
    /// carrying a higher term demotes the receiver", which applies to all four
    /// of its message types -- and it is the shape a composed spec needs most,
    /// because C4 gives it one network and the base layer must ignore the other
    /// layer's messages. Without this the guard projected to a runtime test on
    /// `mtype`, which the dispatch has already consumed, so the emitted helper
    /// referred to unbound names and Verus rejected it.
    fn dispatch_guard_tags(&self, expr: &TlaExpr) -> Option<Vec<String>> {
        let msg = self.msg_param.as_deref()?;
        let TlaExpr::BinOp {
            op: TlaBinOp::In,
            left,
            right,
        } = expr
        else {
            return None;
        };
        let TlaExpr::RecordAccess { record, field } = &**left else {
            return None;
        };
        if !matches!(&**record, TlaExpr::Ident(n) if n == msg)
            || !TAG_FIELDS.contains(&field.as_str())
        {
            return None;
        }
        // The set has to be a literal one, or a name for one: a computed set of
        // tags is not something the dispatch can be built from.
        let items = match right.as_ref() {
            TlaExpr::SetEnum(items) => items.clone(),
            TlaExpr::Ident(name) => match self.spec.operator_bodies.get(name.as_str()) {
                Some((params, TlaExpr::SetEnum(items))) if params.is_empty() => items.clone(),
                _ => return None,
            },
            _ => return None,
        };
        items.iter().map(|i| self.resolve_tag(i)).collect()
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
            // The same comprehension written out in place instead of behind a
            // `Broadcast*` operator. `project_broadcast` already inlines to
            // exactly this shape, so routing it here is not a second path.
            TlaExpr::SetMap { .. } | TlaExpr::SetMapMulti { .. } => self.project_broadcast(expr),
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
    /// A message field the variant declares as an enum, rendered as a variant
    /// rather than the `&str` the source spells.
    ///
    /// The same rule as a record literal, which `project_expr`'s `Record` arm
    /// applies; the two packet paths each have their own copy of the field loop
    /// and so did not get it. `typed_value` recurses into the `IF` that Raft's
    /// `mresult` sits in.
    fn enum_typed_field(
        &self,
        tag: &Option<String>,
        name: &str,
        value: &TlaExpr,
    ) -> Option<String> {
        let ty = tag
            .as_deref()
            .and_then(|t| self.spec.messages.iter().find(|m| m.tag == t))
            .and_then(|v| v.fields.iter().find(|(f, _)| f == name))
            .map(|(_, ty)| ty.clone())?;
        match ty {
            ProjectedType::Enum { .. } => self.typed_value(&ty, value),
            _ => None,
        }
    }

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
                other => {
                    let name = to_snake_case(other);
                    let rendered = match self.enum_typed_field(&tag, &name, value) {
                        Some(text) => text,
                        None => self.project_expr(value)?,
                    };
                    fields.push((name, rendered));
                }
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
        match self.inline_call(expr)? {
            TlaExpr::SetMap {
                expr: body,
                var,
                set,
            } => {
                // The comprehension ranges over the peers; the projected form
                // maps the peer set to packets.
                let peers = self.project_peer_set(&set)?;
                let packet = self
                    .packet_context()
                    .project_packet_with_binders(&body, &[var.as_str()])?;
                Ok(format!("{peers}.map(|{var}: int| {packet})"))
            }
            TlaExpr::SetMapMulti {
                expr: body,
                bindings,
            } => self.project_multi_broadcast(&body, &bindings),
            _ => Err(format!(
                "send expression not yet projectable: {}",
                render_source(expr)
            )),
        }
    }

    /// A broadcast whose comprehension has more than one binder:
    ///
    /// ```text
    /// { PreacceptReq(i, d, jepoch[i], cmd) : d \in viewProposers[i],
    ///                                        cmd \in chosenValue[i] }
    /// ```
    ///
    /// The set is the cross product, so the projected form is one `map` per
    /// binder, innermost first, with a `flatten` for every nesting level the
    /// maps introduced. Each `map` over a set of sets adds one level, so `n`
    /// binders need `n - 1` flattens and the result is a `Set<LPacket>` --
    /// the same type the single-binder path produces, which is what
    /// `sent_packets` is compared against.
    fn project_multi_broadcast(
        &self,
        body: &TlaExpr,
        bindings: &[TlaQuantBound],
    ) -> Result<String, String> {
        let mut sets = Vec::new();
        for binding in bindings {
            let Some(set) = binding.set.as_ref() else {
                return Err(format!(
                    "comprehension binder `{}` has no domain",
                    binding.var
                ));
            };
            sets.push((
                binding.var.as_str(),
                self.project_peer_set(set)?,
                self.binder_type(set)?,
            ));
        }
        let binders: Vec<&str> = sets.iter().map(|(v, ..)| *v).collect();
        let mut acc = self
            .packet_context()
            .project_packet_with_binders(body, &binders)?;
        // Innermost binder first: it is the one whose `map` produces packets
        // directly, and every enclosing `map` then needs a `flatten`.
        for (i, (var, set, ty)) in sets.iter().enumerate().rev() {
            acc = if i + 1 == sets.len() {
                format!("{set}.map(|{var}: {ty}| {acc})")
            } else {
                format!("{set}.map(|{var}: {ty}| {acc}).flatten()")
            };
        }
        Ok(acc)
    }

    /// The context a broadcast's packet is projected in: the message being
    /// handled is not in scope inside a comprehension, so its tag and the
    /// enclosing helper's parameter types are dropped.
    fn packet_context(&self) -> ActionContext<'a> {
        ActionContext {
            spec: self.spec,
            param_types: Default::default(),
            msg_tag: None,
            node_param: self.node_param.clone(),
            msg_param: self.msg_param.clone(),
            network: self.network.clone(),
        }
    }

    /// The Rust type a comprehension binder takes, decided from the projected
    /// type of the set it ranges over.
    ///
    /// The single-binder broadcast can write `int` because its binder ranges
    /// over the peers. A second binder does not have to: `Resubmit`
    /// re-proposes over `chosenValue[i]`, a `Set<LCommand>`, and annotating
    /// that binder `int` emits a closure that does not typecheck. The type is
    /// therefore read off, never assumed -- and `int` is used only for a set
    /// the projection has already recognised as the node set, whose elements
    /// are node ids.
    fn binder_type(&self, set: &TlaExpr) -> Result<String, String> {
        if let Some(ProjectedType::Set(elem)) = self.type_of(set) {
            return Ok(elem.render());
        }
        // `Node` and `Node \ {self}` carry no projected type of their own.
        let base = match set {
            TlaExpr::BinOp {
                op: TlaBinOp::Setminus,
                left,
                ..
            } => left.as_ref(),
            other => other,
        };
        match self.project_node_set(base) {
            Ok(_) => Ok("int".to_string()),
            Err(_) => Err(format!(
                "element type of comprehension domain {}",
                render_source(set)
            )),
        }
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
            other => self.project_set_valued(other),
        }
    }

    fn project_node_set(&self, expr: &TlaExpr) -> Result<String, String> {
        let rendered = render_source(expr);
        if rendered == self.spec.node_set {
            Ok(format!("c.{}", self.spec.node_set_constant()))
        } else {
            Err(format!("node set {rendered}"))
        }
    }

    /// `\E k \in 1 .. hi` rewritten as `\E k \in 0 .. hi - 1` with every use of
    /// `k` in the body replaced by `k + 1`.
    ///
    /// Same set of witnesses, stated one lower. Its whole purpose is that a
    /// sequence read then projects to `s.log[k]` rather than `s.log[k - 1]`,
    /// and Verus can use the former as a trigger and not the latter. Only a
    /// range whose lower bound is literally 1 qualifies -- that is the TLA+
    /// sequence convention, and re-indexing anything else would be a guess.
    fn reindex_range_binder(
        &self,
        bound: &TlaQuantBound,
        body: &TlaExpr,
    ) -> Option<(TlaQuantBound, TlaExpr)> {
        let set = bound.set.as_ref()?;
        let (low, high) = self.as_range(set)?;
        if !matches!(&low, TlaExpr::Number(n) if n.to_i64() == Some(1)) {
            return None;
        }
        // Only worth doing when the body actually indexes with the binder;
        // otherwise it is churn that changes emitted text for no reason.
        if !indexes_with(body, &bound.var) {
            return None;
        }
        let shifted = TlaExpr::BinOp {
            op: TlaBinOp::Plus,
            left: Box::new(TlaExpr::Ident(bound.var.clone())),
            right: Box::new(TlaExpr::Number(crate::tla::ast::TlaNumber::Decimal(
                "1".to_string(),
            ))),
        };
        let body = substitute(body, &bound.var, &shifted);
        let set = TlaExpr::BinOp {
            op: TlaBinOp::DotDot,
            left: Box::new(TlaExpr::Number(crate::tla::ast::TlaNumber::Decimal(
                "0".to_string(),
            ))),
            right: Box::new(TlaExpr::BinOp {
                op: TlaBinOp::Minus,
                left: Box::new(high),
                right: Box::new(TlaExpr::Number(crate::tla::ast::TlaNumber::Decimal(
                    "1".to_string(),
                ))),
            }),
        };
        Some((
            TlaQuantBound {
                var: bound.var.clone(),
                set: Some(set),
            },
            body,
        ))
    }

    /// The node set, or any other expression the projection **knows** to be
    /// set-valued.
    ///
    /// Tables and broadcasts are not always built over the node set, and
    /// requiring that they are is what produced thirteen of the twenty-four
    /// gaps on the tier4 Jetpack composition: Raft's `nextIndex` is a table
    /// over `Server` (a client is never a peer), Jetpack's `cmdPool` is a table
    /// over `Key`, and every recovery broadcast goes to `viewMembers[i]` --
    /// the node's own view, not the whole cluster.
    ///
    /// Knowing it is set-valued is the whole condition, and the reason this is
    /// not simply `project_expr`: an unresolved identifier projects to itself,
    /// so `[k \in Nat |-> ..]` would emit `Map::new(Nat, ..)` against a `Nat`
    /// that does not exist. The same guard is why the quantifier-domain
    /// fallback below is written this way.
    fn project_set_valued(&self, expr: &TlaExpr) -> Result<String, String> {
        match self.project_node_set(expr) {
            Ok(set) => Ok(set),
            Err(node_set_error) => match self.type_of(expr) {
                Some(ProjectedType::Set(_)) => self.project_expr(expr),
                _ => Err(node_set_error),
            },
        }
    }

    /// Like `project_packet`, but with the comprehension's binders in scope so
    /// `d` resolves to a loop variable rather than to a constant.
    fn project_packet_with_binders(
        &self,
        expr: &TlaExpr,
        binders: &[&str],
    ) -> Result<String, String> {
        let record = self.inline_record(expr)?;
        let mut dst = None;
        let mut tag = None;
        let mut fields = Vec::new();
        for (name, value) in &record {
            let projected = |v: &TlaExpr| -> Result<String, String> {
                if let TlaExpr::Ident(n) = v {
                    if binders.contains(&n.as_str()) {
                        return Ok(n.clone());
                    }
                }
                self.project_expr_with_binders(v, binders)
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
                other => {
                    let name = to_snake_case(other);
                    let rendered = match self.enum_typed_field(&tag, &name, value) {
                        Some(text) => text,
                        None => projected(value)?,
                    };
                    fields.push((name, rendered));
                }
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
        self.project_expr_with_binders(expr, &[binder])
    }

    fn project_expr_with_binders(
        &self,
        expr: &TlaExpr,
        binders: &[&str],
    ) -> Result<String, String> {
        // Reads indexed by a comprehension binder: `sendSeq[s][d]` -> the
        // node's table at `d`.
        if let TlaExpr::FnApply { func, arg } = expr {
            if let TlaExpr::Ident(binder) = arg.as_ref() {
                if binders.contains(&binder.as_str()) {
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
        // Simultaneous, not one parameter after another. Substituting in
        // sequence lets a later parameter capture an identifier an earlier
        // substitution just introduced, and TLA+ specs name parameters after
        // what they carry, so the collision is not exotic:
        //
        //     PreacceptReq(s, d, e, c) == [.., mepoch |-> e, msource |-> s, ..]
        //     BroadcastPreaccept(c, e, cmd, members) ==
        //       { PreacceptReq(c, d, e, cmd) : d \in members }
        //
        // called with `e := clientEpoch[c]`. In sequence, `s := c` and
        // `e := clientEpoch[c]` put `c` into the body, and the *fourth*
        // substitution `c := cmd` then rewrote both -- yielding
        // `mepoch |-> clientEpoch[cmd]` and `msource |-> cmd`. The first
        // errored, which is the only reason this was found; the second is a
        // message sent from the wrong node, and would have verified.
        Ok(substitute_all(
            &body,
            &params
                .iter()
                .cloned()
                .zip(args.iter().cloned())
                .collect::<BTreeMap<_, _>>(),
        ))
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
        // A literal in an enum-typed branch is a variant. Without this
        // `jstate' = [jstate EXCEPT ![i] = IF .. THEN Ready ELSE jstate[i]]`
        // emitted `if .. { "ready" } else { s.jstate }`, whose two branches do
        // not even have the same type.
        if let Some(field) = self.state_field(var) {
            let field = field.to_string();
            if let Some(ty @ ProjectedType::Enum { .. }) = &self.field_type(&field) {
                if let Some(text) = self.typed_value(ty, value) {
                    return Ok(text);
                }
            }
        }
        self.project_update(var, value)
    }

    /// Whether an expression denotes the acting node's own entry of `var` --
    /// either `var[self]` written out, or the `@` of an enclosing `![self]`
    /// update, which names the same value.
    fn is_own_entry(&self, var: &str, expr: &TlaExpr) -> bool {
        match expr {
            TlaExpr::Ident(name) => name == "@",
            TlaExpr::FnApply { func, arg } => {
                matches!(&**func, TlaExpr::Ident(name) if name == var) && self.is_node_index(arg)
            }
            _ => false,
        }
    }

    /// `![k] = e, ..` applied to the node's own entry of `field`, which after
    /// projection *is* `s.field`. The nested spelling of a two-level EXCEPT
    /// ends where the flat `![self][k]` one does: `.insert(k, e)`. The two are
    /// not interchangeable in general -- the flat spelling still cannot
    /// project an `@` in its value, see the `old_value` match below -- but
    /// where both project they agree.
    ///
    /// Restricted to a map-typed field on purpose. A sequence-typed one would
    /// need `.update(k - 1, e)` -- Verus's `Seq::insert` shifts the tail, and
    /// the index would lose one -- and an EXCEPT that guessed between the two
    /// is the off-by-one `project_index` exists to prevent. So it is a gap.
    fn project_entry_updates(
        &self,
        field: &str,
        updates: &[TlaExceptUpdate],
    ) -> Result<String, String> {
        let ty = self.field_type(field);
        if !matches!(ty, Some(ProjectedType::Map(..))) {
            return Err(format!(
                "EXCEPT over the acting node's own `{field}`, which projects to \
                 `{}`; only a map is updated by key",
                ty.map(|t| t.render()).unwrap_or_else(|| "?".to_string())
            ));
        }
        let mut acc = format!("s.{field}");
        for update in updates {
            let [TlaExceptPath::Index(key)] = update.path.as_slice() else {
                return Err(format!(
                    "EXCEPT over the acting node's own `{field}` with a \
                     {}-component path",
                    update.path.len()
                ));
            };
            let key = self.project_expr(key)?;
            // `@` binds to the original function's entry, `s.field[k]`, not to
            // the accumulator -- the same choice the multi-update path above
            // makes. It is not literally TLA+'s rule: `[f EXCEPT ![a] = e1,
            // ![b] = e2]` is defined as `[[f EXCEPT ![a] = e1] EXCEPT ![b] =
            // e2]`, so `e2`'s `@` sees the partial update. The two agree
            // unless one EXCEPT writes the same key twice, and disagreeing
            // with the path above would be worse than agreeing with it.
            let old = TlaExpr::Ident(format!("{PROJECTED_MARK}s.{field}[{key}]"));
            let value = self.project_expr(&substitute(&update.value, "@", &old))?;
            acc = format!("{acc}.insert({key}, {value})");
        }
        Ok(acc)
    }

    /// `s.field` updated at one index, with the operation and the index chosen
    /// from the field's projected type.
    ///
    /// TLA+'s `[f EXCEPT ![k] = v]` **replaces**. For a `Map` that is
    /// `insert(k, v)` and the key passes through untouched. For a `Seq` it is
    /// `update(k - 1, v)`: vstd's `Seq::insert` is
    /// `subrange(0,i).push(a).add(subrange(i, len))`, which *grows* the
    /// sequence and shifts the tail, and the index still has to lose one
    /// because TLA+ counts from 1.
    ///
    /// Emitting `insert` for both was two independent wrongs on one line: the
    /// guard read `s.log[k - 1]` while the update wrote at `k`, and the write
    /// lengthened the log instead of overwriting an entry. Verus accepts it --
    /// both are `Seq` operations of the right type.
    ///
    /// A field whose type the projection does not know is a gap, because the
    /// two operations are not interchangeable and guessing picks one.
    fn project_indexed_update(
        &self,
        field: &str,
        index: &TlaExpr,
        value: &str,
    ) -> Result<String, String> {
        match self.field_type(field) {
            Some(ProjectedType::Map(..)) => Ok(format!(
                "s.{field}.insert({}, {value})",
                self.project_expr(index)?
            )),
            Some(ProjectedType::Seq(_)) => Ok(format!(
                "s.{field}.update({}, {value})",
                self.seq_index(index)?
            )),
            other => Err(format!(
                "EXCEPT at an index of `{field}`, which projects to `{}` -- \
                 only a map is updated by key and only a sequence by position",
                other.map(|t| t.render()).unwrap_or_else(|| "?".to_string())
            )),
        }
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
                // Several updates to the same table chain: `[f EXCEPT ![p][a] = x,
                // ![p][b] = y]` is `s.f.insert(a, x).insert(b, y)`. Every `@`
                // still resolves against the *original* function, which is
                // TLA+'s rule and is what the per-update substitution below does.
                if updates.len() > 1 {
                    let mut acc = format!("s.{field}");
                    for update in updates {
                        let [TlaExceptPath::Index(outer), TlaExceptPath::Index(inner)] =
                            update.path.as_slice()
                        else {
                            return Err(format!(
                                "EXCEPT with {} updates needs each to index the acting \
                                 node and then the table",
                                updates.len()
                            ));
                        };
                        if !self.is_node_index(outer) {
                            return Err(format!(
                                "EXCEPT updates `{var}` at a node other than the acting one"
                            ));
                        }
                        let old_value = TlaExpr::FnApply {
                            func: Box::new(TlaExpr::Ident(format!("{PROJECTED_MARK}s.{field}"))),
                            arg: Box::new(inner.clone()),
                        };
                        let value_expr = substitute(&update.value, "@", &old_value);
                        let value = self.project_expr(&value_expr)?;
                        let one = self.project_indexed_update(field, inner, &value)?;
                        // The accumulator has already applied earlier updates,
                        // so only the operation and its arguments come from the
                        // helper; the receiver is whatever we have built.
                        acc = format!(
                            "{acc}{}",
                            one.strip_prefix(&format!("s.{field}")).unwrap_or(&one)
                        );
                    }
                    return Ok(acc);
                }
                let update = &updates[0];
                // `[x EXCEPT ![self] = [x[self] EXCEPT ![k] = e]]` -- the nested
                // spelling of `[x EXCEPT ![self][k] = e]`. TLA+ gives the two the
                // same meaning; only the flat one used to project, so jetpack's
                // `cmdPool` update was reported as a gap.
                //
                // It is recognised here, before the `@` substitution below, on
                // purpose: an `@` inside the inner EXCEPT is the *inner*
                // function's old value, and `substitute` does not know `@` is
                // rebound, so it would capture it and silently read the whole
                // table where the source asked for one key of it.
                if let [TlaExceptPath::Index(index)] = update.path.as_slice() {
                    if self.is_node_index(index) {
                        if let TlaExpr::FnExcept {
                            func: inner,
                            updates: inner_updates,
                        } = &update.value
                        {
                            if self.is_own_entry(var, inner) {
                                return self.project_entry_updates(field, inner_updates);
                            }
                        }
                    }
                }
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
                // The field's own type first: `mark' = [mark EXCEPT ![self] =
                // CASE ..]` replaces the whole field, so the value sits in a
                // position whose type is known, and a literal there is a
                // variant rather than a `&str`.
                let value = match self
                    .field_type(field)
                    .and_then(|ty| self.typed_value(ty, &value_expr))
                {
                    Some(text) => text,
                    None => self.project_expr(&value_expr)?,
                };
                match update.path.as_slice() {
                    // `![self] = e` -- one index, the acting node: the whole
                    // projected field becomes `e`.
                    [TlaExceptPath::Index(index)] if self.is_node_index(index) => Ok(value),
                    // `![self][q] = e` -- the outer index is the node and goes,
                    // the inner one indexes the projected table.
                    [TlaExceptPath::Index(outer), TlaExceptPath::Index(inner)]
                        if self.is_node_index(outer) =>
                    {
                        self.project_indexed_update(field, inner, &value)
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
            // `x' = CASE p -> a [] q -> b [] OTHER -> x`. The same shape as the
            // `IF` above with one level per arm, so it is folded into nested
            // `IF`s and projected by that arm rather than rendered again here.
            // Folding is what keeps `OTHER -> x` meaning "leave it alone":
            // `project_branch_value` is the only place that rule lives.
            //
            // Arms are taken in order. TLA+ defines `CASE` by `CHOOSE`, so the
            // value is unspecified when two guards hold at once; first-match is
            // TLC's rule and the one `translator.rs::translate_case` already
            // follows, and Raft's two guards here are disjoint tests on one
            // enum field, so nothing is lost for this spec.
            //
            // A `CASE` with no `OTHER` has *no value* when no guard holds, so
            // it is a gap rather than an invented default.
            TlaExpr::Case { arms, other } => {
                let Some(other) = other else {
                    return Err(format!(
                        "CASE without an OTHER arm assigned to `{var}`: it has no \
                         value when no guard holds"
                    ));
                };
                self.project_update(var, &case_as_if_then_else(arms, other))
            }
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

    /// `x = "label"` where `x` is enum-typed, as the projected test and the
    /// variant it names.
    ///
    /// The left-hand side need not be a state field: EPaxos compares
    /// `rec.status`, a field of a record it pulled out of its own log.
    fn enum_test(&self, left: &TlaExpr, right: &TlaExpr) -> Option<(String, String)> {
        let literal = match right {
            TlaExpr::String(t) => t.clone(),
            TlaExpr::Ident(_) => self.resolve_tag(right)?,
            _ => return None,
        };
        let wanted = variant_name(&literal);
        let ProjectedType::Enum { variants, .. } = self.type_of(left)? else {
            return None;
        };
        if !variants.contains(&wanted) {
            return None;
        }
        Some((self.project_expr(left).ok()?, wanted))
    }

    /// A string literal passed where the callee declares an enum-typed
    /// parameter, rendered as that variant.
    fn enum_argument(&self, callee: &str, index: usize, arg: &TlaExpr) -> Option<String> {
        let literal = match arg {
            TlaExpr::String(t) => t.clone(),
            TlaExpr::Ident(_) => self.resolve_tag(arg)?,
            _ => return None,
        };
        let (params, body) = self.spec.operator_bodies.get(callee)?;
        let param = params.get(index)?;
        // The parameter's type comes from the record field it fills, which is
        // the same rule `infer_helper_param_types` uses for constructors.
        let TlaExpr::Record(fields) = body else {
            return None;
        };
        let field = fields
            .iter()
            .find(|(_, v)| matches!(v, TlaExpr::Ident(n) if n == param))
            .map(|(f, _)| to_snake_case(f))?;
        let wanted = variant_name(&literal);
        self.spec.records.iter().find_map(|(_, fs)| {
            fs.iter().find_map(|(f, ty)| match ty {
                ProjectedType::Enum { name, variants }
                    if *f == field && variants.contains(&wanted) =>
                {
                    Some(format!("{name}::{wanted}"))
                }
                _ => None,
            })
        })
    }

    /// A copy of this context with one more parameter in scope, so a
    /// comprehension binder can be typed inside its own body.
    fn clone_with_param(&self, var: &str, ty: ProjectedType) -> ActionContext<'a> {
        let mut param_types = self.param_types.clone();
        param_types.insert(var.to_string(), ty);
        ActionContext {
            spec: self.spec,
            param_types,
            msg_tag: self.msg_tag.clone(),
            node_param: self.node_param.clone(),
            msg_param: self.msg_param.clone(),
            network: self.network.clone(),
        }
    }

    /// The variants a set literal names, when the left-hand side is an
    /// enum-typed field and every element resolves to one of its labels.
    fn enum_variants_of(&self, left: &TlaExpr, right: &TlaExpr) -> Option<Vec<String>> {
        let TlaExpr::SetEnum(items) = right else {
            return None;
        };
        if items.is_empty() {
            return None;
        }
        // The left side is usually a state field; since an action parameter can
        // be enum-typed too -- `\E op \in {ReconfigAdd, ReconfigRemove}` is
        // the action's own bound -- the type is asked for directly rather than
        // via the field name. Emitting `set!["add", "remove"].contains(op)`
        // against an enum-typed `op` is what this stops.
        let ProjectedType::Enum { variants, .. } = self.type_of(left)? else {
            return None;
        };
        items
            .iter()
            .map(|item| {
                let literal = match item {
                    TlaExpr::String(t) => t.clone(),
                    TlaExpr::Ident(_) => self.resolve_tag(item)?,
                    _ => return None,
                };
                let wanted = variant_name(&literal);
                variants.iter().find(|v| **v == wanted).cloned()
            })
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
            // A record literal has the type of the struct its field names
            // match, the same way its *value* is projected. Without this a
            // constructor like `Inst(o, n) == [owner |-> o, num |-> n]` gets a
            // return type from the emitted text, which says `int`.
            TlaExpr::Record(fields) => {
                let names: Vec<String> = fields.iter().map(|(n, _)| to_snake_case(n)).collect();
                self.spec
                    .records
                    .iter()
                    .find(|(_, fs)| {
                        fs.len() == names.len() && fs.iter().all(|(f, _)| names.contains(f))
                    })
                    .map(|(name, fs)| ProjectedType::Record {
                        name: name.clone(),
                        fields: fs.clone(),
                    })
            }
            // `CHOOSE x \in S : P` has the element type of `S`; a set
            // comprehension is a set of whatever the body produces. Both are
            // helper *bodies* in EPaxos (`Max`, `KnownInstances`), so getting
            // them wrong types the whole function wrong.
            TlaExpr::Choose { set, .. } => match self.type_of(set.as_deref()?)? {
                ProjectedType::Set(elem) => Some(*elem),
                _ => None,
            },
            TlaExpr::SetMap {
                expr: body,
                var,
                set,
            } => {
                let elem = match self.type_of(set)? {
                    ProjectedType::Set(elem) => *elem,
                    _ => return None,
                };
                let inner = self.clone_with_param(var, elem);
                inner
                    .value_type(body)
                    .map(|t| ProjectedType::Set(Box::new(t)))
            }
            TlaExpr::SetEnum(items) => {
                let first = items.first()?;
                self.value_type(first)
                    .map(|t| ProjectedType::Set(Box::new(t)))
            }
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
            // A parameter first, then a constant: `Server` and `Key` are
            // CONSTANTS, and a table built over one (`nextIndex`, `cmdPool`)
            // needs to be recognised as set-valued the same way a per-node set
            // variable is.
            TlaExpr::Ident(name) => self.param_types.get(name.as_str()).cloned().or_else(|| {
                let snake = crate::tla::projection::to_snake_case(name);
                self.spec
                    .constants
                    .iter()
                    .find(|(n, _)| *n == snake)
                    .map(|(_, t)| t.clone())
            }),
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
                // `(k + 1) - 1` is `k`, and folding it is not cosmetic: a
                // re-indexed range binder writes `k + 1` where the source said
                // `k`, and leaving the arithmetic in the subscript is exactly
                // what stops Verus inferring a trigger -- which is the whole
                // reason the binder was re-indexed.
                if let TlaExpr::BinOp {
                    op: TlaBinOp::Plus,
                    left,
                    right,
                } = index
                {
                    if matches!(right.as_ref(), TlaExpr::Number(n) if n.to_i64() == Some(1)) {
                        return self.project_expr(left);
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
                    Ok(match field.as_str() {
                        "src" | "source" | "sender" | "msource" => "src".to_string(),
                        "dst" | "dest" | "receiver" | "mdest" => "c.node_id".to_string(),
                        other => to_snake_case(other),
                    })
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
            } if self.enum_test(left, right).is_some() => {
                let (l, variant) = self.enum_test(left, right).expect("guarded above");
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
                    // Same spelling the older translator uses (translator.rs).
                    TlaBinOp::Subseteq => format!("{l}.subset_of({r})"),
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
            // `DOMAIN f`. A TLA+ function projects to a Verus `Map`, whose
            // domain is `.dom()`. Jetpack's conflict test walks the keys a node
            // already holds a command for.
            TlaExpr::UnaryOp {
                op: TlaUnaryOp::Domain,
                operand,
            } => Ok(format!("{}.dom()", self.parenthesised(operand, 9)?)),
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
                // First match by field-name set. Two declared records sharing a
                // field-name set but differing in which field is enum-typed
                // would get the wrong enum qualified below -- pre-existing for
                // the struct name, newly extended to the field values.
                let Some((struct_name, declared)) = self.spec.records.iter().find(|(_, fs)| {
                    fs.len() == names.len() && fs.iter().all(|(f, _)| names.contains(f))
                }) else {
                    return Err(format!(
                        "record value with fields {names:?} matches no declared record type"
                    ));
                };
                let rendered: Result<Vec<String>, String> = fields
                    .iter()
                    .map(|(n, v)| {
                        let name = to_snake_case(n);
                        // A field the declaration types as an enum takes a
                        // variant, not the `&str` the source spells: `Entry`'s
                        // `command` is `LEntryCommand`, and
                        // `command |-> InitClusterCommand` must render as
                        // `LEntryCommand::InitCluster`.
                        let value = match declared
                            .iter()
                            .find(|(f, _)| *f == name)
                            .and_then(|(_, ty)| self.enum_literal(ty, v))
                        {
                            Some(variant) => variant,
                            None => self.project_expr(v)?,
                        };
                        Ok(format!("{name}: {value}"))
                    })
                    .collect();
                Ok(format!("{struct_name} {{ {} }}", rendered?.join(", ")))
            }
            TlaExpr::SetEnum(items) if items.is_empty() => Ok("Set::empty()".to_string()),
            TlaExpr::Tuple(items) if items.is_empty() => Ok("Seq::empty()".to_string()),
            // `<<a, b, c>>`. A TLA+ tuple *is* the sequence `[i \in 1..n |-> ..]`
            // -- the language has no separate product type -- so a literal one
            // projects to a `Seq` literal, exactly as `{a, b}` projects to
            // `set![a, b]` just below. Verus's `Seq` is homogeneous, so a spec
            // that uses a tuple as a heterogeneous pair still does not project;
            // `t2_02_epaxos` rewrites that shape as a record for the same reason.
            //
            // A tuple reaching a field whose projected type is not a `Seq` now
            // emits rather than gapping. That is loud, not silent -- Verus
            // rejects `Seq<int>` against `int` -- and the `SetEnum` arm beside
            // it has carried the same exposure all along.
            TlaExpr::Tuple(items) => {
                let rendered: Result<Vec<String>, String> =
                    items.iter().map(|i| self.project_expr(i)).collect();
                Ok(format!("seq![{}]", rendered?.join(", ")))
            }
            TlaExpr::SetEnum(items) => {
                let rendered: Result<Vec<String>, String> =
                    items.iter().map(|i| self.project_expr(i)).collect();
                Ok(format!("set![{}]", rendered?.join(", ")))
            }
            // `CHOOSE x \in S : P(x)`. Verus's `choose` is Hilbert's epsilon and
            // so is TLA+'s CHOOSE: both pick *some* witness and both are
            // deterministic in the predicate, so this is a direct translation
            // rather than an interpretation. `Max(s) == CHOOSE x \in s :
            // \A y \in s : x >= y` is the idiom that needs it.
            TlaExpr::Choose { var, set, body } => {
                let Some(set) = set else {
                    return Err("unbounded CHOOSE".to_string());
                };
                let ty = match self.type_of(set) {
                    Some(ProjectedType::Set(elem)) => elem.render(),
                    _ => "int".to_string(),
                };
                let domain = self.project_quantifier_domain(var, set)?;
                Ok(format!(
                    "choose|{var}: {ty}| {domain} && {}",
                    self.project_expr(body)?
                ))
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
                for (i, arg) in args.iter().enumerate() {
                    // The acting node disappears from the argument list: the
                    // projected helper is already about this node. It is the
                    // *argument* that identifies it, not the parameter name --
                    // the helper may call its own parameter something else.
                    if self.is_node_index(arg) {
                        continue;
                    }
                    // A literal in a position the callee types as an enum names
                    // a variant. `Rec(i, "pre-accepted", ..)` must become
                    // `LRec(.., LRecordStatus::PreAccepted, ..)`, not a `&str`.
                    if let Some(text) = self.enum_argument(name, i, arg) {
                        rendered.push(text);
                        continue;
                    }
                    rendered.push(self.project_expr(arg)?);
                }
                let _ = params;
                Ok(format!("L{}({})", rust_ident(name), rendered.join(", ")))
            }
            // `[x EXCEPT ![self] ...]` used as a value, which is how a helper
            // that returns an updated table is written.
            TlaExpr::FnExcept { func, .. } => {
                let TlaExpr::Ident(var) = &**func else {
                    return Err(format!("EXCEPT over {}", render_source(func)));
                };
                self.project_update(var, expr)
            }
            // `{rec.inst : rec \in log}` -- a set comprehension over a value
            // the node holds, which is a `map` rather than a quantifier.
            TlaExpr::SetMap {
                expr: body,
                var,
                set,
            } => Ok(format!(
                "{}.map(|{var}: {}| {})",
                self.project_expr(set)?,
                match self.type_of(set) {
                    Some(ProjectedType::Set(elem)) => elem.render(),
                    _ => "int".to_string(),
                },
                self.project_expr_with_binder(body, var)?
            )),
            // `{j \in Server : matchIndex[i][j] >= k}` -- a set comprehension
            // with a *filter* rather than a map. This is P4's own shape: every
            // counted quorum in the corpus is written as
            // `Cardinality({j \in S : P(j)}) * 2 > Cardinality(S)`, and until
            // now the set inside the count was refused.
            //
            // `project_set_valued` on the domain, not `project_expr`, for the
            // same reason a table's domain uses it: the guard is what stops a
            // domain of unknown type from emitting a name that does not exist.
            TlaExpr::SetFilter { var, set, filter } => {
                let domain = self.project_set_valued(set)?;
                let elem = match self.type_of(set) {
                    Some(ProjectedType::Set(elem)) => elem.render(),
                    _ => "int".to_string(),
                };
                let predicate = self.project_expr_with_binder(filter, var)?;
                Ok(format!("{domain}.filter(|{var}: {elem}| {predicate})"))
            }
            // `[d \in Node |-> e]` -- a table built over the peers.
            TlaExpr::FnConstruct { var, domain, body } => {
                let set = self.project_set_valued(domain)?;
                let value = self.project_expr_with_binder(body, var)?;
                Ok(format!("Map::new({set}, |{var}: int| {value})"))
            }
            // `LET a == e IN body` in a value position -- a helper body, or the
            // right-hand side of an update. Same expansion as the conjunct form.
            TlaExpr::LetIn { defs, body } => self.project_expr(&expand_let(defs, body)?),
            // `CASE p -> a [] OTHER -> b` in a *value* position, which is where
            // it sits when the update is `x' = [x EXCEPT ![i] = CASE ..]`
            // rather than `x' = CASE ..`. `project_update` folds the outer
            // form; this is the same fold one level in, and without it the
            // shape was a gap depending only on where the CASE was written.
            TlaExpr::Case { arms, other } => {
                let Some(other) = other else {
                    return Err("CASE without an OTHER arm has no value when no \
                                guard holds"
                        .to_string());
                };
                self.project_expr(&case_as_if_then_else(arms, other))
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
        // A block-like expression in an operand position. Inlining a `LET` puts
        // one there for the first time: `succ \cup (members \ heard)` with
        // `succ == IF .. THEN .. ELSE ..` renders as
        // `if .. { .. } else { .. }.union(..)`. rustc does bind the postfix to
        // the whole `if`, so this is belt and braces rather than a fix -- but
        // the reader cannot tell that at a glance, and neither can a
        // hand-edited derivative.
        if matches!(
            expr,
            TlaExpr::IfThenElse { .. }
                | TlaExpr::Case { .. }
                | TlaExpr::LetIn { .. }
                | TlaExpr::Choose { .. }
                | TlaExpr::Forall { .. }
                | TlaExpr::Exists { .. }
        ) {
            return Ok(format!("({text})"));
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
            // `\E k \in 1 .. Len(log[i])` -- a binder over an integer range.
            // A range has no projected *value*, which is the same reason
            // `x \in a .. b` is emitted as a comparison rather than a
            // `contains`, so the domain becomes a bound on the emitted
            // parameter instead.
            //
            // The node set is tried first, and the guard is not decoration: a
            // spec may spell its own node set as a range (`Proc == 0 .. N-1`),
            // `as_range` follows a name to its body, and without the guard this
            // arm would take those binders over from `project_node_set` and
            // change what an already-projecting spec emits.
            other if self.project_node_set(other).is_err() && self.as_range(other).is_some() => {
                let (low, high) = self.as_range(other).expect("guarded above");
                Ok(format!(
                    "{} <= {var} && {var} <= {}",
                    self.parenthesised(&low, precedence(&TlaBinOp::Leq))?,
                    self.parenthesised(&high, precedence(&TlaBinOp::Leq))?
                ))
            }
            // The node set, or -- as EPaxos's `\E rec \in cmdLog[i]` needs --
            // any set-valued expression the node itself holds. See
            // `project_set_valued` for why the type guard is not optional.
            other => Ok(format!(
                "{}.contains({var})",
                self.project_set_valued(other)?
            )),
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
                        let first_time = out.insert(name.clone(), param.name.clone()).is_none();
                        // A composed spec dispatches through an intermediate
                        // operator: `Next` binds the message and calls
                        // `Receive(i, m)`, whose body is a disjunction of the
                        // layers' own handlers. Without following that step
                        // the real handlers have no message parameter, so
                        // `m.field` has no type -- which is what decides
                        // whether indexing it loses one. The tier4 Jetpack
                        // composition reported `application m.mentries[1]`
                        // for exactly this reason, on a handler that
                        // translates fine when `Next` calls it directly.
                        //
                        // Guarded on `first_time` so a cycle terminates.
                        if first_time {
                            collect_calls_with(&callee.body, &param.name, module, out);
                        }
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

pub(crate) fn mentions_prime(expr: &TlaExpr) -> bool {
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

/// `CASE p -> a [] q -> b [] OTHER -> c` as `IF p THEN a ELSE IF q THEN b ELSE c`.
///
/// Desugaring rather than rendering is deliberate: the arms then travel through
/// exactly the code an `IF` does, so the rules about what a branch value means
/// -- and the `@` substitution inside an EXCEPT in one of them -- stay in one
/// place.
fn case_as_if_then_else(arms: &[(TlaExpr, TlaExpr)], other: &TlaExpr) -> TlaExpr {
    arms.iter()
        .rev()
        .fold(other.clone(), |acc, (cond, result)| TlaExpr::IfThenElse {
            cond: Box::new(cond.clone()),
            then_expr: Box::new(result.clone()),
            else_expr: Box::new(acc),
        })
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
/// The projection has one rule for turning a tag into a variant name, and it
/// lives in `projection`. Duplicating it here is how `LRecordStatus::PreAccepted`
/// and a call site's `Pre-accepted` came to disagree.
fn variant_name(tag: &str) -> String {
    crate::tla::projection::variant_name_for(tag)
}

/// Replace every free occurrence of `param` with `value`.
/// `subs` with the given names removed -- what a binder that shadows them
/// leaves visible inside its body.
fn without<'a>(
    subs: &BTreeMap<String, TlaExpr>,
    bound: impl IntoIterator<Item = &'a str>,
) -> BTreeMap<String, TlaExpr> {
    let bound: Vec<&str> = bound.into_iter().collect();
    subs.iter()
        .filter(|(k, _)| !bound.contains(&k.as_str()))
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect()
}

/// Expand `LET a == e1  b == e2 IN body` into `body` with the definitions
/// substituted in.
///
/// Sequential *between* definitions and simultaneous *within* each, which is
/// what TLA+ means and is the opposite of the mistake `inline_call` documents.
/// A definition sees the ones before it, so `canStill == IsFastQuorum(succ \cup
/// ..)` has to be built with `succ` already resolved; but the finished map is
/// then applied to the body in one pass, so a definition whose value mentions a
/// *later* definition's name keeps meaning the outer one.
///
/// Two things are refused rather than guessed:
///
///   - a definition whose value mentions a name the body binds, or whose own
///     name the body rebinds. `substitute_all` does not rename binders, so
///     `LET t == x IN \E x \in S : t` would silently capture.
///   - a definition still present after substitution. `substitute_all` does not
///     walk every node -- `Tuple`, `SetFilter`, `FnConstruct` and `LetIn` are
///     missing from it -- and a name it failed to replace would be emitted as a
///     bare identifier referring to nothing. `children` is the complete walk, so
///     comparing against it is exactly the blind spot.
fn expand_let(defs: &[crate::tla::ast::TlaOperator], body: &TlaExpr) -> Result<TlaExpr, String> {
    let mut subs: BTreeMap<String, TlaExpr> = BTreeMap::new();
    let bound = binders_in(body);
    for def in defs {
        if !def.params.is_empty() {
            return Err(format!("LET definition `{}` takes parameters", def.name));
        }
        let value = substitute_all(&def.body, &subs);
        if bound.contains(&def.name) {
            return Err(format!(
                "LET definition `{}` is rebound by a binder in the body",
                def.name
            ));
        }
        for name in idents_in(&value) {
            if bound.contains(&name) {
                return Err(format!(
                    "LET definition `{}` mentions `{name}`, which the body binds",
                    def.name
                ));
            }
        }
        subs.insert(def.name.clone(), value);
    }
    let expanded = substitute_all(body, &subs);
    let residue = idents_in(&expanded);
    if let Some(name) = subs.keys().find(|n| residue.contains(*n)) {
        return Err(format!(
            "LET definition `{name}` is used where the projection cannot \
             substitute it"
        ));
    }
    Ok(expanded)
}

/// Every identifier an expression mentions, bound or free.
fn idents_in(expr: &TlaExpr) -> std::collections::BTreeSet<String> {
    let mut out = std::collections::BTreeSet::new();
    fn walk(e: &TlaExpr, out: &mut std::collections::BTreeSet<String>) {
        if let TlaExpr::Ident(n) = e {
            out.insert(n.clone());
        }
        for child in children(e) {
            walk(child, out);
        }
    }
    walk(expr, &mut out);
    out
}

/// Every name a binder introduces anywhere in an expression.
fn binders_in(expr: &TlaExpr) -> std::collections::BTreeSet<String> {
    let mut out = std::collections::BTreeSet::new();
    fn walk(e: &TlaExpr, out: &mut std::collections::BTreeSet<String>) {
        match e {
            TlaExpr::Forall { vars, .. } | TlaExpr::Exists { vars, .. } => {
                out.extend(vars.iter().map(|v| v.var.clone()));
            }
            TlaExpr::Choose { var, .. }
            | TlaExpr::SetMap { var, .. }
            | TlaExpr::SetFilter { var, .. }
            | TlaExpr::FnConstruct { var, .. } => {
                out.insert(var.clone());
            }
            TlaExpr::LetIn { defs, .. } => out.extend(defs.iter().map(|d| d.name.clone())),
            // The other two binding forms. `expand_let` refuses a definition
            // whose value mentions a name the body binds, because
            // `substitute_all` does not rename binders -- so a binder this
            // misses is a capture the guard waves through. Named explicitly
            // rather than left to the catch-all below for the reason the whole
            // walker audit exists.
            TlaExpr::SetMapMulti { bindings, .. } => {
                out.extend(bindings.iter().map(|b| b.var.clone()))
            }
            TlaExpr::Lambda { params, .. } => out.extend(params.iter().cloned()),
            TlaExpr::Ident(_)
            | TlaExpr::Number(_)
            | TlaExpr::String(_)
            | TlaExpr::Bool(_)
            | TlaExpr::Prime(_)
            | TlaExpr::BinOp { .. }
            | TlaExpr::UnaryOp { .. }
            | TlaExpr::OpApply { .. }
            | TlaExpr::FnApply { .. }
            | TlaExpr::SetEnum(_)
            | TlaExpr::Tuple(_)
            | TlaExpr::Unchanged(_)
            | TlaExpr::Record(_)
            | TlaExpr::RecordSet(_)
            | TlaExpr::RecordAccess { .. }
            | TlaExpr::FnSet { .. }
            | TlaExpr::FnExcept { .. }
            | TlaExpr::IfThenElse { .. }
            | TlaExpr::Case { .. }
            | TlaExpr::Enabled(_)
            | TlaExpr::Always(_)
            | TlaExpr::Eventually(_)
            | TlaExpr::LeadsTo { .. }
            | TlaExpr::WeakFairness { .. }
            | TlaExpr::StrongFairness { .. } => {}
        }
        for child in children(e) {
            walk(child, out);
        }
    }
    walk(expr, &mut out);
    out
}

/// Substitution, exposed so a test can ask whether it reaches a given position.
///
/// `tests/ast_walker_guard.rs` puts a marker in each structural position and
/// requires it to be gone: naming a variant in the walker is not the same as
/// descending into all of its fields, and the difference was live.
pub fn substitute_for_test(expr: &TlaExpr, param: &str, value: &TlaExpr) -> TlaExpr {
    substitute(expr, param, value)
}

/// Substitute one identifier. A thin wrapper over the simultaneous form --
/// see `inline_call` for why substitution must not be applied in sequence.
fn substitute(expr: &TlaExpr, param: &str, value: &TlaExpr) -> TlaExpr {
    substitute_all(
        expr,
        &[(param.to_string(), value.clone())].into_iter().collect(),
    )
}

fn substitute_all(expr: &TlaExpr, subs: &BTreeMap<String, TlaExpr>) -> TlaExpr {
    match expr {
        TlaExpr::Ident(name) if subs.contains_key(name) => subs[name].clone(),
        TlaExpr::BinOp { op, left, right } => TlaExpr::BinOp {
            op: *op,
            left: Box::new(substitute_all(left, subs)),
            right: Box::new(substitute_all(right, subs)),
        },
        TlaExpr::UnaryOp { op, operand } => TlaExpr::UnaryOp {
            op: *op,
            operand: Box::new(substitute_all(operand, subs)),
        },
        TlaExpr::OpApply { op, args } => TlaExpr::OpApply {
            op: Box::new(substitute_all(op, subs)),
            args: args.iter().map(|a| substitute_all(a, subs)).collect(),
        },
        TlaExpr::FnApply { func, arg } => TlaExpr::FnApply {
            func: Box::new(substitute_all(func, subs)),
            arg: Box::new(substitute_all(arg, subs)),
        },
        TlaExpr::Record(fields) => TlaExpr::Record(
            fields
                .iter()
                .map(|(n, v)| (n.clone(), substitute_all(v, subs)))
                .collect(),
        ),
        TlaExpr::SetEnum(items) => {
            TlaExpr::SetEnum(items.iter().map(|i| substitute_all(i, subs)).collect())
        }
        TlaExpr::SetMap { expr, var, set } => TlaExpr::SetMap {
            expr: Box::new(substitute_all(expr, &without(subs, [var.as_str()]))),
            var: var.clone(),
            set: Box::new(substitute_all(set, subs)),
        },
        TlaExpr::RecordAccess { record, field } => TlaExpr::RecordAccess {
            record: Box::new(substitute_all(record, subs)),
            field: field.clone(),
        },
        TlaExpr::IfThenElse {
            cond,
            then_expr,
            else_expr,
        } => TlaExpr::IfThenElse {
            cond: Box::new(substitute_all(cond, subs)),
            then_expr: Box::new(substitute_all(then_expr, subs)),
            else_expr: Box::new(substitute_all(else_expr, subs)),
        },
        // `CASE` binds nothing, so its arms substitute like any other
        // expression. Leaving it to the catch-all clone below meant a parameter
        // mentioned only inside a `CASE` survived `inline_call` unsubstituted --
        // the same failure mode as the capture bug this function was written
        // for, and one that produces wrong output rather than a gap.
        TlaExpr::Case { arms, other } => TlaExpr::Case {
            arms: arms
                .iter()
                .map(|(cond, result)| (substitute_all(cond, subs), substitute_all(result, subs)))
                .collect(),
            other: other.as_ref().map(|e| Box::new(substitute_all(e, subs))),
        },
        // The nodes below were reaching the catch-all clone, which returns the
        // expression **unchanged** -- so a name inside any of them survived
        // substitution and was emitted referring to whatever it happened to
        // mean at the use site. Found by re-indexing a range binder: `k` inside
        // `{j \in Server : matchIndex[i][j] >= k}` was not rewritten, and the
        // emitted quantifier compared against the wrong value. `inline_call`
        // and `expand_let` go through here too, so the hole was general.
        TlaExpr::Tuple(items) => {
            TlaExpr::Tuple(items.iter().map(|i| substitute_all(i, subs)).collect())
        }
        TlaExpr::Unchanged(items) => {
            TlaExpr::Unchanged(items.iter().map(|i| substitute_all(i, subs)).collect())
        }
        TlaExpr::Prime(inner) => TlaExpr::Prime(Box::new(substitute_all(inner, subs))),
        TlaExpr::Enabled(inner) => TlaExpr::Enabled(Box::new(substitute_all(inner, subs))),
        TlaExpr::RecordSet(fields) => TlaExpr::RecordSet(
            fields
                .iter()
                .map(|(n, v)| (n.clone(), substitute_all(v, subs)))
                .collect(),
        ),
        TlaExpr::FnSet { domain, range } => TlaExpr::FnSet {
            domain: Box::new(substitute_all(domain, subs)),
            range: Box::new(substitute_all(range, subs)),
        },
        // Binding forms: the bound name is hidden inside the body, and only
        // that one -- the domain is outside the binder's own scope.
        TlaExpr::SetFilter { var, set, filter } => TlaExpr::SetFilter {
            var: var.clone(),
            set: Box::new(substitute_all(set, subs)),
            filter: Box::new(substitute_all(filter, &without(subs, [var.as_str()]))),
        },
        TlaExpr::FnConstruct { var, domain, body } => TlaExpr::FnConstruct {
            var: var.clone(),
            domain: Box::new(substitute_all(domain, subs)),
            body: Box::new(substitute_all(body, &without(subs, [var.as_str()]))),
        },
        TlaExpr::SetMapMulti { expr, bindings } => {
            let bound: Vec<&str> = bindings.iter().map(|b| b.var.as_str()).collect();
            TlaExpr::SetMapMulti {
                expr: Box::new(substitute_all(expr, &without(subs, bound.iter().copied()))),
                bindings: bindings
                    .iter()
                    .map(|b| crate::tla::ast::TlaQuantBound {
                        var: b.var.clone(),
                        set: b.set.as_ref().map(|s| substitute_all(s, subs)),
                    })
                    .collect(),
            }
        }
        TlaExpr::Lambda { params, body } => {
            let bound: Vec<&str> = params.iter().map(|p| p.as_str()).collect();
            TlaExpr::Lambda {
                params: params.clone(),
                body: Box::new(substitute_all(body, &without(subs, bound))),
            }
        }
        TlaExpr::LetIn { defs, body } => {
            let bound: Vec<&str> = defs.iter().map(|d| d.name.as_str()).collect();
            let inner = without(subs, bound);
            TlaExpr::LetIn {
                defs: defs
                    .iter()
                    .map(|d| crate::tla::ast::TlaOperator {
                        body: substitute_all(&d.body, &inner),
                        ..d.clone()
                    })
                    .collect(),
                body: Box::new(substitute_all(body, &inner)),
            }
        }
        // Temporal operators. They do not appear in an action body, so nothing
        // has needed these -- but leaving them to the catch-all means the
        // function is *not* total, and "total" is the only property that makes
        // it safe to call from `inline_call` and `expand_let`.
        TlaExpr::Always(inner) => TlaExpr::Always(Box::new(substitute_all(inner, subs))),
        TlaExpr::Eventually(inner) => TlaExpr::Eventually(Box::new(substitute_all(inner, subs))),
        TlaExpr::LeadsTo { left, right } => TlaExpr::LeadsTo {
            left: Box::new(substitute_all(left, subs)),
            right: Box::new(substitute_all(right, subs)),
        },
        TlaExpr::WeakFairness { vars, action } => TlaExpr::WeakFairness {
            vars: Box::new(substitute_all(vars, subs)),
            action: Box::new(substitute_all(action, subs)),
        },
        TlaExpr::StrongFairness { vars, action } => TlaExpr::StrongFairness {
            vars: Box::new(substitute_all(vars, subs)),
            action: Box::new(substitute_all(action, subs)),
        },
        // Quantifiers and CHOOSE bind their own variable, so a binder that
        // shadows a parameter hides *that* parameter -- and only that one --
        // inside the body. The binding sets are outside the binder's scope,
        // so they still see everything. Skipping the whole node left
        // `Max(s)`'s body referring to `s` while its signature said `s_arg`.
        TlaExpr::Forall { vars, body } | TlaExpr::Exists { vars, body } => {
            let inner = without(subs, vars.iter().map(|b| b.var.as_str()));
            let vars = vars
                .iter()
                .map(|b| crate::tla::ast::TlaQuantBound {
                    var: b.var.clone(),
                    set: b.set.as_ref().map(|s| substitute_all(s, subs)),
                })
                .collect();
            let body = Box::new(substitute_all(body, &inner));
            if matches!(expr, TlaExpr::Forall { .. }) {
                TlaExpr::Forall { vars, body }
            } else {
                TlaExpr::Exists { vars, body }
            }
        }
        TlaExpr::Choose { var, set, body } => TlaExpr::Choose {
            var: var.clone(),
            set: set.as_ref().map(|s| Box::new(substitute_all(s, subs))),
            body: Box::new(substitute_all(body, &without(subs, [var.as_str()]))),
        },
        TlaExpr::FnExcept { func, updates } => TlaExpr::FnExcept {
            func: Box::new(substitute_all(func, subs)),
            updates: updates
                .iter()
                .map(|u| crate::tla::ast::TlaExceptUpdate {
                    // The *indices* are expressions too. Cloning the path left
                    // `[x EXCEPT ![k] = ..]`'s `k` at its definition-site name,
                    // meaning whatever that name meant where the result was
                    // emitted -- silent, and it survived the commit written to
                    // eliminate exactly this class, because naming the variant
                    // is not the same as descending into all of it.
                    path: u
                        .path
                        .iter()
                        .map(|step| match step {
                            TlaExceptPath::Index(index) => {
                                TlaExceptPath::Index(substitute_all(index, subs))
                            }
                            TlaExceptPath::Field(name) => TlaExceptPath::Field(name.clone()),
                        })
                        .collect(),
                    value: substitute_all(&u.value, subs),
                })
                .collect(),
        },
        // Leaves, named rather than left to a catch-all. The catch-all is what
        // made this function's holes silent: a node kind nobody had thought
        // about took this arm and came back **unchanged**, which is a wrong
        // answer that looks like a right one. Without it the compiler refuses
        // to build until a new `TlaExpr` variant is decided about, which is a
        // stronger guarantee than any test.
        TlaExpr::Ident(_) | TlaExpr::Number(_) | TlaExpr::String(_) | TlaExpr::Bool(_) => {
            expr.clone()
        }
    }
}

pub(crate) fn render_source(expr: &TlaExpr) -> String {
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
        // The multi-binder comprehension and `LAMBDA` both hold expressions and
        // were reaching the catch-all, so every analysis built on this walk --
        // `mentions_prime`, `reads_state`, the helper-parameter shape tests --
        // looked straight past them.
        TlaExpr::SetMapMulti { expr, bindings } => {
            let mut out = vec![&**expr];
            out.extend(bindings.iter().filter_map(|b| b.set.as_ref()));
            out
        }
        TlaExpr::Lambda { body, .. } => vec![body],
        // Leaves. Listed rather than left to a catch-all so that adding a
        // variant to `TlaExpr` does not silently join them --
        // `walkers_reach_every_sub_expression` fails instead.
        TlaExpr::Ident(_) | TlaExpr::Number(_) | TlaExpr::String(_) | TlaExpr::Bool(_) => {
            Vec::new()
        }
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

    /// A constructor whose parameter is named the same as an identifier an
    /// earlier argument introduces. Substituting one parameter at a time lets
    /// the later one capture it.
    ///
    /// This is the tier4 Jetpack composition reduced: `Send(s, d, e, c)` is
    /// `PreacceptReq`, and the call passes `epoch[c]` for `e` while its own
    /// fourth parameter is called `c`. In sequence the result was
    /// `epoch[cmd]` and `src |-> cmd` -- a message sent from the wrong node,
    /// which would have typechecked.
    #[test]
    fn inlining_substitutes_parameters_simultaneously() {
        const CAPTURE: &str = r#"---- MODULE Test ----
VARIABLES epoch, pending, network
Message == [type: {"req"}, src: Proc, dst: Proc, e: Nat, v: Nat]
TypeOK == /\ epoch \in [Proc -> Nat]
          /\ pending \in [Proc -> Nat]
Send(s, d, e, c) == [type |-> "req", src |-> s, dst |-> d, e |-> e, v |-> c]
Go(c, cmd) == /\ pending[c] = 0
              /\ pending' = [pending EXCEPT ![c] = cmd]
              /\ network' = network \cup {Send(c, c, epoch[c], cmd)}
              /\ UNCHANGED epoch
Recv(self, m) == /\ m.type = "req"
                 /\ epoch' = [epoch EXCEPT ![self] = m.e]
                 /\ network' = network \ {m}
                 /\ UNCHANGED pending
Next == \E self \in Proc :
          \/ \E cmd \in Nat : Go(self, cmd)
          \/ \E m \in network : Recv(self, m)
===="#;

        let projected = actions(CAPTURE);
        let go = action(&projected, "Go");
        assert!(
            go.gaps.is_empty(),
            "capture made the epoch read look like another node's: {:?}",
            go.gaps
        );
        let body = go.conjuncts.join(" ");
        assert!(
            body.contains("s.epoch"),
            "the acting node's own epoch should be read as `s.epoch`: {body}"
        );
        assert!(
            !body.contains("epoch[cmd]") && !body.contains("dst: cmd"),
            "a parameter captured an identifier from an earlier argument: {body}"
        );
    }

    /// `<< e >>` -- a tuple literal with an element in it.
    ///
    /// TLA+ has no product type: `<<a, b>>` *is* the sequence
    /// `[i \in 1..2 |-> ..]`, so a tuple literal projects to `seq![..]`. The
    /// tier4 Jetpack composition's `Init` gives every member the
    /// cluster-forming entry -- `<< B!FirstEntry >>` -- and until this the
    /// whole spec was refused over that one conjunct.
    ///
    /// The element is a record whose `command` field is enum-typed, which is
    /// the other half of the same conjunct: the source spells the variant as a
    /// string, and `&str` does not typecheck against `LEntryCommand`.
    #[test]
    fn projects_a_tuple_literal_as_a_sequence_literal() {
        const TUPLE: &str = r#"---- MODULE Test ----
VARIABLES log, network
Message == [type: {"ping"}, src: Proc, dst: Proc]
Entry == [command: {"append", "initCluster"}, term: Nat]
FirstEntry == [command |-> "initCluster", term |-> 0]
TypeOK == log \in [Proc -> Seq(Entry)]
Init == /\ log = [p \in Proc |-> << FirstEntry >>]
        /\ network = {}
Step(p, m) == /\ m.type = "ping"
              /\ log' = [log EXCEPT ![p] = Append(log[p], FirstEntry)]
              /\ network' = network \ {m}
Next == \E p \in Proc : \E m \in network : Step(p, m)
===="#;
        let module = parse_module(TUPLE).expect("test spec must parse");
        let projected = project(&module).expect("test spec must be clean");
        assert!(
            projected.init_gaps.is_empty(),
            "a tuple literal must project: {:?}",
            projected.init_gaps
        );
        let init = projected.init.join(" ");
        assert!(
            init.contains("seq![LEntry { command: LEntryCommand::InitCluster, term: 0 }]"),
            "a one-element tuple is a one-element Seq, and an enum-typed field \
             takes a variant rather than a string: {init}"
        );
    }

    /// `\E k \in 1 .. Len(log[i])` -- Raft's `AdvanceCommitIndex`. A range has
    /// no projected *value*, so it cannot become a `.contains(k)`; the domain
    /// is a bound on the emitted parameter instead.
    ///
    /// And because the body indexes with the binder, the whole quantifier is
    /// re-indexed onto the sequence's own 0-based domain: `s.log[k]`, with
    /// `k + 1` wherever the source said `k`. Same set of witnesses, stated one
    /// lower -- and the only form Verus can infer a trigger for, since it
    /// refuses a subscript with arithmetic in it. Without this the tier4
    /// Jetpack composition was rejected on exactly this action.
    #[test]
    fn a_range_binder_becomes_a_bound_on_the_parameter() {
        let source = r#"---- MODULE Test ----
VARIABLES log, commitIndex
TypeOK == /\ log \in [Proc -> Seq(Nat)]
          /\ commitIndex \in [Proc -> Nat]
Step(p) == \E k \in 1 .. Len(log[p]) :
             /\ k > commitIndex[p]
             /\ log[p][k] = 0
             /\ commitIndex' = [commitIndex EXCEPT ![p] = k]
Next == \E p \in Proc : Step(p)
===="#;
        let acts = actions(source);
        let body = action(&acts, "Step").conjuncts.join(" ");
        assert!(
            body.contains("0 <= k && k <= (s.log.len() as int) - 1"),
            "the range becomes a bound on the parameter, re-indexed from 0: {body}"
        );
        assert!(
            body.contains("s.log[k]") && !body.contains("s.log[k - 1]"),
            "a subscript with arithmetic in it is what Verus cannot trigger on: {body}"
        );
        assert!(
            body.contains("k + 1 > s.commit_index") && body.contains("s_.commit_index == k + 1"),
            "every other use of the binder moves up by one, or the meaning changes: {body}"
        );
    }

    /// A spec may spell its own node set as a range (`Proc == 1 .. NP`).
    /// `project_node_set` answers such a binder with the node-set constant
    /// today, and has to go on doing so: `as_range` follows the name to its
    /// body, so without the guard the range arm would take the binder over and
    /// change what an already-projecting spec emits.
    #[test]
    fn a_binder_over_a_node_set_written_as_a_range_is_still_the_node_set() {
        let source = r#"---- MODULE Test ----
CONSTANT NP
Proc == 1 .. NP
VARIABLES ok
TypeOK == ok \in [Proc -> BOOLEAN]
Step(p) == /\ \A q \in Proc : ok[p]
           /\ ok' = [ok EXCEPT ![p] = FALSE]
Next == \E p \in Proc : Step(p)
===="#;
        let acts = actions(source);
        assert!(
            action(&acts, "Step")
                .conjuncts
                .iter()
                .any(|c| c.contains("c.proc.contains(q)")),
            "got {:?}",
            action(&acts, "Step").conjuncts
        );
    }

    /// `{j \in S : P(j)}` -- the set inside every counted quorum in the corpus.
    #[test]
    fn a_filtered_set_comprehension_projects_to_filter() {
        let source = r#"---- MODULE Test ----
VARIABLES matchIndex, ok
TypeOK == /\ matchIndex \in [Proc -> [Proc -> Nat]]
          /\ ok \in [Proc -> BOOLEAN]
Step(p) == /\ Cardinality({q \in Proc : matchIndex[p][q] >= 1}) * 2 > Cardinality(Proc)
           /\ ok' = [ok EXCEPT ![p] = TRUE]
           /\ UNCHANGED matchIndex
Next == \E p \in Proc : Step(p)
===="#;
        let acts = actions(source);
        let body = action(&acts, "Step").conjuncts.join(" ");
        assert!(
            body.contains("c.proc.filter(|q: int| s.match_index[q] >= 1)"),
            "the counted set must project: {body}"
        );
    }

    /// `x' = CASE p -> a [] q -> b [] OTHER -> x`, folded into nested `IF`s so
    /// the arms travel the code an `IF` does -- which is where `OTHER -> x`
    /// keeps meaning "leave it alone".
    #[test]
    fn a_case_on_the_right_of_an_update_projects() {
        const CASE_UPDATE: &str = r#"---- MODULE Test ----
VARIABLES x, pc, network
Message == [type: {"val"}, src: Proc, dst: Proc, val: Nat]
TypeOK == /\ x \in [Proc -> Nat]
          /\ pc \in [Proc -> {"a", "b"}]
Recv(self, m) == /\ m.type = "val"
                 /\ x' = CASE m.val = 0 -> [x EXCEPT ![self] = 1]
                           [] m.val = 1 -> [x EXCEPT ![self] = 2]
                           [] OTHER -> x
                 /\ network' = network \ {m}
                 /\ UNCHANGED pc
Next == \E self \in Proc : \E m \in network : Recv(self, m)
===="#;
        let acts = actions(CASE_UPDATE);
        let recv = action(&acts, "Recv");
        assert!(recv.gaps.is_empty(), "CASE must project: {:?}", recv.gaps);
        let body = recv.conjuncts.join(" ");
        assert!(
            body.contains("if val == 0 { 1 } else { if val == 1 { 2 } else { s.x } }"),
            "arms in order, and OTHER leaves the field alone: {body}"
        );
    }

    /// A `CASE` with no `OTHER` has no value when no guard holds, so assigning
    /// one is a gap rather than an invented default.
    #[test]
    fn a_case_without_an_other_arm_is_a_gap() {
        const NO_OTHER: &str = r#"---- MODULE Test ----
VARIABLES x, pc, network
Message == [type: {"val"}, src: Proc, dst: Proc, val: Nat]
TypeOK == /\ x \in [Proc -> Nat]
          /\ pc \in [Proc -> {"a", "b"}]
Recv(self, m) == /\ m.type = "val"
                 /\ x' = CASE m.val = 0 -> [x EXCEPT ![self] = 1]
                           [] m.val = 1 -> [x EXCEPT ![self] = 2]
                 /\ network' = network \ {m}
                 /\ UNCHANGED pc
Next == \E self \in Proc : \E m \in network : Recv(self, m)
===="#;
        let acts = actions(NO_OTHER);
        assert!(
            action(&acts, "Recv")
                .gaps
                .iter()
                .any(|g| g.contains("CASE without an OTHER arm")),
            "got {:?}",
            action(&acts, "Recv").gaps
        );
    }

    /// A message field declared with an inline set of literals is an enum the
    /// source never named. Unnamed it was dropped from the declarations and the
    /// emitter wrote `Resp { res:  }` -- a field with no type at all, and a
    /// guard `res is Ok` naming a variant of nothing. The same defect was found
    /// and fixed for records-in-state; the message path was missed.
    #[test]
    fn an_inline_enum_in_a_message_field_is_named_and_declared() {
        const ENUM_FIELD: &str = r#"---- MODULE Test ----
VARIABLES x, network
Message == [type: {"resp"}, src: Proc, dst: Proc,
            res: {"ok", "stale"}]
TypeOK == x \in [Proc -> Nat]
Init == /\ x = [p \in Proc |-> 0]
        /\ network = {}
Recv(self, m) == /\ m.type = "resp"
                 /\ x' = [x EXCEPT ![self] = IF m.res = "ok" THEN 1 ELSE 0]
                 /\ network' = network \ {m}
Next == \E self \in Proc : \E m \in network : Recv(self, m)
===="#;
        let module = parse_module(ENUM_FIELD).expect("test spec must parse");
        let spec = project_module(&module).expect("test spec must be clean");
        let res_ty = spec
            .messages
            .iter()
            .flat_map(|v| v.fields.iter())
            .find(|(f, _)| f == "res")
            .map(|(_, t)| t.render())
            .expect("the message has a `res` field");
        assert!(
            !res_ty.is_empty(),
            "an unnamed enum renders as the empty string, which emits `res: `"
        );
        assert!(
            spec.enums.iter().any(|(n, _)| *n == res_ty),
            "the enum must also be declared, not just named: {res_ty} not in {:?}",
            spec.enums.iter().map(|(n, _)| n).collect::<Vec<_>>()
        );
    }

    /// A message tag set named by an operator rather than written inline.
    ///
    /// The tag literals were harvested only from a literal `SetEnum`, so every
    /// variant behind a name was dropped -- and with one declaration of several
    /// written that way the loss is **silent end to end**: the message kind
    /// disappears from `LMessage`, its receive handler becomes unreachable from
    /// the dispatch, `clean-tla` exits 0 with no gap, and Verus reports
    /// `0 verified, 0 errors`. A protocol message vanishes and every check
    /// still passes.
    #[test]
    fn a_tag_set_named_by_an_operator_still_yields_its_variants() {
        const MIXED: &str = r#"---- MODULE Test ----
VARIABLES x, msgs
BTags == {"b"}
Message == [type: {"a"}, src: Proc, dst: Proc]
  \cup [type: BTags, src: Proc, dst: Proc]
TypeOK == x \in [Proc -> Nat]
Init == x = [p \in Proc |-> 0] /\ msgs = {}
Send(self) == /\ msgs' = msgs \cup {[type |-> "a", src |-> self, dst |-> self]}
              /\ x' = [x EXCEPT ![self] = 1]
RecvA(self, m) == /\ m.dst = self /\ m.type = "a"
                  /\ x' = [x EXCEPT ![self] = 2]
                  /\ msgs' = msgs \ {m}
RecvB(self, m) == /\ m.dst = self /\ m.type = "b"
                  /\ x' = [x EXCEPT ![self] = 3]
                  /\ msgs' = msgs \ {m}
Next == \E self \in Proc : Send(self) \/ \E m \in msgs : RecvA(self, m) \/ RecvB(self, m)
===="#;
        let module = parse_module(MIXED).expect("fixture must parse");
        let spec = project_module(&module).expect("fixture must be clean");
        let tags: Vec<&str> = spec.messages.iter().map(|m| m.tag.as_str()).collect();
        assert!(
            tags.contains(&"a") && tags.contains(&"b"),
            "a tag set behind a name must still produce its variants, or the \
             message kind disappears from the spec: {tags:?}"
        );
    }

    /// `[log EXCEPT ![i][k] = v]` on a **sequence**-typed per-node field.
    ///
    /// Two independent wrongs on one emitted line, and Verus accepted both
    /// because they are `Seq` operations of the right type: the update wrote at
    /// `k` while the guard read `s.log[k - 1]`, and it used `insert`, which in
    /// vstd is `subrange(0,i).push(a).add(subrange(i, len))` -- it *grows* the
    /// sequence and shifts the tail, where TLA+'s EXCEPT replaces.
    #[test]
    fn an_indexed_update_of_a_sequence_replaces_at_the_adjusted_index() {
        const SEQ: &str = r#"---- MODULE Test ----
EXTENDS Integers, Sequences
VARIABLES log
TypeOK == log \in [Proc -> Seq(Nat)]
Init == log = [p \in Proc |-> << 0 >>]
Step(p, k) == /\ log[p][k] = 0
              /\ log' = [log EXCEPT ![p][k] = 1]
Next == \E p \in Proc : \E k \in 1 .. 1 : Step(p, k)
===="#;
        let acts = actions(SEQ);
        let body = action(&acts, "Step").conjuncts.join(" ");
        assert!(
            body.contains("s.log.update(k - 1, 1)"),
            "a sequence is replaced at the 0-based index, not grown at the \
             1-based one: {body}"
        );
        assert!(
            !body.contains("s.log.insert("),
            "`Seq::insert` shifts the tail; EXCEPT replaces: {body}"
        );
        assert!(
            body.contains("s.log[k - 1]"),
            "and the read the write must agree with: {body}"
        );
    }

    /// The same shape on a **map**-typed field keeps `insert` and the key
    /// untouched -- a map is updated by key, and a key is not an offset.
    #[test]
    fn an_indexed_update_of_a_map_still_inserts_by_key() {
        const MAP: &str = r#"---- MODULE Test ----
VARIABLES tbl
TypeOK == tbl \in [Proc -> [Proc -> Nat]]
Init == tbl = [p \in Proc |-> [q \in Proc |-> 0]]
Step(p, q) == tbl' = [tbl EXCEPT ![p][q] = 1]
Next == \E p \in Proc : \E q \in Proc : Step(p, q)
===="#;
        let acts = actions(MAP);
        let body = action(&acts, "Step").conjuncts.join(" ");
        assert!(
            body.contains("s.tbl.insert(q, 1)"),
            "a map takes its key as written: {body}"
        );
    }

    /// A `CASE` inside an EXCEPT's *value* rather than at the top of the
    /// update: `mark' = [mark EXCEPT ![self] = CASE big -> "hi" [] OTHER ->
    /// "lo"]`.
    ///
    /// `project_update` folded the outer form and `project_expr` had no `Case`
    /// arm at all, so whether the shape projected depended only on where the
    /// CASE was written. Folding it in `project_expr` alone was not enough --
    /// that path has no target type, and an enum-typed field came out compared
    /// against `&str`, which Verus rejects.
    #[test]
    fn a_case_inside_an_except_value_projects_with_the_fields_type() {
        const CASE_VALUE: &str = r#"---- MODULE Test ----
EXTENDS Integers
VARIABLES mark, ctr
TypeOK == /\ mark \in [Proc -> {"lo", "hi"}]
          /\ ctr \in [Proc -> Nat]
Step(p) == /\ mark' = [mark EXCEPT ![p] = CASE ctr[p] > 1 -> "hi" [] OTHER -> "lo"]
           /\ UNCHANGED ctr
Next == \E p \in Proc : Step(p)
===="#;
        let acts = actions(CASE_VALUE);
        let step = action(&acts, "Step");
        assert!(step.gaps.is_empty(), "must project: {:?}", step.gaps);
        let body = step.conjuncts.join(" ");
        assert!(
            body.contains("if s.ctr > 1 { LMark::Hi } else { LMark::Lo }"),
            "the branches are variants of the field's own enum, not strings: \
             {body}"
        );
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
        // `Nat` is not a set the projection knows anything about, so the
        // quantifier domain cannot be projected. It used to be `CHOOSE` that
        // made this test's spec unprojectable; `CHOOSE` now translates, and an
        // unknown domain is the thing still worth refusing -- an unresolved
        // identifier would otherwise project to itself and emit
        // `Nat.contains(v)` against a `Nat` that does not exist.
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
