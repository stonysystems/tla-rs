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
use crate::tla::projection::{to_snake_case, ProjectedSpec, ProjectionError};

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
        texts.extend(action.conjuncts.iter());
        texts.extend(action.frame.iter());
    }
    spec.constants.retain(|(name, _)| {
        name == "node_id" || texts.iter().any(|t| references_constant(t, name))
    });

    Ok(ProjectedModule {
        spec,
        helpers,
        actions,
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
    let node_params = node_parameterized_operators(module);
    let mut helpers = Vec::new();

    for (op_name, node_param) in &node_params {
        if !called.contains(op_name.as_str()) {
            continue;
        }
        let Some(op) = module.operators.iter().find(|o| o.name == *op_name) else {
            continue;
        };
        // Actions are handled by `project_actions`; helpers are the rest.
        if mentions_prime(&op.body) {
            continue;
        }
        let ctx = ActionContext {
            spec,
            node_param: node_param.clone(),
            msg_param: None,
            network: spec.network_variable.clone(),
        };
        let (body, gaps) = match ctx.project_expr(&op.body) {
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
                .map(|p| format!("{}: int", to_snake_case(&p.name)))
                .collect(),
            body,
            gaps,
        });
    }

    helpers.sort_by(|a, b| a.source_name.cmp(&b.source_name));
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
        let ctx = ActionContext {
            spec,
            node_param: node_param.clone(),
            msg_param: msg_param.clone(),
            network: spec.network_variable.clone(),
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
            let mut params = vec!["src: int".to_string()];
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
            Vec::new()
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
            conjuncts,
            frame,
            handles_tag,
            gaps,
        });
    }

    actions.sort_by(|a, b| a.source_name.cmp(&b.source_name));
    actions
}

struct ActionContext<'a> {
    spec: &'a ProjectedSpec,
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
                    updated.push(field.to_string());
                    return Ok(format!(
                        "s_.{field} == {}",
                        self.project_update(var, right)?
                    ));
                }
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
        match field.as_str() {
            "dst" if matches!(&**right, TlaExpr::Ident(n) if *n == self.node_param) => {
                Some(String::new())
            }
            "type" | "kind" | "tag" => match &**right {
                TlaExpr::String(tag) => Some(tag.clone()),
                _ => None,
            },
            _ => None,
        }
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
                "dst" => dst = Some(self.project_expr(value)?),
                "type" | "kind" | "tag" => match value {
                    TlaExpr::String(t) => tag = Some(t.clone()),
                    other => {
                        return Err(format!(
                            "message tag {} is not a literal",
                            render_source(other)
                        ))
                    }
                },
                // `src` is the sender: after projection that is this node, and
                // the framework stamps it on the packet.
                "src" | "source" | "sender" => {}
                // A field a constructor fills with a literal carries no
                // information -- it is there because every message shares one
                // record type. The enum declaration drops it too.
                _ if is_literal(value) => {}
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
                .find(|(_, ty)| matches!(ty, crate::tla::projection::ProjectedType::Set(_)))
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
                "dst" => dst = Some(projected(value)?),
                "type" | "kind" | "tag" => match value {
                    TlaExpr::String(t) => tag = Some(t.clone()),
                    other => {
                        return Err(format!(
                            "message tag {} is not a literal",
                            render_source(other)
                        ))
                    }
                },
                "src" | "source" | "sender" => {}
                _ if is_literal(value) => {}
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
            other => self.project_expr(other),
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
                                return Ok(format!("s.{field}[{}]", self.project_expr(arg)?));
                            }
                        }
                    }
                }
                Err(format!("application {}", render_source(expr)))
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
                    Ok(to_snake_case(field))
                } else {
                    Err(format!("record access {}", render_source(expr)))
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
            TlaExpr::BinOp { op, left, right } => {
                let l = self.project_expr(left)?;
                let r = self.project_expr(right)?;
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
            TlaExpr::SetEnum(items) if items.is_empty() => Ok("Set::empty()".to_string()),
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

/// Whether an expression is a literal, and so carries no information when a
/// constructor uses it to fill a shared record field.
fn is_literal(expr: &TlaExpr) -> bool {
    matches!(
        expr,
        TlaExpr::Number(_) | TlaExpr::String(_) | TlaExpr::Bool(_)
    )
}

/// `"req"` -> `Req`.
fn variant_name(tag: &str) -> String {
    let mut chars = tag.chars();
    match chars.next() {
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
fn children(expr: &TlaExpr) -> Vec<&TlaExpr> {
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
            a.conjuncts.contains(&"s.pc == \"a\"".to_string()),
            "guard should read this node's pc: {:?}",
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
}
