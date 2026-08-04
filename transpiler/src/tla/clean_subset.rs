//! Clean-subset TLA+ linter (Phase 52.M0).
//!
//! The "clean subset" is the input contract of the clean-TLA+ → single-process
//! Verus translator (Phase 52). A global multi-server TLA+ spec can only be
//! *mechanically* projected onto a single-process `LInit`/`LNext` spec when the
//! human has already done the non-automatable part: message-ification of every
//! cross-node read. This module makes that boundary executable — it accepts
//! specs that are projectable and rejects the rest with precise, actionable
//! errors.
//!
//! The five contract rules (full prose: `docs/clean_tla_subset_spec.md`):
//!
//! * **C1** every `VARIABLE` is either per-node (`[Node -> T]`) or the network.
//! * **C2** an action reads only its own node's state (`x[self]`), its
//!   parameters, and the received message.
//! * **C3** no history variables (write-only ghost state, cross-node aggregation).
//! * **C4** exactly one variable is the network, touched only by whitelisted
//!   send/receive/discard shapes, and messages carry `src`/`dst`.
//! * **C5** `Next` is a disjunction of `\E self \in Node : Action(self, ...)`
//!   (plus environment actions that touch only the network).
//!
//! The linter is deliberately syntactic: it reports what it can prove from the
//! AST and stays silent otherwise, so a clean report means "projectable by the
//! Phase 52 passes", not "semantically correct".

use std::collections::{BTreeMap, BTreeSet};

use crate::tla::ast::{
    TlaBinOp, TlaExceptPath, TlaExpr, TlaModule, TlaOperator, TlaQuantBound, TlaUnaryOp,
};

/// Severity of a clean-subset diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CleanSeverity {
    /// The spec is not projectable; the translator must refuse it.
    Error,
    /// Projectable, but the translator will have to guess or the rewrite is
    /// probably not what the author intended.
    Warning,
}

impl CleanSeverity {
    pub fn as_str(self) -> &'static str {
        match self {
            CleanSeverity::Error => "error",
            CleanSeverity::Warning => "warning",
        }
    }
}

/// A single clean-subset contract violation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CleanViolation {
    /// Stable diagnostic code, e.g. `CS003`.
    pub code: &'static str,
    /// Contract rule this code belongs to, e.g. `C2`.
    pub rule: &'static str,
    pub severity: CleanSeverity,
    /// Operator the violation was found in, when known.
    pub operator: Option<String>,
    /// 1-based source line of the enclosing operator, when known.
    pub line: Option<usize>,
    pub message: String,
    /// What the human has to do to make the spec clean.
    pub hint: String,
}

impl CleanViolation {
    fn render(&self) -> String {
        let loc = match (self.line, &self.operator) {
            (Some(l), Some(op)) => format!("line {l} ({op})"),
            (Some(l), None) => format!("line {l}"),
            (None, Some(op)) => format!("({op})"),
            (None, None) => "<module>".to_string(),
        };
        format!(
            "  {loc}: [{}/{}] {}\n      hint: {}",
            self.code, self.rule, self.message, self.hint
        )
    }
}

/// Tunables for specs that do not use the conventional names.
#[derive(Debug, Clone)]
pub struct CleanSubsetConfig {
    /// Force the node/server set constant instead of inferring it.
    pub node_set: Option<String>,
    /// Force the network variable instead of inferring it.
    pub network_var: Option<String>,
    /// Names accepted as the node set when inference falls back to naming.
    pub node_set_candidates: Vec<String>,
    /// Names accepted as the network variable.
    pub network_var_candidates: Vec<String>,
    /// Operators allowed to manipulate the network variable.
    pub network_operators: Vec<String>,
    /// Record fields accepted as the message source.
    pub src_field_aliases: Vec<String>,
    /// Record fields accepted as the message destination.
    pub dst_field_aliases: Vec<String>,
    /// Name of the initial-state operator (exempt from the action rules).
    pub init_operator: String,
    /// Name of the next-state operator.
    pub next_operator: String,
}

impl Default for CleanSubsetConfig {
    fn default() -> Self {
        Self {
            node_set: None,
            network_var: None,
            node_set_candidates: strs(&[
                "Node",
                "Nodes",
                "Server",
                "Servers",
                "Replica",
                "Replicas",
                "Acceptor",
                "Acceptors",
                "Process",
                "Processes",
                "Proc",
                "Participant",
                "RM",
            ]),
            network_var_candidates: strs(&[
                "messages", "msgs", "msg", "sentMsg", "sentMsgs", "sent", "network", "net",
                "msgQueue", "Messages", "packets",
            ]),
            network_operators: strs(&[
                "Send",
                "SendMsg",
                "Sends",
                "Reply",
                "Discard",
                "Broadcast",
                "Receive",
                "WithMessage",
                "WithoutMessage",
            ]),
            src_field_aliases: strs(&["src", "source", "msource", "from", "sender", "msrc"]),
            dst_field_aliases: strs(&["dst", "dest", "mdest", "to", "receiver", "mdst", "target"]),
            init_operator: "Init".to_string(),
            next_operator: "Next".to_string(),
        }
    }
}

fn strs(v: &[&str]) -> Vec<String> {
    v.iter().map(|s| (*s).to_string()).collect()
}

/// How a declared variable was classified by C1.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarKind {
    /// `[Node -> T]`: one copy per node, projectable to a single `s.field`.
    PerNode,
    /// The designated network variable; erased by the P3 pass.
    Network,
    /// Neither — not projectable.
    Unclassified,
}

/// Result of linting one module.
#[derive(Debug, Clone)]
pub struct CleanReport {
    pub module: String,
    /// Node set constant, if it could be determined.
    pub node_set: Option<String>,
    /// Network variable, if it could be determined.
    pub network_var: Option<String>,
    /// Every declared variable with its C1 classification.
    pub var_kinds: BTreeMap<String, VarKind>,
    /// Operators treated as actions (reachable from `Next`, or containing `'`).
    pub actions: BTreeSet<String>,
    pub violations: Vec<CleanViolation>,
}

impl CleanReport {
    /// A module is clean when it has no error-severity violations.
    pub fn is_clean(&self) -> bool {
        !self
            .violations
            .iter()
            .any(|v| v.severity == CleanSeverity::Error)
    }

    pub fn errors(&self) -> impl Iterator<Item = &CleanViolation> {
        self.violations
            .iter()
            .filter(|v| v.severity == CleanSeverity::Error)
    }

    pub fn warnings(&self) -> impl Iterator<Item = &CleanViolation> {
        self.violations
            .iter()
            .filter(|v| v.severity == CleanSeverity::Warning)
    }

    /// Number of errors — the "clean distance" used to grade corpus candidates.
    pub fn clean_distance(&self) -> usize {
        self.errors().count()
    }

    /// Human-readable report.
    pub fn render(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("clean-subset lint: MODULE {}\n", self.module));
        out.push_str(&format!(
            "  node set    : {}\n",
            self.node_set.as_deref().unwrap_or("<unknown>")
        ));
        out.push_str(&format!(
            "  network var : {}\n",
            self.network_var.as_deref().unwrap_or("<unknown>")
        ));
        let per_node: Vec<&str> = self
            .var_kinds
            .iter()
            .filter(|(_, k)| **k == VarKind::PerNode)
            .map(|(n, _)| n.as_str())
            .collect();
        out.push_str(&format!("  per-node    : {}\n", per_node.join(", ")));
        out.push_str(&format!(
            "  actions     : {}\n",
            self.actions.iter().cloned().collect::<Vec<_>>().join(", ")
        ));

        let errors: Vec<&CleanViolation> = self.errors().collect();
        let warnings: Vec<&CleanViolation> = self.warnings().collect();
        if !errors.is_empty() {
            out.push_str(&format!("\nERRORS ({}):\n", errors.len()));
            for v in errors {
                out.push_str(&v.render());
                out.push('\n');
            }
        }
        if !warnings.is_empty() {
            out.push_str(&format!("\nWARNINGS ({}):\n", warnings.len()));
            for v in warnings {
                out.push_str(&v.render());
                out.push('\n');
            }
        }
        if self.is_clean() {
            out.push_str("\nRESULT: clean (projectable by the Phase 52 passes)\n");
        } else {
            out.push_str(&format!(
                "\nRESULT: not clean — clean distance {}\n",
                self.clean_distance()
            ));
        }
        out
    }
}

/// Lint a parsed module against the clean subset with default settings.
pub fn lint_module(module: &TlaModule) -> CleanReport {
    lint_module_with_config(module, &CleanSubsetConfig::default())
}

/// Lint a parsed module against the clean subset.
pub fn lint_module_with_config(module: &TlaModule, config: &CleanSubsetConfig) -> CleanReport {
    Linter::new(module, config).run()
}

// ---------------------------------------------------------------------------
// Linter
// ---------------------------------------------------------------------------

struct Linter<'a> {
    module: &'a TlaModule,
    config: &'a CleanSubsetConfig,
    ops: BTreeMap<String, &'a TlaOperator>,
    vars: BTreeSet<String>,
    node_set: Option<String>,
    network_var: Option<String>,
    per_node: BTreeSet<String>,
    actions: BTreeSet<String>,
    /// Node parameter of each action, as fixed by its `Next` call site.
    action_self: BTreeMap<String, String>,
    violations: Vec<CleanViolation>,
}

/// Per-operator walk context.
#[derive(Debug, Clone, Default)]
struct Ctx {
    operator: String,
    line: Option<usize>,
    /// Symbols that are known to denote nodes (params + node-set-bound vars).
    node_syms: BTreeSet<String>,
    /// The symbol that must be used to index per-node state, when known.
    self_sym: Option<String>,
    /// Message-typed symbols bound by `\E m \in messages`.
    msg_syms: BTreeSet<String>,
}

impl<'a> Linter<'a> {
    fn new(module: &'a TlaModule, config: &'a CleanSubsetConfig) -> Self {
        let ops = module
            .operators
            .iter()
            .map(|op| (op.name.clone(), op))
            .collect();
        Self {
            module,
            config,
            ops,
            vars: module.variables.iter().cloned().collect(),
            node_set: None,
            network_var: None,
            per_node: BTreeSet::new(),
            actions: BTreeSet::new(),
            action_self: BTreeMap::new(),
            violations: Vec::new(),
        }
    }

    fn run(mut self) -> CleanReport {
        self.resolve_node_set();
        self.classify_per_node();
        self.resolve_network_var();
        self.collect_actions();

        self.check_c1_variable_classification();
        self.check_c5_next_shape();
        self.check_actions();
        self.check_c3_history_vars();
        self.check_c4_network_usage();

        let mut var_kinds = BTreeMap::new();
        for v in &self.vars {
            let kind = if Some(v) == self.network_var.as_ref() {
                VarKind::Network
            } else if self.per_node.contains(v) {
                VarKind::PerNode
            } else {
                VarKind::Unclassified
            };
            var_kinds.insert(v.clone(), kind);
        }

        self.violations.sort_by(|a, b| {
            a.severity
                .cmp(&b.severity)
                .then(a.line.cmp(&b.line))
                .then(a.code.cmp(b.code))
        });

        CleanReport {
            module: self.module.name.clone(),
            node_set: self.node_set,
            network_var: self.network_var,
            var_kinds,
            actions: self.actions,
            violations: self.violations,
        }
    }

    // -- setup ------------------------------------------------------------

    fn resolve_node_set(&mut self) {
        if let Some(explicit) = &self.config.node_set {
            self.node_set = Some(explicit.clone());
            return;
        }
        // 1. A CONSTANT with a conventional name.
        for c in &self.module.constants {
            if self.config.node_set_candidates.contains(&c.name) {
                self.node_set = Some(c.name.clone());
                return;
            }
        }
        // 2. The most frequent bounding set of the `Next` existentials.
        if let Some(next) = self.ops.get(&self.config.next_operator) {
            let mut counts: BTreeMap<String, usize> = BTreeMap::new();
            collect_exists_bounds(&next.body, &mut counts);
            if let Some((name, _)) = counts.iter().max_by_key(|(_, n)| **n) {
                if self.module.constants.iter().any(|c| &c.name == name) {
                    self.node_set = Some(name.clone());
                    return;
                }
            }
        }
        // 3. The domain of an `Init` per-node function construction.
        if let Some(init) = self.ops.get(&self.config.init_operator) {
            let mut domains: BTreeMap<String, usize> = BTreeMap::new();
            collect_fn_construct_domains(&init.body, &mut domains);
            if let Some((name, _)) = domains.iter().max_by_key(|(_, n)| **n) {
                self.node_set = Some(name.clone());
                return;
            }
        }
        self.push(
            "CS018",
            "C1",
            CleanSeverity::Error,
            None,
            None,
            "cannot determine the node set: no CONSTANT with a conventional name, no \
             `\\E self \\in S` in Next, no per-node function construction in Init"
                .to_string(),
            "declare the node set as a CONSTANT (Node/Server/...) or pass --node-set".to_string(),
        );
    }

    /// A variable is per-node when it is indexed, EXCEPT-updated at an index,
    /// initialised as `[i \in NodeSet |-> ...]`, or typed `\in [NodeSet -> T]`.
    fn classify_per_node(&mut self) {
        let mut indexed = BTreeSet::new();
        for op in &self.module.operators {
            collect_indexed_vars(&op.body, &self.vars, &mut indexed);
        }
        for v in indexed {
            self.per_node.insert(v);
        }
        if let Some(node_set) = self.node_set.clone() {
            for op in &self.module.operators {
                let mut typed = BTreeSet::new();
                collect_node_typed_vars(&op.body, &self.vars, &node_set, &mut typed);
                for v in typed {
                    self.per_node.insert(v);
                }
            }
        }
    }

    fn resolve_network_var(&mut self) {
        if let Some(explicit) = &self.config.network_var {
            self.network_var = Some(explicit.clone());
            self.per_node.remove(explicit);
            return;
        }
        let named: Vec<String> = self
            .vars
            .iter()
            .filter(|v| self.config.network_var_candidates.contains(v))
            .cloned()
            .collect();
        match named.len() {
            1 => {
                let v = named[0].clone();
                self.per_node.remove(&v);
                self.network_var = Some(v);
                return;
            }
            0 => {}
            n => {
                self.push(
                    "CS008",
                    "C4",
                    CleanSeverity::Error,
                    None,
                    None,
                    format!(
                        "{n} variables look like the network ({}); the clean subset requires \
                         exactly one",
                        named.join(", ")
                    ),
                    "merge them into a single message set, or designate one with --network-var"
                        .to_string(),
                );
                let v = named[0].clone();
                self.per_node.remove(&v);
                self.network_var = Some(v);
                return;
            }
        }
        // Fall back to shape: a non-indexed variable accumulated with `\cup`.
        let candidates: Vec<String> = self
            .vars
            .iter()
            .filter(|v| !self.per_node.contains(*v))
            .filter(|v| {
                self.module
                    .operators
                    .iter()
                    .any(|op| is_set_accumulated(&op.body, v))
            })
            .cloned()
            .collect();
        if candidates.len() == 1 {
            self.network_var = Some(candidates[0].clone());
            self.push(
                "CS019",
                "C4",
                CleanSeverity::Warning,
                None,
                None,
                format!(
                    "network variable inferred from shape as `{}` (no conventional name)",
                    candidates[0]
                ),
                "rename it to `messages`/`msgs` or pass --network-var to make the choice explicit"
                    .to_string(),
            );
            return;
        }
        self.push(
            "CS007",
            "C4",
            CleanSeverity::Error,
            None,
            None,
            "no network variable found: the clean subset requires exactly one variable that \
             carries the messages"
                .to_string(),
            "message-ify the cross-node communication into a `messages` variable, or pass \
             --network-var"
                .to_string(),
        );
    }

    fn collect_actions(&mut self) {
        // Any operator that mentions `'` is an action, except Init.
        for op in &self.module.operators {
            if op.name == self.config.init_operator {
                continue;
            }
            if contains_prime(&op.body) {
                self.actions.insert(op.name.clone());
            }
        }
        self.actions.remove(&self.config.next_operator);

        // Node parameter of each action, from its `Next` call site.
        if let Some(next) = self.ops.get(&self.config.next_operator) {
            let mut sites = Vec::new();
            collect_action_call_sites(&next.body, &BTreeSet::new(), &mut sites);
            for (name, self_arg) in sites {
                if let Some(sym) = self_arg {
                    self.action_self.insert(name, sym);
                }
            }
        }
    }

    // -- C1 ---------------------------------------------------------------

    fn check_c1_variable_classification(&mut self) {
        let vars: Vec<String> = self.vars.iter().cloned().collect();
        for v in vars {
            if Some(&v) == self.network_var.as_ref() || self.per_node.contains(&v) {
                continue;
            }
            self.push(
                "CS001",
                "C1",
                CleanSeverity::Error,
                None,
                None,
                format!(
                    "variable `{v}` is neither per-node (`[{} -> T]`) nor the network",
                    self.node_set.as_deref().unwrap_or("Node")
                ),
                format!(
                    "give `{v}` a per-node type `[{} -> T]`, fold it into a per-node field, or \
                     drop it if it is global bookkeeping",
                    self.node_set.as_deref().unwrap_or("Node")
                ),
            );
        }
    }

    // -- C5 ---------------------------------------------------------------

    fn check_c5_next_shape(&mut self) {
        let Some(next) = self.ops.get(&self.config.next_operator).copied() else {
            self.push(
                "CS011",
                "C5",
                CleanSeverity::Error,
                None,
                None,
                format!("no `{}` operator", self.config.next_operator),
                "the clean subset needs a next-state relation to project".to_string(),
            );
            return;
        };
        if !self.ops.contains_key(&self.config.init_operator) {
            self.push(
                "CS014",
                "C5",
                CleanSeverity::Error,
                None,
                None,
                format!("no `{}` operator", self.config.init_operator),
                "the translator projects Init into `LInit`; add one".to_string(),
            );
        }
        let line = next.span.map(|s| s.start.line);
        let node_set = self.node_set.clone();
        for disjunct in flatten_or(&next.body) {
            // A protocol step must name the node it runs on.
            if let TlaExpr::Exists { vars, .. } = disjunct {
                let bound_ok = vars.iter().any(|b| match &b.set {
                    Some(TlaExpr::Ident(s)) => Some(s) == node_set.as_ref(),
                    _ => false,
                });
                if bound_ok {
                    continue;
                }
            }
            // Otherwise it is only allowed as an environment action (message
            // loss/duplication), which may touch nothing but the network.
            let touched = self.written_vars_of_disjunct(disjunct);
            let only_network =
                !touched.is_empty() && touched.iter().all(|v| Some(v) == self.network_var.as_ref());
            if !only_network {
                self.push(
                    "CS012",
                    "C5",
                    CleanSeverity::Error,
                    Some(self.config.next_operator.clone()),
                    line,
                    format!(
                        "Next disjunct `{}` is not `\\E self \\in {} : Action(self, ...)` and is \
                         not a network-only environment action (writes: {})",
                        render(disjunct),
                        node_set.as_deref().unwrap_or("Node"),
                        if touched.is_empty() {
                            "none".to_string()
                        } else {
                            touched.iter().cloned().collect::<Vec<_>>().join(", ")
                        }
                    ),
                    "wrap the step in `\\E self \\in Node :` so the projection knows which node \
                     executes it"
                        .to_string(),
                );
            }
        }
    }

    /// Variables written by a Next disjunct, following one level of call.
    fn written_vars_of_disjunct(&self, e: &TlaExpr) -> BTreeSet<String> {
        let mut written = BTreeSet::new();
        collect_written_vars(e, &self.vars, &mut written);
        for name in referenced_operators(e, &self.ops.keys().cloned().collect()) {
            if let Some(op) = self.ops.get(&name) {
                collect_written_vars(&op.body, &self.vars, &mut written);
            }
        }
        written
    }

    // -- C2 (per action) --------------------------------------------------

    fn check_actions(&mut self) {
        let actions: Vec<String> = self.actions.iter().cloned().collect();
        for name in actions {
            let Some(op) = self.ops.get(&name).copied() else {
                continue;
            };
            let ctx = Ctx {
                operator: name.clone(),
                line: op.span.map(|s| s.start.line),
                node_syms: op.params.iter().map(|p| p.name.clone()).collect(),
                self_sym: self
                    .action_self
                    .get(&name)
                    .cloned()
                    .or_else(|| op.params.first().map(|p| p.name.clone())),
                msg_syms: BTreeSet::new(),
            };
            self.check_expr(&op.body, &ctx);
        }
        // Non-action helper operators still must not aggregate across nodes.
        let helper_names: Vec<String> = self
            .module
            .operators
            .iter()
            .map(|o| o.name.clone())
            .filter(|n| !self.actions.contains(n) && n != &self.config.next_operator)
            .collect();
        for name in helper_names {
            let Some(op) = self.ops.get(&name).copied() else {
                continue;
            };
            if name == self.config.init_operator {
                continue;
            }
            self.check_aggregation(&op.body, &name, op.span.map(|s| s.start.line));
        }
    }

    fn check_expr(&mut self, e: &TlaExpr, ctx: &Ctx) {
        // Frame conditions (`x'[j] = x[j]`, `x' = x`) are semantically
        // projectable even though they mention a non-self index; the P5 pass
        // regenerates them anyway.
        if is_frame_condition(e) {
            return;
        }
        match e {
            TlaExpr::FnApply { func, arg } => {
                if let Some(v) = base_var_name(func) {
                    if self.per_node.contains(&v) {
                        self.check_index(&v, arg, ctx);
                        self.check_expr(arg, ctx);
                        return;
                    }
                }
                self.check_expr(func, ctx);
                self.check_expr(arg, ctx);
            }
            TlaExpr::FnExcept { func, updates } => {
                if let Some(v) = base_var_name(func) {
                    if self.per_node.contains(&v) {
                        if let Some(TlaExceptPath::Index(idx)) =
                            updates.first().and_then(|u| u.path.first())
                        {
                            self.check_index(&v, idx, ctx);
                        }
                    }
                }
                for u in updates {
                    for p in &u.path {
                        if let TlaExceptPath::Index(idx) = p {
                            self.check_expr(idx, ctx);
                        }
                    }
                    self.check_expr(&u.value, ctx);
                }
            }
            TlaExpr::Ident(name) => {
                if self.per_node.contains(name) {
                    self.push(
                        "CS015",
                        "C2",
                        CleanSeverity::Error,
                        Some(ctx.operator.clone()),
                        ctx.line,
                        format!(
                            "reads the whole per-node array `{name}` instead of `{name}[{}]`",
                            ctx.self_sym.as_deref().unwrap_or("self")
                        ),
                        "an action may only touch its own node's copy; if it needs another \
                         node's value, that value must arrive in a message"
                            .to_string(),
                    );
                }
            }
            TlaExpr::Prime(inner) => {
                if let TlaExpr::Ident(name) = inner.as_ref() {
                    if self.per_node.contains(name) {
                        // `x' = ...` — the RHS decides; handled by BinOp below.
                        return;
                    }
                }
                self.check_expr(inner, ctx);
            }
            TlaExpr::BinOp { op, left, right } => {
                if *op == TlaBinOp::Eq {
                    if let TlaExpr::Prime(inner) = left.as_ref() {
                        if let TlaExpr::Ident(name) = inner.as_ref() {
                            if self.per_node.contains(name) {
                                self.check_whole_array_write(name, right, ctx);
                                self.check_expr(right, ctx);
                                return;
                            }
                        }
                    }
                }
                self.check_expr(left, ctx);
                self.check_expr(right, ctx);
            }
            TlaExpr::Exists { vars, body } | TlaExpr::Forall { vars, body } => {
                let mut ctx = ctx.clone();
                self.extend_bound(&mut ctx, vars);
                for b in vars {
                    if let Some(set) = &b.set {
                        self.check_expr(set, &ctx);
                    }
                }
                self.check_expr(body, &ctx);
            }
            TlaExpr::SetFilter { var, set, filter } => {
                let mut inner = ctx.clone();
                self.extend_bound(
                    &mut inner,
                    &[TlaQuantBound {
                        var: var.clone(),
                        set: Some(set.as_ref().clone()),
                    }],
                );
                self.check_expr(set, ctx);
                self.check_expr(filter, &inner);
            }
            TlaExpr::SetMap { expr, var, set } => {
                let mut inner = ctx.clone();
                self.extend_bound(
                    &mut inner,
                    &[TlaQuantBound {
                        var: var.clone(),
                        set: Some(set.as_ref().clone()),
                    }],
                );
                self.check_expr(set, ctx);
                self.check_expr(expr, &inner);
            }
            TlaExpr::FnConstruct { var, domain, body } => {
                let mut inner = ctx.clone();
                self.extend_bound(
                    &mut inner,
                    &[TlaQuantBound {
                        var: var.clone(),
                        set: Some(domain.as_ref().clone()),
                    }],
                );
                self.check_expr(domain, ctx);
                self.check_expr(body, &inner);
            }
            TlaExpr::Choose { var, set, body } => {
                let mut inner = ctx.clone();
                inner.node_syms.remove(var);
                if let Some(s) = set {
                    self.check_expr(s, ctx);
                }
                self.check_expr(body, &inner);
            }
            TlaExpr::LetIn { defs, body } => {
                for d in defs {
                    self.check_expr(&d.body, ctx);
                }
                self.check_expr(body, ctx);
            }
            TlaExpr::UnaryOp { operand, .. } => self.check_expr(operand, ctx),
            TlaExpr::OpApply { op, args } => {
                self.check_expr(op, ctx);
                for a in args {
                    self.check_expr(a, ctx);
                }
            }
            TlaExpr::SetEnum(items) | TlaExpr::Tuple(items) => {
                for i in items {
                    self.check_expr(i, ctx);
                }
            }
            TlaExpr::Record(fields) => {
                for (_, v) in fields {
                    self.check_expr(v, ctx);
                }
            }
            TlaExpr::RecordAccess { record, .. } => self.check_expr(record, ctx),
            TlaExpr::IfThenElse {
                cond,
                then_expr,
                else_expr,
            } => {
                self.check_expr(cond, ctx);
                self.check_expr(then_expr, ctx);
                self.check_expr(else_expr, ctx);
            }
            TlaExpr::Case { arms, other } => {
                for (g, v) in arms {
                    self.check_expr(g, ctx);
                    self.check_expr(v, ctx);
                }
                if let Some(o) = other {
                    self.check_expr(o, ctx);
                }
            }
            TlaExpr::FnSet { domain, range } => {
                self.check_expr(domain, ctx);
                self.check_expr(range, ctx);
            }
            TlaExpr::Unchanged(_) | TlaExpr::Number(_) | TlaExpr::String(_) | TlaExpr::Bool(_) => {}
            TlaExpr::Enabled(inner) | TlaExpr::Always(inner) | TlaExpr::Eventually(inner) => {
                self.check_expr(inner, ctx)
            }
            TlaExpr::LeadsTo { left, right } => {
                self.check_expr(left, ctx);
                self.check_expr(right, ctx);
            }
            TlaExpr::WeakFairness { action, .. } | TlaExpr::StrongFairness { action, .. } => {
                self.check_expr(action, ctx)
            }
        }
    }

    fn extend_bound(&self, ctx: &mut Ctx, vars: &[TlaQuantBound]) {
        for b in vars {
            match &b.set {
                Some(TlaExpr::Ident(s)) if Some(s) == self.node_set.as_ref() => {
                    ctx.node_syms.insert(b.var.clone());
                }
                Some(TlaExpr::Ident(s)) if Some(s) == self.network_var.as_ref() => {
                    ctx.msg_syms.insert(b.var.clone());
                    ctx.node_syms.remove(&b.var);
                }
                _ => {
                    ctx.node_syms.remove(&b.var);
                }
            }
        }
    }

    fn check_index(&mut self, var: &str, idx: &TlaExpr, ctx: &Ctx) {
        let Some(self_sym) = ctx.self_sym.as_deref() else {
            return;
        };
        if matches!(idx, TlaExpr::Ident(s) if s == self_sym) {
            return;
        }
        let rendered = render(idx);
        let (why, hint) = if matches!(idx, TlaExpr::Ident(s) if ctx.node_syms.contains(s)) {
            (
                format!("reads peer node state `{var}[{rendered}]` (self is `{self_sym}`)"),
                format!(
                    "message-ify it: `{rendered}` must send the value of its `{var}` in a \
                     message that this action receives"
                ),
            )
        } else if let TlaExpr::RecordAccess { record, field } = idx {
            (
                format!(
                    "indexes `{var}` by the message field `{}.{field}` — that is another node's \
                     state read through a message header",
                    render(record)
                ),
                format!(
                    "put the needed `{var}` value into the message payload instead of indexing \
                     local state by the sender id"
                ),
            )
        } else {
            (
                format!("indexes `{var}[{rendered}]` by something other than self (`{self_sym}`)"),
                format!("an action may only touch `{var}[{self_sym}]`"),
            )
        };
        self.push(
            "CS003",
            "C2",
            CleanSeverity::Error,
            Some(ctx.operator.clone()),
            ctx.line,
            why,
            hint,
        );
    }

    fn check_whole_array_write(&mut self, var: &str, rhs: &TlaExpr, ctx: &Ctx) {
        let bad = match rhs {
            TlaExpr::FnConstruct { domain, .. } => {
                matches!(domain.as_ref(), TlaExpr::Ident(s) if Some(s) == self.node_set.as_ref())
            }
            _ => false,
        };
        if bad {
            self.push(
                "CS016",
                "C2",
                CleanSeverity::Error,
                Some(ctx.operator.clone()),
                ctx.line,
                format!(
                    "rewrites the whole per-node array `{var}' = [i \\in {} |-> ...]` in an action",
                    self.node_set.as_deref().unwrap_or("Node")
                ),
                format!(
                    "only Init may build the whole array; an action must use \
                     `{var}' = [{var} EXCEPT ![{}] = ...]`",
                    ctx.self_sym.as_deref().unwrap_or("self")
                ),
            );
        }
    }

    // -- C3 ---------------------------------------------------------------

    fn check_c3_history_vars(&mut self) {
        // (a) write-only variables: never read by Init or by any action.
        let mut read: BTreeSet<String> = BTreeSet::new();
        let mut names: Vec<String> = self.actions.iter().cloned().collect();
        names.push(self.config.init_operator.clone());
        for name in &names {
            if let Some(op) = self.ops.get(name) {
                collect_effective_reads(&op.body, &self.vars, &mut read);
            }
        }
        let candidates: Vec<String> = self
            .vars
            .iter()
            .filter(|v| Some(*v) != self.network_var.as_ref())
            .filter(|v| !read.contains(*v))
            .filter(|v| self.is_accumulator_only(v))
            .cloned()
            .collect();
        for v in candidates {
            self.push(
                "CS005",
                "C3",
                CleanSeverity::Error,
                None,
                None,
                format!(
                    "variable `{v}` is written but never read by Init or by any action — it is a \
                     history/ghost variable"
                ),
                format!(
                    "delete `{v}` and its updates; history variables exist only for the original \
                     proof and have no single-process counterpart"
                ),
            );
        }

        // (b) aggregation over the node set inside actions.
        let action_ops: Vec<(String, Option<usize>, &TlaExpr)> = self
            .actions
            .iter()
            .filter_map(|n| {
                self.ops
                    .get(n)
                    .map(|op| (n.clone(), op.span.map(|s| s.start.line), &op.body))
            })
            .collect();
        for (name, line, body) in action_ops {
            self.check_aggregation(body, &name, line);
        }
    }

    /// True when every update of `v` in an action only grows it
    /// (`v' = v \cup X`, `v' = v + n`, `v' = v`). Such a variable that nothing
    /// ever reads is a history variable; a variable updated with `EXCEPT` is
    /// real state whose reads simply live elsewhere.
    fn is_accumulator_only(&self, v: &str) -> bool {
        let mut updates = Vec::new();
        for name in &self.actions {
            if let Some(op) = self.ops.get(name) {
                collect_var_updates(&op.body, v, &mut updates);
            }
        }
        if updates.is_empty() {
            return false;
        }
        updates.iter().all(|rhs| match rhs {
            TlaExpr::Ident(x) => x == v,
            TlaExpr::BinOp {
                op: TlaBinOp::Cup | TlaBinOp::Plus,
                left,
                ..
            } => base_var_name(left).as_deref() == Some(v),
            _ => false,
        })
    }

    fn check_aggregation(&mut self, body: &TlaExpr, op_name: &str, line: Option<usize>) {
        let Some(node_set) = self.node_set.clone() else {
            return;
        };
        let mut hits = Vec::new();
        collect_node_aggregations(body, &node_set, &self.per_node, &mut hits);
        for (var, bound) in hits {
            self.push(
                "CS006",
                "C3",
                CleanSeverity::Error,
                Some(op_name.to_string()),
                line,
                format!(
                    "aggregates `{var}[{bound}]` over all of `{node_set}` — a global view of \
                     per-node state"
                ),
                "count locally instead: accumulate the per-node values this node actually \
                 received into a local set and use `Cardinality` on that"
                    .to_string(),
            );
        }
    }

    // -- C4 ---------------------------------------------------------------

    fn check_c4_network_usage(&mut self) {
        let Some(net) = self.network_var.clone() else {
            return;
        };
        let action_ops: Vec<(String, Option<usize>)> = self
            .actions
            .iter()
            .filter_map(|n| {
                self.ops
                    .get(n)
                    .map(|op| (n.clone(), op.span.map(|s| s.start.line)))
            })
            .collect();
        for (name, line) in action_ops {
            let body = self.ops.get(&name).map(|o| o.body.clone());
            let Some(body) = body else { continue };
            let mut updates = Vec::new();
            collect_var_updates(&body, &net, &mut updates);
            for rhs in updates {
                if !self.is_whitelisted_network_update(&rhs, &net) {
                    self.push(
                        "CS009",
                        "C4",
                        CleanSeverity::Error,
                        Some(name.clone()),
                        line,
                        format!(
                            "network variable updated as `{net}' = {}`, which is not a \
                             send/reply/discard shape",
                            render(&rhs)
                        ),
                        format!(
                            "use `{net}' = {net} \\cup {{m}}` (send), \
                             `{net}' = {net} \\ {{m}}` (discard), or a whitelisted operator ({})",
                            self.config.network_operators.join("/")
                        ),
                    );
                }
                self.check_message_fields(&rhs, &name, line);
            }
        }
    }

    fn is_whitelisted_network_update(&self, rhs: &TlaExpr, net: &str) -> bool {
        match rhs {
            TlaExpr::Ident(v) if v == net => true,
            TlaExpr::BinOp {
                op: TlaBinOp::Cup | TlaBinOp::Setminus,
                left,
                right,
            } => {
                self.is_whitelisted_network_update(left, net)
                    && !mentions_var(right, net)
                    && matches!(right.as_ref(), TlaExpr::SetEnum(_) | TlaExpr::Ident(_))
            }
            TlaExpr::OpApply { op, .. } => match op.as_ref() {
                TlaExpr::Ident(name) => self.config.network_operators.contains(name),
                _ => false,
            },
            _ => false,
        }
    }

    fn check_message_fields(&mut self, rhs: &TlaExpr, op_name: &str, line: Option<usize>) {
        let mut records = Vec::new();
        collect_records(rhs, &mut records);
        for fields in records {
            let names: BTreeSet<String> = fields.iter().cloned().collect();
            let has_src = names
                .iter()
                .any(|f| self.config.src_field_aliases.contains(f));
            let has_dst = names
                .iter()
                .any(|f| self.config.dst_field_aliases.contains(f));
            if has_src && has_dst {
                continue;
            }
            let mut missing = Vec::new();
            if !has_src {
                missing.push("src");
            }
            if !has_dst {
                missing.push("dst");
            }
            self.push(
                "CS010",
                "C4",
                CleanSeverity::Error,
                Some(op_name.to_string()),
                line,
                format!(
                    "sent message `[{}]` is missing the {} field(s)",
                    fields.join(", "),
                    missing.join(" and ")
                ),
                "the framework routes on `src`/`dst`; every message must name its sender and \
                 its destination"
                    .to_string(),
            );
        }
    }

    // -- helpers ----------------------------------------------------------

    #[allow(clippy::too_many_arguments)]
    fn push(
        &mut self,
        code: &'static str,
        rule: &'static str,
        severity: CleanSeverity,
        operator: Option<String>,
        line: Option<usize>,
        message: String,
        hint: String,
    ) {
        let v = CleanViolation {
            code,
            rule,
            severity,
            operator,
            line,
            message,
            hint,
        };
        if !self.violations.contains(&v) {
            self.violations.push(v);
        }
    }
}

// ---------------------------------------------------------------------------
// AST helpers
// ---------------------------------------------------------------------------

/// Render an expression compactly, for diagnostics only.
fn render(e: &TlaExpr) -> String {
    match e {
        TlaExpr::Ident(s) => s.clone(),
        TlaExpr::Prime(i) => format!("{}'", render(i)),
        TlaExpr::Number(n) => match n {
            crate::tla::ast::TlaNumber::Decimal(s)
            | crate::tla::ast::TlaNumber::Binary(s)
            | crate::tla::ast::TlaNumber::Octal(s)
            | crate::tla::ast::TlaNumber::Hex(s) => s.clone(),
        },
        TlaExpr::String(s) => format!("\"{s}\""),
        TlaExpr::Bool(b) => if *b { "TRUE" } else { "FALSE" }.to_string(),
        TlaExpr::FnApply { func, arg } => format!("{}[{}]", render(func), render(arg)),
        TlaExpr::RecordAccess { record, field } => format!("{}.{field}", render(record)),
        TlaExpr::OpApply { op, args } => format!(
            "{}({})",
            render(op),
            args.iter().map(render).collect::<Vec<_>>().join(", ")
        ),
        TlaExpr::SetEnum(items) => format!(
            "{{{}}}",
            items.iter().map(render).collect::<Vec<_>>().join(", ")
        ),
        TlaExpr::Record(fields) => format!(
            "[{}]",
            fields
                .iter()
                .map(|(k, v)| format!("{k} |-> {}", render(v)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        TlaExpr::BinOp { op, left, right } => {
            format!("{} {} {}", render(left), binop_str(*op), render(right))
        }
        TlaExpr::UnaryOp { op, operand } => match op {
            TlaUnaryOp::Not => format!("~{}", render(operand)),
            TlaUnaryOp::Neg => format!("-{}", render(operand)),
            TlaUnaryOp::Subset => format!("SUBSET {}", render(operand)),
            TlaUnaryOp::Union => format!("UNION {}", render(operand)),
            TlaUnaryOp::Domain => format!("DOMAIN {}", render(operand)),
        },
        TlaExpr::FnExcept { func, .. } => format!("[{} EXCEPT ...]", render(func)),
        TlaExpr::FnConstruct { var, domain, .. } => {
            format!("[{var} \\in {} |-> ...]", render(domain))
        }
        TlaExpr::Exists { vars, .. } => format!(
            "\\E {} : ...",
            vars.iter()
                .map(|b| b.var.clone())
                .collect::<Vec<_>>()
                .join(", ")
        ),
        TlaExpr::Forall { vars, .. } => format!(
            "\\A {} : ...",
            vars.iter()
                .map(|b| b.var.clone())
                .collect::<Vec<_>>()
                .join(", ")
        ),
        TlaExpr::Unchanged(_) => "UNCHANGED ...".to_string(),
        _ => "<expr>".to_string(),
    }
}

fn binop_str(op: TlaBinOp) -> &'static str {
    match op {
        TlaBinOp::And => "/\\",
        TlaBinOp::Or => "\\/",
        TlaBinOp::Implies => "=>",
        TlaBinOp::Iff => "<=>",
        TlaBinOp::In => "\\in",
        TlaBinOp::NotIn => "\\notin",
        TlaBinOp::Subseteq => "\\subseteq",
        TlaBinOp::Cup => "\\cup",
        TlaBinOp::Cap => "\\cap",
        TlaBinOp::Setminus => "\\",
        TlaBinOp::CrossProd => "\\X",
        TlaBinOp::Plus => "+",
        TlaBinOp::Minus => "-",
        TlaBinOp::Times => "*",
        TlaBinOp::Div => "\\div",
        TlaBinOp::Mod => "%",
        TlaBinOp::Slash => "/",
        TlaBinOp::Caret => "^",
        TlaBinOp::DotDot => "..",
        TlaBinOp::Eq => "=",
        TlaBinOp::Neq => "#",
        TlaBinOp::Lt => "<",
        TlaBinOp::Gt => ">",
        TlaBinOp::Leq => "<=",
        TlaBinOp::Geq => ">=",
        TlaBinOp::Compose => "\\cdot",
    }
}

/// Walk every sub-expression, calling `f` on each node.
fn walk(e: &TlaExpr, f: &mut impl FnMut(&TlaExpr)) {
    f(e);
    match e {
        TlaExpr::Prime(i)
        | TlaExpr::UnaryOp { operand: i, .. }
        | TlaExpr::Enabled(i)
        | TlaExpr::Always(i)
        | TlaExpr::Eventually(i) => walk(i, f),
        TlaExpr::BinOp { left, right, .. } | TlaExpr::LeadsTo { left, right } => {
            walk(left, f);
            walk(right, f);
        }
        TlaExpr::OpApply { op, args } => {
            walk(op, f);
            for a in args {
                walk(a, f);
            }
        }
        TlaExpr::FnApply { func, arg } => {
            walk(func, f);
            walk(arg, f);
        }
        TlaExpr::SetEnum(items) | TlaExpr::Tuple(items) | TlaExpr::Unchanged(items) => {
            for i in items {
                walk(i, f);
            }
        }
        TlaExpr::SetFilter { set, filter, .. } => {
            walk(set, f);
            walk(filter, f);
        }
        TlaExpr::SetMap { expr, set, .. } => {
            walk(expr, f);
            walk(set, f);
        }
        TlaExpr::FnConstruct { domain, body, .. } => {
            walk(domain, f);
            walk(body, f);
        }
        TlaExpr::FnExcept { func, updates } => {
            walk(func, f);
            for u in updates {
                for p in &u.path {
                    if let TlaExceptPath::Index(i) = p {
                        walk(i, f);
                    }
                }
                walk(&u.value, f);
            }
        }
        TlaExpr::FnSet { domain, range } => {
            walk(domain, f);
            walk(range, f);
        }
        TlaExpr::Record(fields) => {
            for (_, v) in fields {
                walk(v, f);
            }
        }
        TlaExpr::RecordAccess { record, .. } => walk(record, f),
        TlaExpr::Forall { vars, body } | TlaExpr::Exists { vars, body } => {
            for b in vars {
                if let Some(s) = &b.set {
                    walk(s, f);
                }
            }
            walk(body, f);
        }
        TlaExpr::Choose { set, body, .. } => {
            if let Some(s) = set {
                walk(s, f);
            }
            walk(body, f);
        }
        TlaExpr::IfThenElse {
            cond,
            then_expr,
            else_expr,
        } => {
            walk(cond, f);
            walk(then_expr, f);
            walk(else_expr, f);
        }
        TlaExpr::Case { arms, other } => {
            for (g, v) in arms {
                walk(g, f);
                walk(v, f);
            }
            if let Some(o) = other {
                walk(o, f);
            }
        }
        TlaExpr::LetIn { defs, body } => {
            for d in defs {
                walk(&d.body, f);
            }
            walk(body, f);
        }
        TlaExpr::WeakFairness { vars, action } | TlaExpr::StrongFairness { vars, action } => {
            walk(vars, f);
            walk(action, f);
        }
        TlaExpr::Ident(_) | TlaExpr::Number(_) | TlaExpr::String(_) | TlaExpr::Bool(_) => {}
    }
}

/// Strip `'` and return the identifier name at the base of an application.
fn base_var_name(e: &TlaExpr) -> Option<String> {
    match e {
        TlaExpr::Ident(s) => Some(s.clone()),
        TlaExpr::Prime(i) => base_var_name(i),
        _ => None,
    }
}

fn contains_prime(e: &TlaExpr) -> bool {
    let mut found = false;
    walk(e, &mut |x| {
        if matches!(x, TlaExpr::Prime(_)) || matches!(x, TlaExpr::Unchanged(_)) {
            found = true;
        }
    });
    found
}

fn mentions_var(e: &TlaExpr, var: &str) -> bool {
    let mut found = false;
    walk(e, &mut |x| {
        if matches!(x, TlaExpr::Ident(s) if s == var) {
            found = true;
        }
    });
    found
}

/// `x' = x` or `x'[j] = x[j]` — a frame condition, not a cross-node read.
fn is_frame_condition(e: &TlaExpr) -> bool {
    let TlaExpr::BinOp {
        op: TlaBinOp::Eq,
        left,
        right,
    } = e
    else {
        return false;
    };
    fn unprime(e: &TlaExpr) -> Option<TlaExpr> {
        match e {
            TlaExpr::Prime(i) => Some(i.as_ref().clone()),
            TlaExpr::FnApply { func, arg } => unprime(func).map(|f| TlaExpr::FnApply {
                func: Box::new(f),
                arg: arg.clone(),
            }),
            _ => None,
        }
    }
    unprime(left).as_ref() == Some(right.as_ref())
}

fn flatten_or(e: &TlaExpr) -> Vec<&TlaExpr> {
    match e {
        TlaExpr::BinOp {
            op: TlaBinOp::Or,
            left,
            right,
        } => {
            let mut v = flatten_or(left);
            v.extend(flatten_or(right));
            v
        }
        other => vec![other],
    }
}

fn collect_exists_bounds(e: &TlaExpr, out: &mut BTreeMap<String, usize>) {
    walk(e, &mut |x| {
        if let TlaExpr::Exists { vars, .. } = x {
            for b in vars {
                if let Some(TlaExpr::Ident(s)) = &b.set {
                    *out.entry(s.clone()).or_insert(0) += 1;
                }
            }
        }
    });
}

fn collect_fn_construct_domains(e: &TlaExpr, out: &mut BTreeMap<String, usize>) {
    walk(e, &mut |x| {
        if let TlaExpr::FnConstruct { domain, .. } = x {
            if let TlaExpr::Ident(s) = domain.as_ref() {
                *out.entry(s.clone()).or_insert(0) += 1;
            }
        }
    });
}

/// Variables used as `v[...]`, `[v EXCEPT ![...]]`, or `v = [i \in S |-> ...]`.
fn collect_indexed_vars(e: &TlaExpr, vars: &BTreeSet<String>, out: &mut BTreeSet<String>) {
    walk(e, &mut |x| match x {
        TlaExpr::FnApply { func, .. } => {
            if let Some(v) = base_var_name(func) {
                if vars.contains(&v) {
                    out.insert(v);
                }
            }
        }
        TlaExpr::FnExcept { func, .. } => {
            if let Some(v) = base_var_name(func) {
                if vars.contains(&v) {
                    out.insert(v);
                }
            }
        }
        TlaExpr::BinOp {
            op: TlaBinOp::Eq,
            left,
            right,
        } => {
            if let (Some(v), TlaExpr::FnConstruct { .. }) = (base_var_name(left), right.as_ref()) {
                if vars.contains(&v) {
                    out.insert(v);
                }
            }
        }
        _ => {}
    });
}

/// Variables constrained as `v \in [NodeSet -> T]` (a TypeOK-style declaration).
fn collect_node_typed_vars(
    e: &TlaExpr,
    vars: &BTreeSet<String>,
    node_set: &str,
    out: &mut BTreeSet<String>,
) {
    walk(e, &mut |x| {
        if let TlaExpr::BinOp {
            op: TlaBinOp::In,
            left,
            right,
        } = x
        {
            if let (Some(v), TlaExpr::FnSet { domain, .. }) = (base_var_name(left), right.as_ref())
            {
                if vars.contains(&v)
                    && matches!(domain.as_ref(), TlaExpr::Ident(d) if d == node_set)
                {
                    out.insert(v);
                }
            }
        }
    });
}

/// `v' = v \cup ...` anywhere in the expression.
fn is_set_accumulated(e: &TlaExpr, var: &str) -> bool {
    let mut found = false;
    walk(e, &mut |x| {
        if let TlaExpr::BinOp {
            op: TlaBinOp::Eq,
            left,
            right,
        } = x
        {
            if base_var_name(left).as_deref() == Some(var)
                && matches!(left.as_ref(), TlaExpr::Prime(_))
            {
                if let TlaExpr::BinOp {
                    op: TlaBinOp::Cup,
                    left: l2,
                    ..
                } = right.as_ref()
                {
                    if base_var_name(l2).as_deref() == Some(var) {
                        found = true;
                    }
                }
            }
        }
    });
    found
}

/// Right-hand sides of `var' = RHS`.
fn collect_var_updates(e: &TlaExpr, var: &str, out: &mut Vec<TlaExpr>) {
    walk(e, &mut |x| {
        if let TlaExpr::BinOp {
            op: TlaBinOp::Eq,
            left,
            right,
        } = x
        {
            if matches!(left.as_ref(), TlaExpr::Prime(i) if matches!(i.as_ref(), TlaExpr::Ident(s) if s == var))
            {
                out.push(right.as_ref().clone());
            }
        }
    });
}

/// State variables that are genuinely written: primed occurrences that are not
/// part of a frame condition (`x' = x`).
fn collect_written_vars(e: &TlaExpr, vars: &BTreeSet<String>, out: &mut BTreeSet<String>) {
    let mut skip: BTreeSet<*const TlaExpr> = BTreeSet::new();
    walk(e, &mut |x| {
        if is_frame_condition(x) {
            walk(x, &mut |y| {
                if matches!(y, TlaExpr::Prime(_)) {
                    skip.insert(y as *const TlaExpr);
                }
            });
        }
    });
    walk(e, &mut |x| {
        if let TlaExpr::Prime(i) = x {
            if skip.contains(&(x as *const TlaExpr)) {
                return;
            }
            if let Some(v) = base_var_name(i) {
                if vars.contains(&v) {
                    out.insert(v);
                }
            }
        }
    });
}

/// Reads that count for the C3 history-variable test: any unprimed occurrence
/// that is not part of the variable's own accumulation or a frame condition.
fn collect_effective_reads(e: &TlaExpr, vars: &BTreeSet<String>, out: &mut BTreeSet<String>) {
    match e {
        // `v' = RHS` (an update) and `v = RHS` (an Init assignment): the left
        // side is a write, and `v' = v \cup {..}` / `v' = v + 1` is
        // self-accumulation, not a read that justifies keeping `v`.
        TlaExpr::BinOp {
            op: TlaBinOp::Eq,
            left,
            right,
        } if matches!(left.as_ref(), TlaExpr::Prime(_))
            || matches!(left.as_ref(), TlaExpr::Ident(v) if vars.contains(v)) =>
        {
            let target = base_var_name(left);
            let mut sub = BTreeSet::new();
            collect_effective_reads_inner(right, vars, &mut sub);
            if let Some(t) = &target {
                sub.remove(t);
            }
            out.extend(sub);
        }
        TlaExpr::BinOp { left, right, .. } => {
            collect_effective_reads(left, vars, out);
            collect_effective_reads(right, vars, out);
        }
        TlaExpr::LetIn { defs, body } => {
            for d in defs {
                collect_effective_reads(&d.body, vars, out);
            }
            collect_effective_reads(body, vars, out);
        }
        TlaExpr::Exists { vars: bs, body } | TlaExpr::Forall { vars: bs, body } => {
            for b in bs {
                if let Some(s) = &b.set {
                    collect_effective_reads_inner(s, vars, out);
                }
            }
            collect_effective_reads(body, vars, out);
        }
        TlaExpr::IfThenElse {
            cond,
            then_expr,
            else_expr,
        } => {
            collect_effective_reads(cond, vars, out);
            collect_effective_reads(then_expr, vars, out);
            collect_effective_reads(else_expr, vars, out);
        }
        TlaExpr::Unchanged(_) => {}
        other => collect_effective_reads_inner(other, vars, out),
    }
}

fn collect_effective_reads_inner(e: &TlaExpr, vars: &BTreeSet<String>, out: &mut BTreeSet<String>) {
    let mut primed: BTreeSet<*const TlaExpr> = BTreeSet::new();
    walk(e, &mut |x| {
        if let TlaExpr::Prime(i) = x {
            primed.insert(i.as_ref() as *const TlaExpr);
        }
    });
    walk(e, &mut |x| {
        if let TlaExpr::Ident(s) = x {
            if vars.contains(s) && !primed.contains(&(x as *const TlaExpr)) {
                out.insert(s.clone());
            }
        }
    });
}

/// `v[i]` where `i` is bound by a comprehension/quantifier over the node set.
fn collect_node_aggregations(
    e: &TlaExpr,
    node_set: &str,
    per_node: &BTreeSet<String>,
    out: &mut Vec<(String, String)>,
) {
    fn bound_over(set: &TlaExpr, node_set: &str) -> bool {
        matches!(set, TlaExpr::Ident(s) if s == node_set)
    }
    fn scan(
        body: &TlaExpr,
        bound: &str,
        per_node: &BTreeSet<String>,
        out: &mut Vec<(String, String)>,
    ) {
        walk(body, &mut |x| {
            if let TlaExpr::FnApply { func, arg } = x {
                if let (Some(v), TlaExpr::Ident(i)) = (base_var_name(func), arg.as_ref()) {
                    if per_node.contains(&v) && i == bound {
                        out.push((v, bound.to_string()));
                    }
                }
            }
        });
    }
    walk(e, &mut |x| match x {
        TlaExpr::SetMap { expr, var, set } if bound_over(set, node_set) => {
            scan(expr, var, per_node, out)
        }
        TlaExpr::SetFilter { var, set, filter } if bound_over(set, node_set) => {
            scan(filter, var, per_node, out)
        }
        TlaExpr::FnConstruct { var, domain, body } if bound_over(domain, node_set) => {
            scan(body, var, per_node, out)
        }
        _ => {}
    });
}

/// Field-name lists of every record literal in the expression.
fn collect_records(e: &TlaExpr, out: &mut Vec<Vec<String>>) {
    walk(e, &mut |x| {
        if let TlaExpr::Record(fields) = x {
            out.push(fields.iter().map(|(k, _)| k.clone()).collect());
        }
    });
}

/// Operators referenced in an expression, whether applied (`Foo(i)`) or named
/// with no arguments (`Restart`).
fn referenced_operators(e: &TlaExpr, known: &BTreeSet<String>) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    walk(e, &mut |x| match x {
        TlaExpr::OpApply { op, .. } => {
            if let TlaExpr::Ident(name) = op.as_ref() {
                if known.contains(name) {
                    out.insert(name.clone());
                }
            }
        }
        TlaExpr::Ident(name) => {
            if known.contains(name) {
                out.insert(name.clone());
            }
        }
        _ => {}
    });
    out
}

/// `Next` call sites: `(action name, first argument if it is a bound symbol)`.
fn collect_action_call_sites(
    e: &TlaExpr,
    bound: &BTreeSet<String>,
    out: &mut Vec<(String, Option<String>)>,
) {
    match e {
        TlaExpr::Exists { vars, body } => {
            let mut inner = bound.clone();
            for b in vars {
                inner.insert(b.var.clone());
            }
            collect_action_call_sites(body, &inner, out);
        }
        TlaExpr::BinOp { left, right, .. } => {
            collect_action_call_sites(left, bound, out);
            collect_action_call_sites(right, bound, out);
        }
        TlaExpr::OpApply { op, args } => {
            if let TlaExpr::Ident(name) = op.as_ref() {
                let first = match args.first() {
                    Some(TlaExpr::Ident(s)) if bound.contains(s) => Some(s.clone()),
                    _ => None,
                };
                out.push((name.clone(), first));
            }
        }
        TlaExpr::LetIn { body, .. } => collect_action_call_sites(body, bound, out),
        TlaExpr::IfThenElse {
            then_expr,
            else_expr,
            ..
        } => {
            collect_action_call_sites(then_expr, bound, out);
            collect_action_call_sites(else_expr, bound, out);
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tla::parser::parse_module;

    fn lint(src: &str) -> CleanReport {
        let module = parse_module(src).expect("fixture must parse");
        lint_module(&module)
    }

    fn lint_cfg(src: &str, config: &CleanSubsetConfig) -> CleanReport {
        let module = parse_module(src).expect("fixture must parse");
        lint_module_with_config(&module, config)
    }

    fn has(report: &CleanReport, code: &str) -> bool {
        report.violations.iter().any(|v| v.code == code)
    }

    /// Minimal clean spec: one per-node variable, one network variable, one
    /// node-parameterised action, one receiving action.
    const CLEAN: &str = r#"
---- MODULE Clean ----
EXTENDS Naturals

CONSTANT Node

VARIABLE state, messages

Ping(self) ==
    state[self] = 0
    /\ state' = [state EXCEPT ![self] = 1]
    /\ messages' = messages \cup {[type |-> "ping", src |-> self, dst |-> self]}

Pong(self, m) ==
    m.dst = self
    /\ state' = [state EXCEPT ![self] = 2]
    /\ messages' = messages \ {m}

Init == state = [i \in Node |-> 0] /\ messages = {}

Next == (\E self \in Node : Ping(self)) \/ (\E self \in Node : \E m \in messages : Pong(self, m))
====
"#;

    #[test]
    fn clean_spec_is_accepted() {
        let report = lint(CLEAN);
        assert!(
            report.is_clean(),
            "expected clean, got:\n{}",
            report.render()
        );
        assert_eq!(report.node_set.as_deref(), Some("Node"));
        assert_eq!(report.network_var.as_deref(), Some("messages"));
        assert_eq!(report.var_kinds["state"], VarKind::PerNode);
        assert_eq!(report.var_kinds["messages"], VarKind::Network);
        assert_eq!(report.clean_distance(), 0);
        assert!(report.actions.contains("Ping"));
        assert!(report.actions.contains("Pong"));
        assert!(!report.actions.contains("Next"));
        assert!(!report.actions.contains("Init"));
    }

    #[test]
    fn c2_cross_node_read_is_rejected() {
        let src = CLEAN.replace(
            "    state[self] = 0",
            "    (\\E peer \\in Node : state[peer] = 0)",
        );
        let report = lint(&src);
        assert!(has(&report, "CS003"), "{}", report.render());
        let v = report
            .violations
            .iter()
            .find(|v| v.code == "CS003")
            .unwrap();
        assert_eq!(v.rule, "C2");
        assert_eq!(v.operator.as_deref(), Some("Ping"));
        assert!(v.line.is_some(), "violation must carry a source line");
        assert!(v.message.contains("state[peer]"), "{}", v.message);
        assert!(v.hint.contains("message-ify"), "{}", v.hint);
    }

    #[test]
    fn c2_index_by_message_field_is_rejected() {
        let src = CLEAN.replace("    m.dst = self", "    state[m.src] = 0");
        let report = lint(&src);
        assert!(has(&report, "CS003"), "{}", report.render());
        let v = report
            .violations
            .iter()
            .find(|v| v.code == "CS003")
            .unwrap();
        assert!(v.message.contains("m.src"), "{}", v.message);
    }

    #[test]
    fn c2_whole_array_read_is_rejected() {
        let src = CLEAN.replace("    state[self] = 0", "    Cardinality(state) = 0");
        let report = lint(&src);
        assert!(has(&report, "CS015"), "{}", report.render());
    }

    #[test]
    fn c2_whole_array_write_in_action_is_rejected() {
        let src = CLEAN.replace(
            "    /\\ state' = [state EXCEPT ![self] = 1]",
            "    /\\ state' = [i \\in Node |-> 1]",
        );
        let report = lint(&src);
        assert!(has(&report, "CS016"), "{}", report.render());
    }

    #[test]
    fn init_may_build_the_whole_array() {
        // The same shape that CS016 rejects in an action is required in Init.
        let report = lint(CLEAN);
        assert!(!has(&report, "CS016"), "{}", report.render());
    }

    #[test]
    fn frame_conditions_are_not_cross_node_reads() {
        let src = CLEAN.replace(
            "    /\\ state' = [state EXCEPT ![self] = 1]",
            "    /\\ state' = [state EXCEPT ![self] = 1] /\\ (\\A j \\in Node : state'[j] = state[j])",
        );
        let report = lint(&src);
        assert!(!has(&report, "CS003"), "{}", report.render());
    }

    #[test]
    fn c1_global_scalar_variable_is_rejected() {
        let src = CLEAN
            .replace(
                "VARIABLE state, messages",
                "VARIABLE state, epoch, messages",
            )
            .replace("Init == state =", "Init == epoch = 0 /\\ state =")
            .replace(
                "    /\\ state' = [state EXCEPT ![self] = 1]",
                "    /\\ state' = [state EXCEPT ![self] = 1] /\\ epoch' = epoch + 1",
            );
        let report = lint(&src);
        assert!(has(&report, "CS001"), "{}", report.render());
        assert_eq!(report.var_kinds["epoch"], VarKind::Unclassified);
    }

    #[test]
    fn c3_history_variable_is_rejected() {
        let src = CLEAN
            .replace(
                "VARIABLE state, messages",
                "VARIABLE state, history, messages",
            )
            .replace("Init == state =", "Init == history = {} /\\ state =")
            .replace(
                "    /\\ state' = [state EXCEPT ![self] = 1]",
                "    /\\ state' = [state EXCEPT ![self] = 1] /\\ history' = history \\cup {state[self]}",
            );
        let report = lint(&src);
        assert!(has(&report, "CS005"), "{}", report.render());
        let v = report
            .violations
            .iter()
            .find(|v| v.code == "CS005")
            .unwrap();
        assert_eq!(v.rule, "C3");
        assert!(v.message.contains("history"), "{}", v.message);
    }

    #[test]
    fn c3_real_state_is_not_reported_as_history() {
        // `state` is only ever read inside its own EXCEPT update in this spec,
        // but an EXCEPT update is not accumulation, so it is real state.
        let report = lint(CLEAN);
        assert!(!has(&report, "CS005"), "{}", report.render());
    }

    #[test]
    fn c3_aggregation_over_node_set_is_rejected() {
        let src = CLEAN.replace(
            "Init == state =",
            "AllStates == { state[i] : i \\in Node }\n\nInit == state =",
        );
        let report = lint(&src);
        assert!(has(&report, "CS006"), "{}", report.render());
        let v = report
            .violations
            .iter()
            .find(|v| v.code == "CS006")
            .unwrap();
        assert_eq!(v.operator.as_deref(), Some("AllStates"));
    }

    #[test]
    fn c4_missing_network_variable_is_rejected() {
        let src = r#"
---- MODULE NoNet ----
CONSTANT Node
VARIABLE state
Step(self) == state[self] = 0 /\ state' = [state EXCEPT ![self] = 1]
Init == state = [i \in Node |-> 0]
Next == \E self \in Node : Step(self)
====
"#;
        let report = lint(src);
        assert!(has(&report, "CS007"), "{}", report.render());
        assert!(report.network_var.is_none());
    }

    #[test]
    fn c4_two_network_candidates_are_rejected() {
        let src = CLEAN
            .replace("VARIABLE state, messages", "VARIABLE state, messages, msgs")
            .replace("Init == state =", "Init == msgs = {} /\\ state =")
            .replace(
                "    /\\ messages' = messages \\cup",
                "    /\\ msgs' = msgs \\cup {[src |-> self, dst |-> self]} /\\ messages' = messages \\cup",
            );
        let report = lint(&src);
        assert!(has(&report, "CS008"), "{}", report.render());
    }

    #[test]
    fn c4_network_variable_can_be_inferred_from_shape() {
        let src = CLEAN.replace("messages", "wire");
        let report = lint(&src);
        assert_eq!(report.network_var.as_deref(), Some("wire"));
        assert!(has(&report, "CS019"), "{}", report.render());
        // CS019 is a warning: an inferable network variable is still clean.
        assert!(report.is_clean(), "{}", report.render());
    }

    #[test]
    fn c4_non_send_network_update_is_rejected() {
        let src = CLEAN.replace(
            "    /\\ messages' = messages \\ {m}",
            "    /\\ messages' = {}",
        );
        let report = lint(&src);
        assert!(has(&report, "CS009"), "{}", report.render());
    }

    #[test]
    fn c4_whitelisted_send_operator_is_accepted() {
        let src = CLEAN.replace(
            "    /\\ messages' = messages \\ {m}",
            "    /\\ messages' = Discard(m, messages)",
        );
        let report = lint(&src);
        assert!(!has(&report, "CS009"), "{}", report.render());
    }

    #[test]
    fn c4_message_without_src_dst_is_rejected() {
        let src = CLEAN.replace(
            "{[type |-> \"ping\", src |-> self, dst |-> self]}",
            "{[type |-> \"ping\"]}",
        );
        let report = lint(&src);
        assert!(has(&report, "CS010"), "{}", report.render());
        let v = report
            .violations
            .iter()
            .find(|v| v.code == "CS010")
            .unwrap();
        assert!(v.message.contains("src and dst"), "{}", v.message);
    }

    #[test]
    fn c5_missing_next_is_rejected() {
        let src = CLEAN.replace(
            "Next == (\\E self \\in Node : Ping(self)) \\/ (\\E self \\in Node : \\E m \\in messages : Pong(self, m))",
            "",
        );
        let report = lint(&src);
        assert!(has(&report, "CS011"), "{}", report.render());
    }

    #[test]
    fn c5_missing_init_is_rejected() {
        let src = CLEAN.replace("Init == state = [i \\in Node |-> 0] /\\ messages = {}", "");
        let report = lint(&src);
        assert!(has(&report, "CS014"), "{}", report.render());
    }

    #[test]
    fn c5_unquantified_disjunct_is_rejected() {
        let src = CLEAN
            .replace(
                "Init == state =",
                "Reset == state' = [i \\in Node |-> 0] /\\ messages' = messages\n\nInit == state =",
            )
            .replace("Pong(self, m))", "Pong(self, m)) \\/ Reset");
        let report = lint(&src);
        assert!(has(&report, "CS012"), "{}", report.render());
        let v = report
            .violations
            .iter()
            .find(|v| v.code == "CS012")
            .unwrap();
        assert!(v.message.contains("Reset"), "{}", v.message);
    }

    #[test]
    fn c5_network_only_environment_action_is_accepted() {
        let src = CLEAN
            .replace(
                "Init == state =",
                "Drop(m) == messages' = messages \\ {m} /\\ state' = state\n\nInit == state =",
            )
            .replace(
                "Pong(self, m))",
                "Pong(self, m)) \\/ (\\E m \\in messages : Drop(m))",
            );
        let report = lint(&src);
        assert!(!has(&report, "CS012"), "{}", report.render());
        assert!(report.is_clean(), "{}", report.render());
    }

    #[test]
    fn missing_node_set_is_reported() {
        let src = r#"
---- MODULE NoNodes ----
CONSTANT Widget
VARIABLE messages
Step == messages' = messages \cup {[src |-> 1, dst |-> 2]}
Init == messages = {}
Next == Step
====
"#;
        let report = lint(src);
        assert!(has(&report, "CS018"), "{}", report.render());
        assert!(report.node_set.is_none());
    }

    #[test]
    fn explicit_config_overrides_inference() {
        let src = CLEAN
            .replace("CONSTANT Node", "CONSTANT Ring")
            .replace("\\in Node", "\\in Ring");
        let config = CleanSubsetConfig {
            node_set: Some("Ring".to_string()),
            network_var: Some("messages".to_string()),
            ..CleanSubsetConfig::default()
        };
        let report = lint_cfg(&src, &config);
        assert_eq!(report.node_set.as_deref(), Some("Ring"));
        assert!(report.is_clean(), "{}", report.render());
    }

    #[test]
    fn report_renders_codes_rules_and_hints() {
        let src = CLEAN.replace("    state[self] = 0", "    Cardinality(state) = 0");
        let text = lint(&src).render();
        assert!(text.contains("clean-subset lint: MODULE Clean"));
        assert!(text.contains("node set    : Node"));
        assert!(text.contains("network var : messages"));
        assert!(text.contains("[CS015/C2]"));
        assert!(text.contains("hint:"));
        assert!(text.contains("RESULT: not clean"));
    }

    #[test]
    fn violations_are_deduplicated_and_sorted() {
        let report = lint(&CLEAN.replace(
            "    state[self] = 0",
            "    (\\E peer \\in Node : state[peer] = 0 /\\ state[peer] = 1)",
        ));
        let cs003 = report
            .violations
            .iter()
            .filter(|v| v.code == "CS003")
            .count();
        assert_eq!(cs003, 1, "identical violations must be reported once");
        let severities: Vec<CleanSeverity> = report.violations.iter().map(|v| v.severity).collect();
        let mut sorted = severities.clone();
        sorted.sort();
        assert_eq!(severities, sorted, "errors must be listed before warnings");
    }

    #[test]
    fn all_diagnostic_codes_are_distinct_per_rule() {
        // Guard against copy-paste: every code used in this module must map to
        // exactly one contract rule.
        let mut seen: BTreeMap<&str, &str> = BTreeMap::new();
        let sources: Vec<CleanReport> = vec![
            lint(CLEAN),
            lint(&CLEAN.replace("    state[self] = 0", "    Cardinality(state) = 0")),
            lint(&CLEAN.replace(
                "    /\\ messages' = messages \\ {m}",
                "    /\\ messages' = {}",
            )),
        ];
        for r in &sources {
            for v in &r.violations {
                if let Some(prev) = seen.insert(v.code, v.rule) {
                    assert_eq!(prev, v.rule, "code {} mapped to two rules", v.code);
                }
            }
        }
    }
}
