//! Clean-subset linter (Phase 52.M0).
//!
//! Decides whether a TLA+ module is in the *clean subset* — the input contract
//! for the global-multi-server → single-process projection. The contract itself
//! is written up in `docs/clean_tla_subset.md`; this module is its executable
//! form.
//!
//! The linter's job is to draw the line between "a human must rewrite this" and
//! "the tool can translate this", and to say *which decision* the human still
//! owes for each violation. A message that only says "unsupported" is a bug
//! here.
//!
//! Rules implemented so far: **C5** (actions parameterized by node), **C1**
//! (per-node state) and **C2** (no instantaneous cross-node reads). C5 runs
//! first because it is what identifies the node set that every other rule is
//! stated against, and C1 second because C2 only applies to per-node state.

use std::collections::{BTreeMap, BTreeSet};

use crate::tla::ast::{TlaBinOp, TlaExpr, TlaModule, TlaOperator};
use crate::tla::tokenizer::Span;
use crate::verus2tla::TlaPrinter;

/// A clean-subset rule.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CleanRule {
    /// Per-node state.
    C1,
    /// No instantaneous cross-node reads.
    C2,
    /// No history variables.
    C3,
    /// One designated network variable.
    C4,
    /// Actions are parameterized by node.
    C5,
}

impl CleanRule {
    pub fn as_str(&self) -> &'static str {
        match self {
            CleanRule::C1 => "C1",
            CleanRule::C2 => "C2",
            CleanRule::C3 => "C3",
            CleanRule::C4 => "C4",
            CleanRule::C5 => "C5",
        }
    }
}

/// One reason the module is not in the subset.
#[derive(Debug, Clone)]
pub struct Finding {
    pub rule: CleanRule,
    /// Line of the enclosing definition, 1-indexed. `TlaExpr` carries no span,
    /// so a finding is located at definition granularity and names the offending
    /// construct in its message.
    pub line: usize,
    pub column: usize,
    /// The definition the violation was found in, for orientation.
    pub definition: String,
    /// What is wrong and what the human has to decide about it.
    pub message: String,
}

/// The rules `lint_module` actually evaluates today. Reported alongside the
/// verdict: "clean" means "no violation of these rules", and claiming more than
/// that would be dishonest while C2/C3/C4 are unimplemented.
pub const RULES_CHECKED: &[CleanRule] = &[CleanRule::C1, CleanRule::C2, CleanRule::C5];

/// The verdict for one module.
#[derive(Debug, Clone, Default)]
pub struct CleanSubsetReport {
    pub findings: Vec<Finding>,
    /// The node set the spec quantifies over, as written (`Proc`, `0..N-1`).
    /// `None` when C5 could not identify one, in which case the other rules
    /// have nothing to state themselves against.
    pub node_set: Option<String>,
    /// Variables established to be per-node (`[Node -> T]`).
    pub per_node_variables: Vec<String>,
    /// Variables that are neither per-node nor the network.
    pub global_variables: Vec<String>,
}

impl CleanSubsetReport {
    /// No violations **of the rules that are implemented**. See `RULES_CHECKED`.
    pub fn is_clean(&self) -> bool {
        self.findings.is_empty()
    }

    /// Rules not yet implemented, so callers can qualify a "clean" verdict.
    pub fn unchecked_rules(&self) -> Vec<CleanRule> {
        [
            CleanRule::C1,
            CleanRule::C2,
            CleanRule::C3,
            CleanRule::C4,
            CleanRule::C5,
        ]
        .into_iter()
        .filter(|r| !RULES_CHECKED.contains(r))
        .collect()
    }

    pub fn violations(&self) -> usize {
        self.findings.len()
    }
}

/// Lint a parsed module against the clean subset.
pub fn lint_module(module: &TlaModule) -> CleanSubsetReport {
    let mut report = CleanSubsetReport::default();
    let ctx = LintContext::new(module);

    ctx.check_c5(&mut report);
    ctx.check_c1(&mut report);
    ctx.check_c2(&mut report);

    report.findings.sort_by_key(|f| (f.rule, f.line, f.column));
    // The same read can appear in several branches of one action; reporting it
    // once per occurrence would bury the distinct decisions a human has to make.
    report.findings.dedup_by(|a, b| {
        a.rule == b.rule && a.definition == b.definition && a.message == b.message
    });
    report
}

struct LintContext<'a> {
    module: &'a TlaModule,
    printer: TlaPrinter,
}

impl<'a> LintContext<'a> {
    fn new(module: &'a TlaModule) -> Self {
        Self {
            module,
            printer: TlaPrinter::new(),
        }
    }

    fn show(&self, expr: &TlaExpr) -> String {
        self.printer.print_expr(expr, 0).trim().replace('\n', " ")
    }

    fn operator(&self, name: &str) -> Option<&'a TlaOperator> {
        self.module.operators.iter().find(|o| o.name == name)
    }

    fn position(span: Option<Span>) -> (usize, usize) {
        span.map(|s| (s.start.line, s.start.column))
            .unwrap_or((0, 0))
    }

    fn finding(
        &self,
        rule: CleanRule,
        op: Option<&TlaOperator>,
        message: impl Into<String>,
    ) -> Finding {
        let (line, column) = Self::position(op.and_then(|o| o.span));
        Finding {
            rule,
            line,
            column,
            definition: op.map(|o| o.name.clone()).unwrap_or_default(),
            message: message.into(),
        }
    }

    // ===================== C5: actions parameterized by node =====================

    /// `Next` must be a disjunction whose disjuncts are either
    /// `\E self \in Node : Action(self)` or a parameterless environment action.
    ///
    /// This runs first: the node set it recovers is what C1 and C2 are stated
    /// against, so a module that fails C5 cannot be meaningfully checked at all.
    fn check_c5(&self, report: &mut CleanSubsetReport) {
        let Some(next) = self.operator("Next") else {
            report.findings.push(self.finding(
                CleanRule::C5,
                None,
                "no `Next` operator: the spec has no next-state relation to project. \
                 Name the top-level action `Next`, or state which operator plays that role.",
            ));
            return;
        };

        let mut node_sets: BTreeSet<String> = BTreeSet::new();
        let disjuncts = flatten_disjunction(&next.body);
        for disjunct in &disjuncts {
            self.check_c5_disjunct(disjunct, next, &mut node_sets, report);
        }

        match node_sets.len() {
            0 => {
                // Every disjunct was an environment action or unrecognized; the
                // C5 disjunct checks have already said why.
            }
            1 => report.node_set = node_sets.into_iter().next(),
            _ => {
                let listed = node_sets.into_iter().collect::<Vec<_>>().join(", ");
                report.findings.push(self.finding(
                    CleanRule::C5,
                    Some(next),
                    format!(
                        "`Next` quantifies over more than one node set ({listed}). \
                         Projection targets one node, so the spec must have a single \
                         node set; unify them, or move the extra role out of `Next` \
                         as an environment action."
                    ),
                ));
            }
        }
    }

    fn check_c5_disjunct(
        &self,
        disjunct: &TlaExpr,
        next: &TlaOperator,
        node_sets: &mut BTreeSet<String>,
        report: &mut CleanSubsetReport,
    ) {
        match disjunct {
            TlaExpr::Exists { vars, body } => {
                if vars.len() > 1 {
                    report.findings.push(self.finding(
                        CleanRule::C5,
                        Some(next),
                        format!(
                            "`Next` quantifies over {} nodes at once ({}). A step that \
                             involves two nodes atomically is a cross-node read in \
                             disguise (C2): decide which node takes the step and what \
                             message carries the other one's part.",
                            vars.len(),
                            vars.iter()
                                .map(|v| v.var.clone())
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                    ));
                }
                for bound in vars {
                    if let Some(set) = &bound.set {
                        node_sets.insert(self.show(set));
                    } else {
                        report.findings.push(self.finding(
                            CleanRule::C5,
                            Some(next),
                            format!(
                                "`\\E {}` is unbounded in `Next`; the node set must be \
                                 explicit for the projection to know what it is \
                                 projecting from.",
                                bound.var
                            ),
                        ));
                    }
                }
                // The body may itself be a disjunction of actions applied to the
                // bound node -- that is the normal shape and needs no further
                // C5 checking.
                let _ = body;
            }
            // A parameterless environment action (`Terminating`, message delivery,
            // crash) is allowed: the framework performs it, not the projected node.
            TlaExpr::Ident(_) => {}
            TlaExpr::OpApply { op, args } => {
                let named = self.show(op);
                let rendered = args.iter().map(|a| self.show(a)).collect::<Vec<_>>();
                report.findings.push(self.finding(
                    CleanRule::C5,
                    Some(next),
                    format!(
                        "`Next` applies `{named}` to fixed argument(s) ({}) instead of \
                         quantifying over the node set. Projection needs \
                         `\\E self \\in Node : {named}(self, ...)`, otherwise the spec \
                         describes one particular node rather than any node.",
                        rendered.join(", ")
                    ),
                ));
            }
            other => {
                report.findings.push(self.finding(
                    CleanRule::C5,
                    Some(next),
                    format!(
                        "`Next` has a disjunct that is neither `\\E self \\in Node : ...` \
                         nor an environment action: `{}`.",
                        self.show(other)
                    ),
                ));
            }
        }
    }

    // ===================== C2: no instantaneous cross-node reads =====================

    /// Inside an action taken by node `self`, a per-node variable may only be
    /// read at `self`.
    ///
    /// This is the rule the whole subset exists for. `x[other]` says a node
    /// atomically observes another node's current state, which no
    /// implementation can do; turning it into something implementable means
    /// deciding which message carries that value, who sends it, and what the
    /// receiver does with a stale copy. That decision is not in the spec.
    fn check_c2(&self, report: &mut CleanSubsetReport) {
        if report.node_set.is_none() || report.per_node_variables.is_empty() {
            // Nothing to state the rule against; C5/C1 have said why.
            return;
        }
        let per_node: BTreeSet<&str> = report
            .per_node_variables
            .iter()
            .map(|s| s.as_str())
            .collect();

        for (op_name, node_param) in self.node_parameterized_operators() {
            let Some(op) = self.operator(&op_name) else {
                continue;
            };
            let mut reads = Vec::new();
            self.collect_foreign_reads(&op.body, &node_param, &per_node, &mut reads);
            for (var, index) in reads {
                report.findings.push(self.finding(
                    CleanRule::C2,
                    Some(op),
                    format!(
                        "reads `{var}[{index}]` -- another node's state, observed \
                         instantaneously. A node taking this step can only read \
                         `{var}[{node_param}]`. Decide which message carries \
                         `{var}` from that node, who sends it and when, and what \
                         this action does with a stale copy."
                    ),
                ));
            }
        }
    }

    /// Operators reachable from `Next` that act on behalf of a node, mapped to
    /// the name that node goes by inside them.
    ///
    /// The node parameter is followed through calls: `Next` passes `self` to
    /// `proc(self)`, which passes its own parameter to `a(self)`, and a read of
    /// another node's state is a violation at any depth.
    fn node_parameterized_operators(&self) -> BTreeMap<String, String> {
        let mut found: BTreeMap<String, String> = BTreeMap::new();
        let Some(next) = self.operator("Next") else {
            return found;
        };

        // Seed from `\E self \in Node : ... Action(self) ...`.
        let mut seeds = Vec::new();
        for disjunct in flatten_disjunction(&next.body) {
            if let TlaExpr::Exists { vars, body } = disjunct {
                for bound in vars {
                    seeds.push((bound.var.clone(), body));
                }
            }
        }
        for (node_var, body) in seeds {
            self.enqueue_callees(body, &node_var, &mut found);
        }

        // Transitively follow the node parameter through further calls.
        loop {
            let mut grew = false;
            let snapshot: Vec<(String, String)> =
                found.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
            for (op_name, node_param) in snapshot {
                if let Some(op) = self.operator(&op_name) {
                    let before = found.len();
                    self.enqueue_callees(&op.body, &node_param, &mut found);
                    grew |= found.len() != before;
                }
            }
            if !grew {
                break;
            }
        }
        found
    }

    /// Record every operator `body` calls with `node_var` in some argument
    /// position, under the name that argument has in the callee.
    fn enqueue_callees(
        &self,
        body: &TlaExpr,
        node_var: &str,
        found: &mut BTreeMap<String, String>,
    ) {
        let mut calls = Vec::new();
        Self::collect_calls_passing(body, node_var, &mut |callee, index| {
            calls.push((callee.to_string(), index));
        });
        for (callee, index) in calls {
            let Some(op) = self.operator(&callee) else {
                continue;
            };
            let Some(param) = op.params.get(index) else {
                continue;
            };
            found.entry(callee).or_insert_with(|| param.name.clone());
        }
    }

    /// Visit `Callee(.., node_var, ..)` applications.
    fn collect_calls_passing(expr: &TlaExpr, node_var: &str, sink: &mut impl FnMut(&str, usize)) {
        if let TlaExpr::OpApply { op, args } = expr {
            if let TlaExpr::Ident(name) = &**op {
                for (i, arg) in args.iter().enumerate() {
                    if matches!(arg, TlaExpr::Ident(a) if a == node_var) {
                        sink(name, i);
                    }
                }
            }
        }
        walk_children(expr, &mut |child| {
            Self::collect_calls_passing(child, node_var, sink)
        });
    }

    /// Collect `x[e]` reads of per-node variables where `e` is not the node.
    fn collect_foreign_reads(
        &self,
        expr: &TlaExpr,
        node_param: &str,
        per_node: &BTreeSet<&str>,
        out: &mut Vec<(String, String)>,
    ) {
        if let TlaExpr::FnApply { func, arg } = expr {
            // Only the outermost index selects a node: in `req[p][q]`, `q`
            // indexes into p's own table and is not a cross-node read.
            let base: &TlaExpr = match &**func {
                TlaExpr::Prime(inner) => inner,
                other => other,
            };
            if let TlaExpr::Ident(var) = base {
                if per_node.contains(var.as_str())
                    && !matches!(&**arg, TlaExpr::Ident(a) if a == node_param)
                {
                    out.push((var.clone(), self.show(arg)));
                }
            }
        }
        walk_children(expr, &mut |child| {
            self.collect_foreign_reads(child, node_param, per_node, out)
        });
    }

    // ===================== C1: per-node state =====================

    /// Every variable must be per-node (`[Node -> T]`), the network, or absent.
    ///
    /// Per-node-ness is read off the spec's own declarations: a type invariant
    /// saying `x \in [Node -> T]`, or an `Init` conjunct building
    /// `x = [n \in Node |-> ...]`. Both are how specs in the wild state it.
    fn check_c1(&self, report: &mut CleanSubsetReport) {
        let Some(node_set) = report.node_set.clone() else {
            // Without a node set from C5 there is nothing to compare domains
            // against; C5 has already reported the reason.
            return;
        };

        let mut per_node = Vec::new();
        let mut global = Vec::new();
        for var in &self.module.variables {
            if self.is_per_node(var, &node_set) {
                per_node.push(var.clone());
            } else {
                global.push(var.clone());
            }
        }

        // A spec with no per-node variable at all is not "nearly clean": it has
        // no projection whatsoever. Saying that once is more useful than
        // repeating a C1 violation for each variable.
        if per_node.is_empty() && !global.is_empty() {
            report.findings.push(self.finding(
                CleanRule::C1,
                None,
                format!(
                    "no variable is per-node (`[{node_set} -> T]`): {}. This spec models \
                     shared state rather than a distributed protocol, so there is no node \
                     dimension to project away. It needs to be re-modelled per node before \
                     translation is meaningful.",
                    global.join(", ")
                ),
            ));
        } else {
            for var in &global {
                report.findings.push(self.finding(
                    CleanRule::C1,
                    None,
                    format!(
                        "`{var}` is mutable state that is not per-node and not the \
                         designated network. After projection each node holds only its \
                         own state, so a value spanning nodes has nowhere to live: make \
                         it `[{node_set} -> T]`, or designate it as the network (C4)."
                    ),
                ));
            }
        }

        report.per_node_variables = per_node;
        report.global_variables = global;
    }

    /// Whether `var` is declared as a function over the node set, by either the
    /// type-invariant idiom or the `Init` idiom.
    fn is_per_node(&self, var: &str, node_set: &str) -> bool {
        self.module
            .operators
            .iter()
            .any(|op| self.states_per_node(&op.body, var, node_set))
    }

    fn states_per_node(&self, expr: &TlaExpr, var: &str, node_set: &str) -> bool {
        match expr {
            // `x \in [Node -> T]` (type invariant)
            TlaExpr::BinOp {
                op: TlaBinOp::In,
                left,
                right,
            } => {
                if !self.is_var_ref(left, var) {
                    return false;
                }
                matches!(&**right, TlaExpr::FnSet { domain, .. }
                    if self.show(domain) == node_set)
            }
            // `x = [n \in Node |-> ...]` (Init)
            TlaExpr::BinOp {
                op: TlaBinOp::Eq,
                left,
                right,
            } => {
                if !self.is_var_ref(left, var) {
                    return false;
                }
                matches!(&**right, TlaExpr::FnConstruct { domain, .. }
                    if self.show(domain) == node_set)
            }
            // Walk conjunctions/disjunctions and LET bodies looking for either.
            TlaExpr::BinOp { left, right, .. } => {
                self.states_per_node(left, var, node_set)
                    || self.states_per_node(right, var, node_set)
            }
            TlaExpr::LetIn { body, .. } => self.states_per_node(body, var, node_set),
            TlaExpr::Forall { body, .. } | TlaExpr::Exists { body, .. } => {
                self.states_per_node(body, var, node_set)
            }
            _ => false,
        }
    }

    fn is_var_ref(&self, expr: &TlaExpr, var: &str) -> bool {
        matches!(expr, TlaExpr::Ident(name) if name == var)
    }
}

/// Apply `f` to each direct sub-expression.
fn walk_children(expr: &TlaExpr, f: &mut impl FnMut(&TlaExpr)) {
    match expr {
        TlaExpr::Ident(_) | TlaExpr::Number(_) | TlaExpr::String(_) | TlaExpr::Bool(_) => {}
        TlaExpr::Prime(inner)
        | TlaExpr::UnaryOp { operand: inner, .. }
        | TlaExpr::Enabled(inner)
        | TlaExpr::Always(inner)
        | TlaExpr::Eventually(inner) => f(inner),
        TlaExpr::BinOp { left, right, .. } | TlaExpr::LeadsTo { left, right } => {
            f(left);
            f(right);
        }
        TlaExpr::OpApply { op, args } => {
            f(op);
            args.iter().for_each(f);
        }
        TlaExpr::FnApply { func, arg } => {
            f(func);
            f(arg);
        }
        TlaExpr::SetEnum(items) | TlaExpr::Tuple(items) | TlaExpr::Unchanged(items) => {
            items.iter().for_each(f)
        }
        TlaExpr::SetFilter { set, filter, .. } => {
            f(set);
            f(filter);
        }
        TlaExpr::SetMap { expr, set, .. } => {
            f(expr);
            f(set);
        }
        TlaExpr::FnConstruct { domain, body, .. } => {
            f(domain);
            f(body);
        }
        TlaExpr::FnExcept { func, updates } => {
            f(func);
            for update in updates {
                for step in &update.path {
                    if let crate::tla::ast::TlaExceptPath::Index(index) = step {
                        f(index);
                    }
                }
                f(&update.value);
            }
        }
        TlaExpr::FnSet { domain, range } => {
            f(domain);
            f(range);
        }
        TlaExpr::Record(fields) | TlaExpr::RecordSet(fields) => {
            fields.iter().for_each(|(_, v)| f(v))
        }
        TlaExpr::RecordAccess { record, .. } => f(record),
        TlaExpr::Forall { vars, body } | TlaExpr::Exists { vars, body } => {
            vars.iter().filter_map(|v| v.set.as_ref()).for_each(&mut *f);
            f(body);
        }
        TlaExpr::Choose { set, body, .. } => {
            if let Some(set) = set {
                f(set);
            }
            f(body);
        }
        TlaExpr::IfThenElse {
            cond,
            then_expr,
            else_expr,
        } => {
            f(cond);
            f(then_expr);
            f(else_expr);
        }
        TlaExpr::Case { arms, other } => {
            for (cond, result) in arms {
                f(cond);
                f(result);
            }
            if let Some(other) = other {
                f(other);
            }
        }
        TlaExpr::LetIn { defs, body } => {
            defs.iter().for_each(|d| f(&d.body));
            f(body);
        }
        TlaExpr::WeakFairness { vars, action } | TlaExpr::StrongFairness { vars, action } => {
            f(vars);
            f(action);
        }
    }
}

/// Flatten a `\/`-tree into its disjuncts.
fn flatten_disjunction(expr: &TlaExpr) -> Vec<&TlaExpr> {
    match expr {
        TlaExpr::BinOp {
            op: TlaBinOp::Or,
            left,
            right,
        } => {
            let mut out = flatten_disjunction(left);
            out.extend(flatten_disjunction(right));
            out
        }
        other => vec![other],
    }
}

/// Render a report as JSON. Hand-written to keep the linter free of a
/// serialization dependency and to make the shape obvious at the call site;
/// the schema is documented in `docs/clean_tla_subset.md`.
pub fn report_to_json(report: &CleanSubsetReport) -> String {
    let findings = report
        .findings
        .iter()
        .map(|f| {
            format!(
                r#"{{"rule":"{}","line":{},"column":{},"definition":"{}","message":"{}"}}"#,
                f.rule.as_str(),
                f.line,
                f.column,
                escape_json(&f.definition),
                escape_json(&f.message)
            )
        })
        .collect::<Vec<_>>()
        .join(",");

    let quoted = |value: &Option<String>| match value {
        Some(v) => format!(r#""{}""#, escape_json(v)),
        None => "null".to_string(),
    };
    let list = |values: &[String]| {
        values
            .iter()
            .map(|v| format!(r#""{}""#, escape_json(v)))
            .collect::<Vec<_>>()
            .join(",")
    };

    let rules_checked = RULES_CHECKED
        .iter()
        .map(|r| format!(r#""{}""#, r.as_str()))
        .collect::<Vec<_>>()
        .join(",");
    let rules_unchecked = report
        .unchecked_rules()
        .iter()
        .map(|r| format!(r#""{}""#, r.as_str()))
        .collect::<Vec<_>>()
        .join(",");

    format!(
        r#"{{"clean":{},"violations":{},"rules_checked":[{rules_checked}],"rules_not_implemented":[{rules_unchecked}],"node_set":{},"per_node_variables":[{}],"global_variables":[{}],"findings":[{}]}}"#,
        report.is_clean(),
        report.violations(),
        quoted(&report.node_set),
        list(&report.per_node_variables),
        list(&report.global_variables),
        findings
    )
}

fn escape_json(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tla::parse_module;

    fn lint(source: &str) -> CleanSubsetReport {
        let module = parse_module(source).expect("test spec must parse");
        lint_module(&module)
    }

    fn rules(report: &CleanSubsetReport) -> Vec<CleanRule> {
        report.findings.iter().map(|f| f.rule).collect()
    }

    #[test]
    fn accepts_a_per_node_spec() {
        let source = r#"---- MODULE Test ----
VARIABLES clock, req
TypeOK == /\ clock \in [Proc -> Nat]
          /\ req \in [Proc -> [Proc -> Nat]]
Step(p) == clock' = [clock EXCEPT ![p] = clock[p] + 1]
Next == \E p \in Proc : Step(p)
===="#;
        let report = lint(source);
        assert!(
            report.is_clean(),
            "expected clean, got {:?}",
            report.findings
        );
        assert_eq!(report.node_set.as_deref(), Some("Proc"));
        assert_eq!(report.per_node_variables, vec!["clock", "req"]);
    }

    #[test]
    fn recognizes_per_node_state_from_init() {
        // Not every spec has a type invariant; `Init` states the shape too.
        let source = r#"---- MODULE Test ----
VARIABLES pc
Init == pc = [n \in Proc |-> "start"]
Step(p) == pc' = [pc EXCEPT ![p] = "done"]
Next == \E p \in Proc : Step(p)
===="#;
        let report = lint(source);
        assert!(report.is_clean(), "got {:?}", report.findings);
        assert_eq!(report.per_node_variables, vec!["pc"]);
    }

    #[test]
    fn rejects_a_global_mutable_variable() {
        // LamportMutex's `crit \in SUBSET Proc`: a set spanning nodes has
        // nowhere to live once the node dimension is projected away.
        let source = r#"---- MODULE Test ----
VARIABLES clock, crit
TypeOK == /\ clock \in [Proc -> Nat]
          /\ crit \in SUBSET Proc
Enter(p) == crit' = crit \union {p}
Next == \E p \in Proc : Enter(p)
===="#;
        let report = lint(source);
        assert_eq!(rules(&report), vec![CleanRule::C1]);
        assert!(
            report.findings[0].message.contains("crit"),
            "the finding must name the variable: {}",
            report.findings[0].message
        );
        assert_eq!(report.global_variables, vec!["crit"]);
    }

    #[test]
    fn reports_a_fully_global_spec_once() {
        // ReadersWriters: nothing is per-node, so the spec has no projection at
        // all. One finding is more useful than one per variable.
        let source = r#"---- MODULE Test ----
VARIABLES readers, writers
Init == /\ readers = {}
        /\ writers = {}
Acquire(p) == readers' = readers \union {p}
Next == \E p \in Proc : Acquire(p)
===="#;
        let report = lint(source);
        assert_eq!(rules(&report), vec![CleanRule::C1]);
        assert!(
            report.findings[0]
                .message
                .contains("no variable is per-node"),
            "got {}",
            report.findings[0].message
        );
    }

    #[test]
    fn rejects_next_without_node_quantification() {
        let source = r#"---- MODULE Test ----
VARIABLES x
Step(p) == x' = x
Next == Step(1)
===="#;
        let report = lint(source);
        let c5 = report
            .findings
            .iter()
            .find(|f| f.rule == CleanRule::C5)
            .unwrap_or_else(|| panic!("expected a C5 finding, got {:?}", report.findings));
        assert!(c5.message.contains("fixed argument"), "got {}", c5.message);
    }

    #[test]
    fn rejects_two_node_atomic_step() {
        let source = r#"---- MODULE Test ----
VARIABLES x
Transfer(p, q) == x' = x
Next == \E p, q \in Proc : Transfer(p, q)
===="#;
        let report = lint(source);
        let c5 = report
            .findings
            .iter()
            .find(|f| f.rule == CleanRule::C5)
            .unwrap_or_else(|| panic!("expected a C5 finding, got {:?}", report.findings));
        assert!(
            c5.message.contains("nodes at once") && c5.message.contains("cross-node read"),
            "the finding must explain that an atomic two-node step hides a \
             cross-node read: {}",
            c5.message
        );
    }

    #[test]
    fn allows_a_parameterless_environment_action() {
        let source = r#"---- MODULE Test ----
VARIABLES pc
Init == pc = [n \in Proc |-> "start"]
Step(p) == pc' = [pc EXCEPT ![p] = "done"]
Terminating == pc' = pc
Next == (\E p \in Proc : Step(p)) \/ Terminating
===="#;
        let report = lint(source);
        assert!(report.is_clean(), "got {:?}", report.findings);
    }

    #[test]
    fn missing_next_is_reported_not_silently_clean() {
        let source = r#"---- MODULE Test ----
VARIABLES x
Init == x = 0
===="#;
        let report = lint(source);
        assert_eq!(rules(&report), vec![CleanRule::C5]);
        assert!(report.node_set.is_none());
    }

    #[test]
    fn json_shape_is_stable() {
        let source = r#"---- MODULE Test ----
VARIABLES clock
TypeOK == clock \in [Proc -> Nat]
Step(p) == clock' = clock
Next == \E p \in Proc : Step(p)
===="#;
        let json = report_to_json(&lint(source));
        assert!(json.contains(r#""clean":true"#), "{json}");
        assert!(json.contains(r#""violations":0"#), "{json}");
        assert!(json.contains(r#""node_set":"Proc""#), "{json}");
        assert!(
            json.contains(r#""rules_checked":["C1","C2","C5"]"#),
            "{json}"
        );
        assert!(
            json.contains(r#""rules_not_implemented":["C3","C4"]"#),
            "a 'clean' verdict must say which rules were not evaluated: {json}"
        );
        assert!(json.contains(r#""per_node_variables":["clock"]"#), "{json}");
    }

    #[test]
    fn rejects_a_read_of_another_node() {
        // TeachingConcurrency `Simple`: the left neighbour's x.
        let source = r#"---- MODULE Test ----
VARIABLES x, y
TypeOK == /\ x \in [Proc -> Nat]
          /\ y \in [Proc -> Nat]
b(self) == y' = [y EXCEPT ![self] = x[(self - 1) % N]]
Next == \E self \in Proc : b(self)
===="#;
        let report = lint(source);
        let c2 = report
            .findings
            .iter()
            .find(|f| f.rule == CleanRule::C2)
            .unwrap_or_else(|| panic!("expected a C2 finding, got {:?}", report.findings));
        assert_eq!(c2.definition, "b");
        assert!(
            c2.message.contains("x[(self - 1) % N]") && c2.message.contains("which message"),
            "the finding must quote the read and name the decision it forces: {}",
            c2.message
        );
    }

    #[test]
    fn follows_the_node_parameter_through_calls() {
        // Next -> proc(self) -> b(self): a foreign read two calls deep is still
        // a violation, and it is attributed to the action that performs it.
        let source = r#"---- MODULE Test ----
VARIABLES x, y
TypeOK == /\ x \in [Proc -> Nat]
          /\ y \in [Proc -> Nat]
b(p) == y' = [y EXCEPT ![p] = x[p - 1]]
proc(q) == b(q)
Next == \E self \in Proc : proc(self)
===="#;
        let report = lint(source);
        let c2 = report
            .findings
            .iter()
            .find(|f| f.rule == CleanRule::C2)
            .unwrap_or_else(|| panic!("expected a C2 finding, got {:?}", report.findings));
        assert_eq!(
            c2.definition, "b",
            "attributed to the action doing the read"
        );
    }

    #[test]
    fn allows_indexing_into_the_nodes_own_table() {
        // LamportMutex `beats(p,q)`: req[p][q] is p's own accumulated table
        // about q, not q's live state. Only the outermost index selects a node.
        let source = r#"---- MODULE Test ----
VARIABLES req
TypeOK == req \in [Proc -> [Proc -> Nat]]
beats(p, q) == \/ req[p][q] = 0
               \/ req[p][p] < req[p][q]
Step(p) == \A q \in Proc : beats(p, q)
Next == \E p \in Proc : Step(p)
===="#;
        let report = lint(source);
        assert!(
            !report.findings.iter().any(|f| f.rule == CleanRule::C2),
            "reading into one's own table is not a cross-node read: {:?}",
            report.findings
        );
    }

    #[test]
    fn a_repeated_read_is_reported_once() {
        let source = r#"---- MODULE Test ----
VARIABLES x
TypeOK == x \in [Proc -> Nat]
Step(p) == \/ x' = [x EXCEPT ![p] = x[p + 1]]
           \/ x' = [x EXCEPT ![p] = x[p + 1]]
Next == \E p \in Proc : Step(p)
===="#;
        let report = lint(source);
        assert_eq!(
            report
                .findings
                .iter()
                .filter(|f| f.rule == CleanRule::C2)
                .count(),
            1,
            "one decision, one finding: {:?}",
            report.findings
        );
    }
}
