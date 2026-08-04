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
//! Rules implemented so far: **C5** (actions parameterized by node) and **C1**
//! (per-node state). C5 runs first because it is what identifies the node set
//! that every other rule is stated against.

use std::collections::BTreeSet;

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
pub const RULES_CHECKED: &[CleanRule] = &[CleanRule::C1, CleanRule::C5];

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

    report.findings.sort_by_key(|f| (f.rule, f.line, f.column));
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
        assert!(json.contains(r#""rules_checked":["C1","C5"]"#), "{json}");
        assert!(
            json.contains(r#""rules_not_implemented":["C2","C3","C4"]"#),
            "a 'clean' verdict must say which rules were not evaluated: {json}"
        );
        assert!(json.contains(r#""per_node_variables":["clock"]"#), "{json}");
    }
}
