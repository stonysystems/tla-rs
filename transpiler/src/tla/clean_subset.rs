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
//! Rule order matters and is not arbitrary:
//!
//! 1. **C5** identifies the node set every other rule is stated against.
//! 2. **C4** designates the network. It runs before C1 and C2 because the
//!    network is deliberately *not* per-node state and is deliberately read
//!    across nodes — flagging it under those rules would be wrong.
//! 3. **C1** classifies the remaining variables as per-node or global.
//! 4. **C2** checks reads of per-node variables.
//! 5. **C3** looks for history variables among what C1 called global.

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
/// verdict: "clean" means "no violation of these rules".
///
/// All five are implemented now. The comment here said "while C2/C3/C4 are
/// unimplemented" long after they were, which mattered because
/// `unchecked_rules` reads this list and a reader auditing "what was actually
/// checked" was being told, in the same breath, both that the list is complete
/// and that three of it were not written yet.
///
/// The list is kept rather than deleted because `rules_skipped` answers a
/// different question -- a rule that is implemented can still decline to run on
/// a particular spec, and that is the distinction the report exists to make.
pub const RULES_CHECKED: &[CleanRule] = &[
    CleanRule::C1,
    CleanRule::C2,
    CleanRule::C3,
    CleanRule::C4,
    CleanRule::C5,
];

/// Variable names conventionally used for the message network. Used only to
/// recognise a *near-miss* -- a variable that plays the network's role but is
/// not in the required shape -- so the linter can say "this is your network,
/// and here is what is wrong with it" instead of reporting it as unexplained
/// global state.
const CONVENTIONAL_NETWORK_NAMES: &[&str] = &[
    "network", "msgs", "messages", "sentMsg", "sentMsgs", "net", "msgQueue",
];

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
    /// The variable designated as the message network, if one was identified.
    pub network_variable: Option<String>,
    /// A variable that plays the network's role but is not in the required
    /// shape. C4 explains what to do with it; other rules stay quiet about it,
    /// because "flatten the network" is the one decision to make, not one
    /// decision per read.
    pub network_near_miss: Option<String>,
    /// Rules that are implemented but did **not** run on this module, with the
    /// reason. C1/C2/C3 all need a node set, and return early without one, so a
    /// spec the linter understands *less* runs fewer rules, reports fewer
    /// findings, and scores as *cleaner* than one it understands well. The
    /// count alone cannot distinguish "nothing wrong" from "nothing checked";
    /// this field is what makes that difference visible to a reader or a script.
    pub skipped_rules: Vec<(CleanRule, String)>,
}

impl CleanSubsetReport {
    /// No violations **of the rules that are implemented**. See `RULES_CHECKED`.
    pub fn is_clean(&self) -> bool {
        self.findings.is_empty()
    }

    /// Rules not yet implemented, so callers can qualify a "clean" verdict.
    ///
    /// Empty today, and that is the honest answer rather than a dead branch:
    /// all five are implemented. What a caller wants instead is
    /// `skipped_rules`, which records a rule that *is* implemented and still
    /// declined to run on this spec -- and that is the case a low violation
    /// count must never be read past.
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
    ctx.check_c4(&mut report);
    ctx.check_c1(&mut report);
    ctx.check_c2(&mut report);
    ctx.check_c3(&mut report);

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

    /// `Next` must be a disjunction whose disjuncts are either an action taken
    /// by a node, or a parameterless environment action.
    ///
    /// The node set is **not** simply "the set `Next` quantifies over": real
    /// specs quantify over value domains in the same breath, as in Paxos's
    /// `\E b \in Ballot : Phase1a(b)` alongside `\E a \in Acceptor : Phase1b(a)`.
    /// It is inferred instead from the variable declarations -- the set that
    /// per-node state is indexed by -- and only then confirmed against `Next`.
    /// The next-state relation.
    ///
    /// Usually called `Next`, but a spec may name it anything and point at it
    /// from `Spec == Init /\ [][TPNext]_vars`. Following that is more accurate
    /// than insisting on a name -- otherwise a purely cosmetic difference
    /// inflates a spec's measured distance from the subset.
    fn next_relation(&self) -> Option<&'a TlaOperator> {
        if let Some(next) = self.operator("Next") {
            return Some(next);
        }
        // The spec operator is not always called `Spec` -- TwoPhase names its
        // `TPSpec`. Any 0-ary operator of the form `Init /\ [][Action]_vars`
        // identifies the next-state relation.
        //
        // **`Spec` first, then declaration order.** A module may define several
        // -- an abstract `AbsSpec` beside the real one is the usual reason --
        // and taking whichever was declared first meant reordering two lines
        // changed which spec was analysed. Reproduced: with `AbsSpec` above
        // `Spec` the linter examined the abstract stuttering relation and never
        // looked at the real `Next` at all.
        let named_spec = self
            .module
            .operators
            .iter()
            .find(|op| op.params.is_empty() && op.name == "Spec");
        let candidates = named_spec.into_iter().chain(
            self.module
                .operators
                .iter()
                .filter(|op| op.params.is_empty()),
        );
        for op in candidates {
            let mut named = None;
            find_boxed_action(&op.body, &mut named);
            if let Some(name) = named {
                if let Some(next) = self.operator(&name) {
                    return Some(next);
                }
            }
        }
        None
    }

    /// Every 0-ary operator of the form `Init /\ [][Action]_vars`, by the
    /// action each names.
    ///
    /// More than one means the module defines several specs and the choice of
    /// which to lint is not the linter's to make silently.
    fn spec_candidates(&self) -> Vec<(String, String)> {
        let mut out = Vec::new();
        for op in &self.module.operators {
            if !op.params.is_empty() {
                continue;
            }
            let mut named = None;
            find_boxed_action(&op.body, &mut named);
            if let Some(name) = named {
                if self.operator(&name).is_some() {
                    out.push((op.name.clone(), name));
                }
            }
        }
        out
    }

    fn check_c5(&self, report: &mut CleanSubsetReport) {
        let Some(next) = self.next_relation() else {
            report.findings.push(self.finding(
                CleanRule::C5,
                None,
                "no next-state relation: neither a `Next` operator nor a `Spec` of the \
                 form `Init /\\ [][Action]_vars` that names one.",
            ));
            return;
        };

        // A `Next` of the form `\/ CommandLeaderAction \/ ReplicaAction`
        // pushes the quantification one level down, into 0-ary grouping
        // operators. Analysing the literal body would find no node binder and
        // report a violation the spec does not have -- EPaxos is written this
        // way, and so are plenty of others.
        let expanded = self.expand_action_groups(&next.body);
        let node_set = self.infer_node_set(next, &expanded);
        let Some(node_set) = node_set else {
            report.findings.push(self.finding(
                CleanRule::C5,
                Some(next),
                "cannot identify the node set: no set is both the domain of a declared \
                 per-node variable (`x \\in [Node -> T]`) and quantified over in `Next`. \
                 Declare the per-node state over the node set, and let `Next` read \
                 `\\E self \\in Node : Action(self)`.",
            ));
            return;
        };

        // Several specs in one module, and only one of them was linted. The
        // linter picks `Spec` and then declaration order; either way the others
        // went unexamined, and this spec's verdict is not about them.
        if self.operator("Next").is_none() {
            let candidates = self.spec_candidates();
            if candidates.len() > 1 {
                report.findings.push(self.finding(
                    CleanRule::C5,
                    Some(next),
                    format!(
                        "this module defines {} next-state relations -- {} -- and \
                         only `{}` was linted. Reordering the definitions would \
                         change which one that is. Say which spec is the one to \
                         check, by naming its action `Next`.",
                        candidates.len(),
                        candidates
                            .iter()
                            .map(|(spec, action)| format!("`{spec}` names `{action}`"))
                            .collect::<Vec<_>>()
                            .join(", "),
                        next.name
                    ),
                ));
            }
        }

        // A tie was broken by the domain's printed name, silently. Say so: the
        // rules that follow are all stated against whichever set won, so a
        // reader has to know the choice was arbitrary before reading the count.
        let tied = self.tied_node_sets(&expanded);
        if tied.len() > 1 {
            report.findings.push(self.finding(
                CleanRule::C5,
                Some(next),
                format!(
                    "the node set is ambiguous: {} are equally good candidates -- \
                     each is quantified over in `Next` and carries the same amount \
                     of declared state. `{node_set}` was chosen, and every other \
                     rule below is stated against it, so a read of another \
                     candidate's state is not reported. Say which set the \
                     protocol's nodes are drawn from.",
                    tied.iter()
                        .map(|d| format!("`{d}`"))
                        .collect::<Vec<_>>()
                        .join(" and ")
                ),
            ));
        }

        for disjunct in flatten_disjunction(&expanded) {
            self.check_c5_disjunct(disjunct, next, &node_set, report);
        }
        report.node_set = Some(node_set);
    }

    /// The set that per-node state is indexed by.
    ///
    /// Candidates are the domains of variables declared as functions; the node
    /// set is the candidate that `Next` also quantifies over, and where several
    /// qualify, the one carrying the most state.
    /// Whether an operator is an action: its body is primed, or it calls
    /// something that is.
    ///
    /// The transitive part is what matters. EPaxos's `ReplicaAction` contains
    /// no `'` of its own -- it is `\E replica \in Replicas : Phase1Reply(replica)
    /// \/ ...`, and the primes live one call further down. Testing the literal
    /// body would classify it as a value and leave it unexpanded.
    fn is_action(&self, name: &str, seen: &mut Vec<String>) -> bool {
        if seen.iter().any(|s| s == name) {
            return false;
        }
        let Some(op) = self.operator(name) else {
            return false;
        };
        if crate::tla::action_projection::mentions_prime(&op.body) {
            return true;
        }
        seen.push(name.to_string());
        let mut called = Vec::new();
        collect_called_names(&op.body, &mut called);
        let result = called.iter().any(|c| self.is_action(c, seen));
        seen.pop();
        result
    }

    /// Replace 0-ary *action* operators by their bodies, so a `Next` that
    /// groups its disjuncts behind names is analysed as the disjunction it is.
    ///
    /// Only operators whose body is primed are expanded. A 0-ary *value*
    /// operator (`Ballot == 0 .. MaxBallot`) is left alone: inlining it would
    /// turn a set name into a set expression and the node set would lose the
    /// name the rest of the projection refers to it by.
    fn expand_action_groups(&self, expr: &TlaExpr) -> TlaExpr {
        fn go(expr: &TlaExpr, ctx: &LintContext<'_>, seen: &mut Vec<String>) -> TlaExpr {
            match expr {
                TlaExpr::Ident(name) => {
                    if seen.contains(name) {
                        return expr.clone();
                    }
                    match ctx.operator(name) {
                        Some(op)
                            if op.params.is_empty()
                                && groups_actions(&op.body)
                                && ctx.is_action(name, &mut Vec::new()) =>
                        {
                            seen.push(name.clone());
                            let body = go(&op.body, ctx, seen);
                            seen.pop();
                            body
                        }
                        _ => expr.clone(),
                    }
                }
                TlaExpr::BinOp {
                    op: op @ (TlaBinOp::Or | TlaBinOp::And),
                    left,
                    right,
                } => TlaExpr::BinOp {
                    op: *op,
                    left: Box::new(go(left, ctx, seen)),
                    right: Box::new(go(right, ctx, seen)),
                },
                other => other.clone(),
            }
        }
        go(expr, self, &mut Vec::new())
    }

    fn infer_node_set(&self, next: &TlaOperator, expanded: &TlaExpr) -> Option<String> {
        let mut domain_counts: BTreeMap<String, usize> = BTreeMap::new();
        for var in &self.module.variables {
            for domain in self.declared_domains(var) {
                *domain_counts.entry(domain).or_default() += 1;
            }
        }
        let _ = next;
        let quantified = Self::quantified_sets(expanded, self);

        domain_counts
            .into_iter()
            .filter(|(domain, _)| quantified.contains(domain))
            .max_by_key(|(domain, count)| (*count, domain.clone()))
            .map(|(domain, _)| domain)
    }

    /// The domains that tie for the node set, when more than one does.
    ///
    /// `infer_node_set` breaks a tie by the domain's printed name -- the one
    /// that sorts last wins -- and nothing recorded that the choice was a coin
    /// flip. It is not a harmless one: with the wrong set designated, C1/C2/C3
    /// are stated against the wrong dimension, real cross-node reads of the
    /// true per-node variable vanish from the report, and the violation count
    /// goes **down**. Renaming an unrelated set from `Aux` to `Zux` took a spec
    /// from 2 findings to 1 and dropped a genuine `log[j]`.
    ///
    /// There is no better implicit rule to reach for here: in a real tie both
    /// domains are quantified by `Next` and both are written at, which is
    /// everything the subset says a node set looks like. So the answer is to
    /// say so rather than to choose better in silence.
    fn tied_node_sets(&self, expanded: &TlaExpr) -> Vec<String> {
        let mut domain_counts: BTreeMap<String, usize> = BTreeMap::new();
        for var in &self.module.variables {
            for domain in self.declared_domains(var) {
                *domain_counts.entry(domain).or_default() += 1;
            }
        }
        let quantified = Self::quantified_sets(expanded, self);
        let candidates: Vec<(String, usize)> = domain_counts
            .into_iter()
            .filter(|(domain, _)| quantified.contains(domain))
            .collect();
        let Some(best) = candidates.iter().map(|(_, c)| *c).max() else {
            return Vec::new();
        };
        let tied: Vec<String> = candidates
            .into_iter()
            .filter(|(_, c)| *c == best)
            .map(|(d, _)| d)
            .collect();
        if tied.len() > 1 {
            tied
        } else {
            Vec::new()
        }
    }

    /// The sets `Next` quantifies over, at any depth.
    fn quantified_sets(expr: &TlaExpr, ctx: &LintContext<'_>) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        Self::collect_quantified_sets(expr, ctx, &mut out);
        out
    }

    fn collect_quantified_sets(expr: &TlaExpr, ctx: &LintContext<'_>, out: &mut BTreeSet<String>) {
        if let TlaExpr::Exists { vars, .. } | TlaExpr::Forall { vars, .. } = expr {
            for bound in vars {
                if let Some(set) = &bound.set {
                    out.insert(ctx.show(set));
                }
            }
        }
        walk_children(expr, &mut |child| {
            Self::collect_quantified_sets(child, ctx, out)
        });
    }

    /// The domains a variable is declared over, from either the type-invariant
    /// idiom (`x \in [S -> T]`) or the `Init` idiom (`x = [n \in S |-> ...]`).
    fn declared_domains(&self, var: &str) -> Vec<String> {
        let mut out = Vec::new();
        for op in &self.module.operators {
            self.collect_declared_domains(&op.body, var, &mut out);
        }
        out
    }

    fn collect_declared_domains(&self, expr: &TlaExpr, var: &str, out: &mut Vec<String>) {
        match expr {
            TlaExpr::BinOp {
                op: TlaBinOp::In,
                left,
                right,
            } if self.is_var_ref(left, var) => {
                if let TlaExpr::FnSet { domain, .. } = &**right {
                    out.push(self.show(domain));
                }
            }
            TlaExpr::BinOp {
                op: TlaBinOp::Eq,
                left,
                right,
            } if self.is_var_ref(left, var) => {
                if let TlaExpr::FnConstruct { domain, .. } = &**right {
                    out.push(self.show(domain));
                }
            }
            _ => {}
        }
        walk_children(expr, &mut |child| {
            self.collect_declared_domains(child, var, out)
        });
    }

    fn check_c5_disjunct(
        &self,
        disjunct: &TlaExpr,
        next: &TlaOperator,
        node_set: &str,
        report: &mut CleanSubsetReport,
    ) {
        match disjunct {
            TlaExpr::Exists { vars, body } => {
                let over_node_set: Vec<&str> = vars
                    .iter()
                    .filter(|b| b.set.as_ref().map(|s| self.show(s)).as_deref() == Some(node_set))
                    .map(|b| b.var.as_str())
                    .collect();

                // Binding more than one node is *not* itself a violation. The
                // first is the acting node; the rest are parameters, and the
                // commonest thing a spec does with one is address a message:
                // Raft's `\E i, j \in Server : RequestVote(i, j)` reads only
                // `i`'s state and sends to `j`.
                //
                // Whether the action actually reaches into another node's state
                // is exactly what C2 decides, so this rule leaves it to C2
                // rather than rejecting a legitimate shape.
                if over_node_set.is_empty() {
                    // A disjunct quantifying only over value domains still has
                    // to reach a node action somewhere inside it -- unless it
                    // quantifies over the **network**, which is what an
                    // environment action looks like.
                    //
                    // `\E m \in messages : DropMessage(m)` is message loss: the
                    // framework performs it, no node does, and the subset
                    // contract has always permitted it ("or is an environment
                    // action (message delivery, loss, crash) that the framework
                    // -- not the projected node -- performs"). The rule was
                    // rejecting it because our own corpus has no lossy network
                    // and never exercised the shape; the fixture that found it
                    // came from the parallel Phase 52.M0 implementation.
                    // C4 has not run yet -- C5 goes first, because the node set
                    // it recovers is what every other rule is stated against --
                    // so the network is identified the same way C4 identifies it
                    // rather than read off the report.
                    let over_network = vars.iter().any(|b| {
                        b.set
                            .as_ref()
                            .map(|set| self.show(set))
                            .is_some_and(|name| {
                                self.module
                                    .variables
                                    .iter()
                                    .any(|v| *v == name && self.is_set_valued_network(v))
                            })
                    });
                    let inner = Self::quantified_sets(body, self);
                    if !over_network && !inner.contains(node_set) {
                        report.findings.push(self.finding(
                            CleanRule::C5,
                            Some(next),
                            format!(
                                "a `Next` disjunct never binds a node from `{node_set}`: `{}`. \
                                 Every step must be taken by some node, or be an environment \
                                 action the framework performs.",
                                self.show(disjunct)
                            ),
                        ));
                    }
                }
                for bound in vars {
                    if bound.set.is_none() {
                        report.findings.push(self.finding(
                            CleanRule::C5,
                            Some(next),
                            format!(
                                "`\\E {}` is unbounded in `Next`; the domain must be explicit \
                                 for the projection to know what it is projecting from.",
                                bound.var
                            ),
                        ));
                    }
                }
            }
            // A parameterless environment action (`Terminating`, message
            // delivery, crash) is allowed: the framework performs it.
            TlaExpr::Ident(_) => {}
            TlaExpr::OpApply { op, args } => {
                let named = self.show(op);
                let rendered = args.iter().map(|a| self.show(a)).collect::<Vec<_>>();
                report.findings.push(self.finding(
                    CleanRule::C5,
                    Some(next),
                    format!(
                        "`Next` applies `{named}` to fixed argument(s) ({}) instead of \
                         quantifying over `{node_set}`. Projection needs \
                         `\\E self \\in {node_set} : {named}(self, ...)`, otherwise the spec \
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
                        "`Next` has a disjunct that is neither a node action nor an \
                         environment action: `{}`.",
                        self.show(other)
                    ),
                ));
            }
        }
    }

    // ===================== C4: one designated network =====================

    /// Exactly one variable is the message network: a set of messages touched
    /// only by send (`net' = net \cup {m}`), receive (`\E m \in net`) and
    /// discard (`net' = net \ {m}`).
    ///
    /// The projection rewrites the network away entirely -- sends become an
    /// action's output messages and receives become an action's input, because
    /// the tla-rs framework owns delivery. That rewrite is only sound if the
    /// tool knows which variable is the network and that nothing else is done
    /// to it.
    fn check_c4(&self, report: &mut CleanSubsetReport) {
        let candidates: Vec<&String> = self
            .module
            .variables
            .iter()
            .filter(|v| self.is_set_valued_network(v))
            .collect();

        match candidates.len() {
            1 => {
                let net = candidates[0].clone();
                self.check_message_addressing(&net, report);
                report.network_variable = Some(net);
                return;
            }
            n if n > 1 => {
                let listed = candidates
                    .iter()
                    .map(|v| v.as_str())
                    .collect::<Vec<_>>()
                    .join(", ");
                report.findings.push(self.finding(
                    CleanRule::C4,
                    None,
                    format!(
                        "more than one variable looks like the network ({listed}). The \
                         projection turns exactly one variable into framework send/receive; \
                         merge them into a single message set, or say which one is the \
                         network and re-model the others as per-node state."
                    ),
                ));
                return;
            }
            _ => {}
        }

        // No variable is in the required shape. If one is *playing* the
        // network's role, say what is wrong with it rather than letting C1
        // report it as unexplained state.
        for var in &self.module.variables {
            if CONVENTIONAL_NETWORK_NAMES.contains(&var.as_str()) {
                report.network_near_miss = Some(var.clone());
                // Say what was actually observed. This message used to assert
                // "it is only ever updated with EXCEPT, so it is a
                // per-connection structure (a queue array)" on the sole
                // evidence that the variable had a conventional *name* -- and
                // that was false on three specs, including a spec whose only
                // update is `msgs' = {}` (zero EXCEPTs) and Jetpack's
                // `messages`, which the module never assigns at all. A
                // diagnostic that invents a mechanism is worse than one that
                // admits it does not know.
                let mut updates = Vec::new();
                for op in &self.module.operators {
                    self.collect_updates_of(&op.body, var, &mut updates);
                }
                let observed = if updates.is_empty() {
                    "this module never assigns it, so its shape cannot be read here".to_string()
                } else if updates
                    .iter()
                    .all(|rhs| matches!(rhs, TlaExpr::FnExcept { .. }))
                {
                    "it is only ever updated with EXCEPT, so it is a per-connection \
                     structure (a queue array) rather than one set"
                        .to_string()
                } else {
                    format!(
                        "its updates are not the send/receive/discard shapes ({})",
                        updates
                            .iter()
                            .map(|rhs| self.show(rhs))
                            .collect::<Vec<_>>()
                            .join("; ")
                    )
                };
                report.findings.push(self.finding(
                    CleanRule::C4,
                    None,
                    format!(
                        "`{var}` carries the messages but is not a message set: {observed}. \
                         Flatten it into a single set of messages tagged with sender and \
                         recipient. If it was a per-connection structure, note that doing so \
                         drops any ordering the original relied on -- that is a real semantic \
                         change and belongs in the rewrite notes."
                    ),
                ));
                return;
            }
        }
    }

    /// Whether `var` is a set-valued network.
    ///
    /// Two pieces of evidence are required, and both matter:
    ///
    /// - every update is `var \cup ...` / `var \ ...` applied to the variable
    ///   itself (send and discard), and
    /// - somewhere an action *receives* from it: `\E m \in var : ...`.
    ///
    /// The receive requirement is what separates a network from an ordinary
    /// shared set. Without it, LamportMutex's `crit` -- the set of nodes in the
    /// critical section, updated with exactly the same `\cup` / `\` idiom --
    /// gets designated as the network, which then suppresses the C1 finding
    /// that is the real problem with it.
    fn is_set_valued_network(&self, var: &str) -> bool {
        let mut updates = Vec::new();
        for op in &self.module.operators {
            self.collect_updates_of(&op.body, var, &mut updates);
        }
        if updates.is_empty() || !updates.iter().all(|rhs| self.is_set_delta_of(rhs, var)) {
            return false;
        }
        self.module
            .operators
            .iter()
            .any(|op| Self::has_receive_from(&op.body, var))
    }

    /// Whether `expr` receives from `var`: `\E m \in var : ...`.
    fn has_receive_from(expr: &TlaExpr, var: &str) -> bool {
        if let TlaExpr::Exists { vars, .. } = expr {
            if vars
                .iter()
                .any(|b| matches!(&b.set, Some(TlaExpr::Ident(name)) if name == var))
            {
                return true;
            }
        }
        // Testing that a particular *message* is in the network is also a
        // receive: `[type |-> "Prepared", rm |-> r] \in msgs` is how TwoPhase
        // reads its network.
        //
        // The element has to be a record. A network carries messages, and
        // messages are records; `p \in crit` tests membership of a node in an
        // ordinary shared set, and treating that as a receive would designate
        // LamportMutex's critical-section set as the network -- suppressing the
        // C1 finding that is the real problem with it.
        if let TlaExpr::BinOp {
            op: TlaBinOp::In,
            left,
            right,
        } = expr
        {
            if matches!(&**right, TlaExpr::Ident(name) if name == var)
                && matches!(&**left, TlaExpr::Record(_))
            {
                return true;
            }
        }
        let mut found = false;
        walk_children(expr, &mut |child| {
            found |= Self::has_receive_from(child, var);
        });
        found
    }

    /// Collect the right-hand sides of `var' = rhs`. The right-hand sides are
    /// cloned rather than borrowed: `walk_children` hands out children with an
    /// anonymous lifetime, and a handful of small expressions is not worth a
    /// second, lifetime-preserving walker.
    fn collect_updates_of(&self, expr: &TlaExpr, var: &str, out: &mut Vec<TlaExpr>) {
        if let TlaExpr::BinOp {
            op: TlaBinOp::Eq,
            left,
            right,
        } = expr
        {
            if matches!(&**left, TlaExpr::Prime(inner)
                if matches!(&**inner, TlaExpr::Ident(name) if name == var))
            {
                out.push((**right).clone());
            }
        }
        walk_children(expr, &mut |child| self.collect_updates_of(child, var, out));
    }

    /// Every message sent into the network must say who it is for.
    ///
    /// The addressing field is **inferred, not named**: it is whichever field
    /// the receive guard tests, since that is what the framework routes on
    /// (`docs/clean_tla_subset.md`, C4: receive is "guarded on `m` being
    /// addressed to `self`"). Hardcoding `dst` reported four clean corpus specs
    /// as violations -- Raft, EPaxos, dining philosophers and Jetpack all use
    /// the Raft-lineage `mdest`, and the name is not the point.
    ///
    /// If no receive guard tests any field of the message, the network is never
    /// addressed at all, which is the same defect stated at the other end.
    fn check_message_addressing(&self, net: &str, report: &mut CleanSubsetReport) {
        let mut fields: BTreeSet<String> = BTreeSet::new();
        for op in &self.module.operators {
            self.collect_addressing_fields(&op.body, net, &mut fields);
        }
        // The *tag* is not routing. A handler guards on both `m.dst = i` and
        // `m.type = "req"`, so the candidate set picks up `type` -- and since
        // the rule accepts a message carrying **any** candidate, and every
        // message carries its tag, it could never fail. That is the second
        // reason this rule never fired; following the call into the handler
        // was only the first.
        let fields: BTreeSet<String> = fields
            .into_iter()
            .filter(|f| !crate::tla::projection::TAG_FIELDS.contains(&f.as_str()))
            .collect();
        // More than one candidate means the guard tests several fields; any of
        // them routes, so requiring all would be wrong. Requiring *some* is the
        // honest weakening.
        // With no guard to read the routing field off, fall back to the
        // conventional spellings and check the *messages* instead.
        //
        // "No receive tests an addressing field" is NOT "no message is
        // addressed": once the projection replaces the network with framework
        // send/receive, delivery is by address and a handler has no reason to
        // re-test it. Reporting on the guard's absence flagged specs whose
        // messages carry a perfectly good `dst`. What C4 is owed is that the
        // message says who it is for, so that is what gets checked.
        let fields: BTreeSet<String> = if fields.is_empty() {
            crate::tla::projection::ROUTING_FIELDS
                .iter()
                .map(|f| (*f).to_string())
                .collect()
        } else {
            fields
        };

        let mut seen: BTreeSet<String> = BTreeSet::new();
        for op in &self.module.operators {
            let mut sends = Vec::new();
            self.collect_sends_into(&op.body, net, &mut sends);
            for send in sends {
                let mut messages = Vec::new();
                self.collect_sent_messages(&send, &mut messages);
                for (present, shown) in messages {
                    if present.iter().any(|f| fields.contains(f)) || !seen.insert(shown.clone()) {
                        continue;
                    }
                    let wanted = fields.iter().cloned().collect::<Vec<_>>().join("` or `");
                    report.findings.push(self.finding(
                        CleanRule::C4,
                        Some(op),
                        format!(
                            "the message `{shown}` sent into `{net}` carries no `{wanted}`, \
                             which is the field the receive guard routes on, so the \
                             framework cannot deliver it. Every message must say who it is \
                             for: the projection replaces `{net}` with framework \
                             send/receive."
                        ),
                    ));
                }
            }
        }
    }

    /// Fields of a message tested by a receive guard: the `f` in
    /// `\E m \in net : .. m.f = self ..`.
    fn collect_addressing_fields(&self, expr: &TlaExpr, net: &str, out: &mut BTreeSet<String>) {
        if let TlaExpr::Exists { vars, body } = expr {
            let bound: Vec<&str> = vars
                .iter()
                .filter(|b| b.set.as_ref().map(|s| self.show(s)).as_deref() == Some(net))
                .map(|b| b.var.as_str())
                .collect();
            if !bound.is_empty() {
                self.collect_guarded_fields(body, &bound, out);
            }
        }
        walk_children(expr, &mut |child| {
            self.collect_addressing_fields(child, net, out)
        });
    }

    /// `m.f = x` / `x = m.f` for a message variable `m`.
    ///
    /// **Follows a call.** Almost every spec writes
    /// `\E m \in msgs : Handler(i, m)` and puts the `m.dst = i` guard in the
    /// handler, so reading only the literal body of the `\E` found no
    /// addressing field at all -- and `check_message_addressing` returns early
    /// when the set is empty. The rule therefore never executed on any of the
    /// corpus's clean specs. It reports rather than being silently wrong: the
    /// projection refuses an unaddressed message with "broadcast message has
    /// no destination or no tag". But a lint that never runs makes `clean`
    /// claim more than was checked, and the diagnostic belongs here, where it
    /// can say what to do, rather than at translation.
    fn collect_guarded_fields(&self, expr: &TlaExpr, msg: &[&str], out: &mut BTreeSet<String>) {
        if let TlaExpr::OpApply { op, args } = expr {
            if let TlaExpr::Ident(callee) = &**op {
                for (i, arg) in args.iter().enumerate() {
                    let passes_msg = matches!(arg, TlaExpr::Ident(v) if msg.contains(&v.as_str()));
                    if !passes_msg {
                        continue;
                    }
                    if let Some(target) = self.operator(callee) {
                        if let Some(param) = target.params.get(i) {
                            // One level. A handler that itself dispatches to
                            // another handler is the composition shape, and
                            // `Receive`'s own body holds the guards there.
                            self.collect_guarded_fields(&target.body, &[param.name.as_str()], out);
                        }
                    }
                }
            }
        }
        if let TlaExpr::BinOp {
            op: TlaBinOp::Eq,
            left,
            right,
        } = expr
        {
            for (side, other) in [(left, right), (right, left)] {
                if let TlaExpr::RecordAccess { record, field } = &**side {
                    if !matches!(&**record, TlaExpr::Ident(v) if msg.contains(&v.as_str())) {
                        continue;
                    }
                    // Routing is a comparison against a plain *name* -- the
                    // acting node. `m.mdest = i` routes; `m.mdeps =
                    // leaderDeps[i]` is a payload agreement test, and taking it
                    // as a routing candidate made EPaxos report a message for
                    // carrying no `mdeps`. A node identity is a bare
                    // identifier; a state read is not.
                    if matches!(&**other, TlaExpr::Ident(_)) {
                        out.insert(field.clone());
                    }
                }
            }
        }
        walk_children(expr, &mut |child| {
            self.collect_guarded_fields(child, msg, out)
        });
    }

    /// The right-hand sides of `net' = net \cup <expr>`, which are the sends.
    fn collect_sends_into(&self, expr: &TlaExpr, net: &str, out: &mut Vec<TlaExpr>) {
        if let TlaExpr::BinOp {
            op: TlaBinOp::Eq,
            left,
            right,
        } = expr
        {
            if matches!(&**left, TlaExpr::Prime(inner)
                if matches!(&**inner, TlaExpr::Ident(v) if v == net))
            {
                self.collect_union_operands(right, net, out);
            }
        }
        walk_children(expr, &mut |child| self.collect_sends_into(child, net, out));
    }

    /// Operands of a `\cup` chain other than the network itself: the new
    /// messages. `net \ {m}` is a discard and contributes nothing.
    fn collect_union_operands(&self, expr: &TlaExpr, net: &str, out: &mut Vec<TlaExpr>) {
        match expr {
            TlaExpr::BinOp {
                op: TlaBinOp::Cup,
                left,
                right,
            } => {
                self.collect_union_operands(left, net, out);
                self.collect_union_operands(right, net, out);
            }
            TlaExpr::Ident(v) if v == net => {}
            other => out.push(other.clone()),
        }
    }

    /// Message records sent into `net`, as (record fields, how it was written).
    ///
    /// The contract requires each message to "carry enough addressing to say who
    /// it is for" (`docs/clean_tla_subset.md`, C4). A record with no destination
    /// field cannot be routed once P3 rewrites the network away, because the
    /// framework delivers by address and there is none.
    ///
    /// One level of indirection is resolved, because that is how the corpus
    /// writes messages: `msgs' = msgs \cup {Prepared(s, d)}` with
    /// `Prepared(s, d) == [type |-> "Prepared", src |-> s, dst |-> d]`. Anything
    /// deeper is left alone rather than guessed at.
    fn collect_sent_messages(&self, expr: &TlaExpr, out: &mut Vec<(Vec<String>, String)>) {
        match expr {
            TlaExpr::Record(fields) => {
                out.push((
                    fields.iter().map(|(n, _)| n.clone()).collect(),
                    self.show(expr),
                ));
            }
            // `Prepared(s, d)` -- resolve the operator and read its record body.
            TlaExpr::OpApply { op, .. } => {
                if let TlaExpr::Ident(name) = &**op {
                    if let Some(target) = self.operator(name) {
                        match &target.body {
                            TlaExpr::Record(fields) => {
                                out.push((
                                    fields.iter().map(|(n, _)| n.clone()).collect(),
                                    format!("{}(..)", name),
                                ));
                                return;
                            }
                            // A broadcast helper:
                            // `Broadcast(s, ..) == { Ctor(s, d, ..) : d \in .. }`.
                            // The messages are the comprehension's elements, and
                            // they were invisible here -- the body is not a
                            // `Record`, so this fell through to the walk below
                            // and picked up whatever record-shaped *argument*
                            // the call happened to take. EPaxos passes
                            // `Inst(i, crtInst[i])`, an instance identifier, and
                            // it was reported as an unaddressed message.
                            TlaExpr::SetMap { expr: body, .. }
                            | TlaExpr::SetMapMulti { expr: body, .. } => {
                                self.collect_sent_messages(body, out);
                                return;
                            }
                            _ => {}
                        }
                    }
                }
                // An unresolved call: its arguments are not messages, so there
                // is nothing here to look at. Descending into them is what
                // produced the false positive above.
                if !matches!(&**op, TlaExpr::Ident(name) if self.operator(name).is_some()) {
                    walk_children(expr, &mut |child| self.collect_sent_messages(child, out));
                }
            }
            other => walk_children(other, &mut |child| self.collect_sent_messages(child, out)),
        }
    }

    /// Whether `expr` is `var` modified only by `\cup` / `\` (set difference),
    /// possibly nested: `(net \cup {m}) \ {old}`.
    fn is_set_delta_of(&self, expr: &TlaExpr, var: &str) -> bool {
        match expr {
            TlaExpr::Ident(name) => name == var,
            TlaExpr::BinOp {
                op: TlaBinOp::Cup | TlaBinOp::Setminus | TlaBinOp::Cap,
                left,
                right,
            } => self.is_set_delta_of(left, var) || self.is_set_delta_of(right, var),
            TlaExpr::IfThenElse {
                then_expr,
                else_expr,
                ..
            } => self.is_set_delta_of(then_expr, var) && self.is_set_delta_of(else_expr, var),
            _ => false,
        }
    }

    // ===================== C3: no history variables =====================

    /// A variable that exists only to record the past or to aggregate across
    /// nodes for the benefit of an invariant.
    ///
    /// It is recognised by what its update does: gathering per-node state over
    /// the whole node set, as in Raft's
    /// `allLogs' = allLogs \cup {log[i] : i \in Server}`. Such a variable is
    /// global by construction and has no runtime meaning -- the implementation
    /// would maintain state the protocol never consults.
    fn check_c3(&self, report: &mut CleanSubsetReport) {
        // C3 aggregates over per-node variables. With none identified it has
        // nothing to look at, and saying nothing then reports as "executed and
        // found nothing" -- C2 declares itself skipped in exactly this state
        // and C3 did not. `skipped_rules` exists so a low violation count is
        // not read as "nearly clean"; a rule that quietly did nothing is the
        // case it was built for.
        if report.node_set.is_some() && report.per_node_variables.is_empty() {
            report.skipped_rules.push((
                CleanRule::C3,
                "no per-node variables were identified, so there is nothing an \
                 aggregation over the node set could aggregate"
                    .to_string(),
            ));
            return;
        }

        let Some(node_set) = report.node_set.clone() else {
            report.skipped_rules.push((
                CleanRule::C3,
                "no node set was identified, so there is nothing to state \
                 per-node updates against"
                    .to_string(),
            ));
            return;
        };
        let per_node: BTreeSet<&str> = report
            .per_node_variables
            .iter()
            .map(|s| s.as_str())
            .collect();

        for var in report.global_variables.clone() {
            let mut updates = Vec::new();
            for op in &self.module.operators {
                self.collect_updates_of(&op.body, &var, &mut updates);
            }
            let aggregating = updates
                .iter()
                .any(|rhs| self.aggregates_over_nodes(rhs, &node_set, &per_node));
            if aggregating {
                report.findings.push(self.finding(
                    CleanRule::C3,
                    None,
                    format!(
                        "`{var}` is a history variable: it is built by gathering per-node \
                         state over all of `{node_set}`. No node can maintain it, and the \
                         protocol never consults it -- it exists for the invariants. Delete \
                         it and restate those invariants over reachable state, recording the \
                         change in the rewrite notes."
                    ),
                ));
            }
        }
    }

    /// Whether `expr` gathers per-node state over the node set: a comprehension
    /// or quantifier bound to the node set whose body reads a per-node variable
    /// at that bound variable.
    fn aggregates_over_nodes(
        &self,
        expr: &TlaExpr,
        node_set: &str,
        per_node: &BTreeSet<&str>,
    ) -> bool {
        let bound_over_nodes = match expr {
            TlaExpr::SetMap {
                expr: body,
                var,
                set,
            } => {
                if self.show(set) == node_set {
                    Some((var.clone(), &**body))
                } else {
                    None
                }
            }
            TlaExpr::SetFilter { var, set, filter } => {
                if self.show(set) == node_set {
                    Some((var.clone(), &**filter))
                } else {
                    None
                }
            }
            TlaExpr::Forall { vars, body } | TlaExpr::Exists { vars, body } => vars
                .iter()
                .find(|b| b.set.as_ref().map(|s| self.show(s)) == Some(node_set.to_string()))
                .map(|b| (b.var.clone(), &**body)),
            _ => None,
        };

        if let Some((bound_var, body)) = bound_over_nodes {
            let mut reads = Vec::new();
            self.collect_reads_at(body, &bound_var, per_node, &mut reads);
            if !reads.is_empty() {
                return true;
            }
        }

        let mut found = false;
        walk_children(expr, &mut |child| {
            found |= self.aggregates_over_nodes(child, node_set, per_node);
        });
        found
    }

    /// Collect `x[bound_var]` reads of per-node variables.
    fn collect_reads_at(
        &self,
        expr: &TlaExpr,
        bound_var: &str,
        per_node: &BTreeSet<&str>,
        out: &mut Vec<String>,
    ) {
        if let TlaExpr::FnApply { func, arg } = expr {
            let base: &TlaExpr = match &**func {
                TlaExpr::Prime(inner) => inner,
                other => other,
            };
            if let TlaExpr::Ident(var) = base {
                if per_node.contains(var.as_str())
                    && matches!(&**arg, TlaExpr::Ident(a) if a == bound_var)
                {
                    out.push(var.clone());
                }
            }
        }
        walk_children(expr, &mut |child| {
            self.collect_reads_at(child, bound_var, per_node, out)
        });
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
            report.skipped_rules.push((
                CleanRule::C2,
                if report.node_set.is_none() {
                    "no node set was identified, so cross-node reads cannot be \
                     recognised"
                        .to_string()
                } else {
                    "no per-node variables were identified, so there is nothing \
                     a cross-node read could read"
                        .to_string()
                },
            ));
            return;
        }
        let node_set_name = report
            .node_set
            .clone()
            .expect("guarded above: C2 returns early without a node set");
        // The network is exempt: reading messages other nodes sent is what a
        // network is for, and a malformed one is C4's single decision, not one
        // C2 finding per read of it.
        let per_node: BTreeSet<&str> = report
            .per_node_variables
            .iter()
            .map(|s| s.as_str())
            .filter(|v| {
                report.network_variable.as_deref() != Some(v)
                    && report.network_near_miss.as_deref() != Some(v)
            })
            .collect();

        for (op_name, node_param) in self.node_parameterized_operators() {
            let Some(op) = self.operator(&op_name) else {
                continue;
            };
            let mut writes = Vec::new();
            self.collect_whole_array_writes(&op.body, &per_node, &node_set_name, &mut writes);
            let _ = &node_set_name;
            writes.sort();
            writes.dedup();
            for var in writes {
                report.findings.push(self.finding(
                    CleanRule::C2,
                    Some(op),
                    format!(
                        "assigns `{var}` as a whole array -- one step that updates every \
                         node at once. A node taking this step can only write \
                         `{var}[{node_param}]`. Only `Init` may build the whole function."
                    ),
                ));
            }

            let mut whole = Vec::new();
            self.collect_whole_array_reads(&op.body, &per_node, &mut whole);
            whole.sort();
            whole.dedup();
            for var in whole {
                report.findings.push(self.finding(
                    CleanRule::C2,
                    Some(op),
                    format!(
                        "reads `{var}` as a whole array -- every node's state at once, \
                         with no index. A node taking this step can only read \
                         `{var}[{node_param}]`. Aggregate it the way the algorithm \
                         actually learns it: a message per node, and a local tally."
                    ),
                ));
            }

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

        // `Next` may take its step *inline* rather than calling an action:
        // `Next == \E p \in Proc : x' = [x EXCEPT ![p] = x[p + 1]]`. The loop
        // above iterates `node_parameterized_operators`, which records only
        // *callees*, so a spec written this way had C2 -- the rule the whole
        // subset exists for -- run on nothing at all and report `clean`. The
        // identical read written as `Step(p)` was reported.
        //
        // The walk stops at a call to an operator this module defines: that
        // body is covered by the loop above, and descending would report the
        // same read twice under two names.
        if let Some(next) = self.next_relation() {
            let expanded = self.expand_action_groups(&next.body);
            let node_set = report.node_set.clone().unwrap_or_default();
            for disjunct in flatten_disjunction(&expanded) {
                let TlaExpr::Exists { vars, body } = disjunct else {
                    continue;
                };
                let Some(bound) = vars
                    .iter()
                    .find(|b| b.set.as_ref().map(|set| self.show(set)) == Some(node_set.clone()))
                else {
                    continue;
                };
                let mut reads = Vec::new();
                self.collect_inline_foreign_reads(body, &bound.var, &per_node, &mut reads);
                reads.sort();
                reads.dedup();
                for (var, index) in reads {
                    let node_param = &bound.var;
                    report.findings.push(self.finding(
                        CleanRule::C2,
                        Some(next),
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

        let owned: Vec<String> = per_node.iter().map(|v| v.to_string()).collect();
        drop(per_node);
        self.check_parameterless_disjuncts(&owned, report);
    }

    /// A `Next` disjunct that is a bare name -- `\/ Terminating` -- is permitted
    /// as an environment action the framework performs. C5 accepted it without
    /// looking inside, which is the unchecked prose a linter exists to replace.
    ///
    /// A parameterless action has no `self`, so **no** index into per-node state
    /// is the legitimate one: `\A i \in Proc : pc[i] = "Done"` asks every node
    /// at once, and no single node can evaluate it. Frame conditions are exempt
    /// as everywhere else, which is what keeps `UNCHANGED <<..>>` clean.
    fn check_parameterless_disjuncts(
        &self,
        per_node_owned: &[String],
        report: &mut CleanSubsetReport,
    ) {
        let per_node: BTreeSet<&str> = per_node_owned.iter().map(|v| v.as_str()).collect();
        let per_node = &per_node;
        let Some(next) = self.next_relation() else {
            return;
        };
        let expanded = self.expand_action_groups(&next.body);
        for disjunct in flatten_disjunction(&expanded) {
            let TlaExpr::Ident(name) = disjunct else {
                continue;
            };
            let Some(op) = self.operator(name) else {
                // A `Next` disjunct naming an operator the module does not
                // define. C5 blesses a bare-name disjunct without inspection --
                // it is how an environment action the framework performs is
                // written -- so without this the name is simply accepted and
                // the verdict is `clean`.
                //
                // For this project that is the shape a *failed composition*
                // takes: a name `resolve_module_file` did not bring in looks
                // exactly like an environment action. A whole protocol layer
                // can go missing and the linter says nothing.
                report.findings.push(self.finding(
                    CleanRule::C5,
                    Some(next),
                    format!(
                        "`Next` names `{name}`, which this module does not \
                         define. A bare name in `Next` is read as an \
                         environment action the framework performs, so an \
                         undefined one is accepted rather than reported -- and \
                         if it came from another module, the composition did \
                         not resolve and everything behind that name is \
                         missing from this measurement."
                    ),
                ));
                continue;
            };
            if !op.params.is_empty() {
                continue;
            }
            // Inlined first: a 0-ary disjunct's guard is usually one call
            // away. `Terminating == /\ Done /\ UNCHANGED pc` with
            // `Done == \A i \in Proc : pc[i] = 1` reads every node's `pc`, and
            // reading only `Terminating`'s literal body found nothing at all --
            // one level of naming hid the whole guard. This rule exists
            // *because* C5 blesses bare-name disjuncts without inspection, so
            // inheriting the same blind spot one call deeper defeated it.
            let body = self.inline_nullary_calls(&op.body, 0);
            let mut touched = Vec::new();
            self.collect_whole_array_reads(&body, per_node, &mut touched);
            let mut indexed = Vec::new();
            // No parameter names a node here, so every index is foreign.
            self.collect_foreign_reads(&body, "", per_node, &mut indexed);
            touched.extend(
                indexed
                    .into_iter()
                    .map(|(var, index)| format!("{var}[{index}]")),
            );
            touched.sort();
            touched.dedup();
            for what in touched {
                report.findings.push(self.finding(
                    CleanRule::C2,
                    Some(op),
                    format!(
                        "`{name}` is a `Next` disjunct with no node parameter, so the \
                         framework performs it -- but it reads `{what}`, which is some \
                         node's state. There is no `self` here for the read to be about, \
                         and no single node can evaluate it. Either give the action a node \
                         parameter, or state the condition in something a node can observe \
                         locally."
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
        let Some(next) = self.next_relation() else {
            return found;
        };

        // Seed from `\E self \in Node : ... Action(self) ...`, over the
        // **expanded** `Next`.
        //
        // A spec that groups its disjuncts behind 0-ary names -- `Next ==
        // \/ CommandLeaderAction \/ ReplicaAction`, which is how EPaxos is
        // written -- puts the quantifier one level down. Seeding from the raw
        // body finds no `Exists`, returns an empty map, and **C2 then iterates
        // over nothing**: the rule the whole subset exists for is silently
        // disabled on exactly the specs most likely to need it. `check_c5`
        // was taught to expand; this was not, and nothing caught the
        // difference because the corpus's `clean.tla` rewrites all quantify
        // directly in `Next`.
        let expanded = self.expand_action_groups(&next.body);
        // Only a binder that ranges over the **node set** names a node.
        //
        // Seeding from every binder makes `\E m \in DOMAIN messages :
        // ServerReceive(m)` declare `m` -- a *message* -- to be the acting
        // node, and C2 then reads every legitimate `jepoch[i]` in the handlers
        // reachable from it as "another node's state". On Jetpack's composition
        // that alone accounted for most of 31 C2 findings, all of them false.
        let node_set = self.infer_node_set(next, &expanded);
        let mut seeds = Vec::new();
        for disjunct in flatten_disjunction(&expanded) {
            if let TlaExpr::Exists { vars, body } = disjunct {
                for bound in vars {
                    let over_node_set = match (&bound.set, &node_set) {
                        (Some(set), Some(ns)) => self.show(set) == *ns,
                        // With no node set identified, C1/C2/C3 do not run
                        // anyway; keeping the old permissive behaviour here
                        // only produces findings nothing will report.
                        _ => false,
                    };
                    if over_node_set {
                        seeds.push((bound.var.clone(), body));
                    }
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

    /// An expression with calls to 0-ary operators replaced by their bodies.
    ///
    /// Bounded: an operator naming itself, directly or through a chain, would
    /// otherwise not terminate, and three levels is well past what any spec in
    /// the corpus writes.
    fn inline_nullary_calls(&self, expr: &TlaExpr, depth: usize) -> TlaExpr {
        if depth > 3 {
            return expr.clone();
        }
        if let TlaExpr::Ident(name) = expr {
            if let Some(op) = self.operator(name) {
                if op.params.is_empty() {
                    return self.inline_nullary_calls(&op.body, depth + 1);
                }
            }
        }
        if let TlaExpr::BinOp { op, left, right } = expr {
            return TlaExpr::BinOp {
                op: *op,
                left: Box::new(self.inline_nullary_calls(left, depth)),
                right: Box::new(self.inline_nullary_calls(right, depth)),
            };
        }
        expr.clone()
    }

    /// The parameter this operator updates its own state at: the `p` of
    /// `x' = [x EXCEPT ![p] = ..]`.
    ///
    /// In the clean subset that *is* the acting node -- C1 says state is
    /// per-node and a node writes its own -- so it is the right answer when
    /// several parameters could be the node and argument order would otherwise
    /// decide. `None` when the body writes at no parameter or at more than one,
    /// which is not a tie this can break.
    fn parameter_written_at(&self, op: &TlaOperator) -> Option<String> {
        let params: BTreeSet<&str> = op.params.iter().map(|p| p.name.as_str()).collect();
        let mut found: BTreeSet<String> = BTreeSet::new();
        fn walk(expr: &TlaExpr, params: &BTreeSet<&str>, out: &mut BTreeSet<String>) {
            if let TlaExpr::BinOp {
                op: TlaBinOp::Eq,
                left,
                right,
            } = expr
            {
                if matches!(&**left, TlaExpr::Prime(_)) {
                    if let TlaExpr::FnExcept { updates, .. } = &**right {
                        for update in updates {
                            if let Some(crate::tla::ast::TlaExceptPath::Index(TlaExpr::Ident(
                                name,
                            ))) = update.path.first()
                            {
                                if params.contains(name.as_str()) {
                                    out.insert(name.clone());
                                }
                            }
                        }
                    }
                }
            }
            walk_children(expr, &mut |child| walk(child, params, out));
        }
        walk(&op.body, &params, &mut found);
        (found.len() == 1).then(|| found.into_iter().next().expect("len checked"))
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
            // First-wins, EXCEPT that a parameter the body actually updates
            // *at* wins over one that merely arrived first.
            //
            // With `\E i, j \in Proc : Own(j, i)` the seeds are visited in
            // binder order, so `i` reached argument 1 and designated the
            // callee's second parameter "the node" -- and `Own(a, b) == x' =
            // [x EXCEPT ![a] = ..]`, which touches only `a`, was reported for a
            // cross-node read of `x[a]`. Swapping the two arguments at the call
            // site flipped the verdict on an operator that had not changed.
            //
            // In the clean subset the acting node is the one whose own state
            // the action updates, so that is the tie-break rather than
            // argument order.
            let writes_at = self.parameter_written_at(op);
            match found.get(&callee) {
                Some(existing) if Some(existing.as_str()) == writes_at.as_deref() => {}
                _ if writes_at.as_deref() == Some(param.name.as_str()) => {
                    found.insert(callee, param.name.clone());
                }
                Some(_) => {}
                None => {
                    found.insert(callee, param.name.clone());
                }
            }
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
    /// Per-node variables assigned as a whole array: `x' = [i \in Node |-> ..]`.
    ///
    /// The contract allows this only in `Init` (`docs/clean_tla_subset.md`, C2:
    /// "Writing the whole array is out ... a step that updates every node. Only
    /// `Init` may do it"). Scanning only the operators reachable from `Next` is
    /// what exempts `Init`, so the exemption needs no special case.
    ///
    /// The constructor must be the **direct** right-hand side. A constructor
    /// over the node set nested inside an `EXCEPT` updates one node's inner
    /// table -- Lamport-mutex's `[sendSeq EXCEPT ![s] = [d \in Proc |-> ..]]`
    /// advances every *destination* counter within node `s`, which is a
    /// single-node step.
    ///
    /// Known limit: a spec that hides the constructor behind a helper
    /// (`x' = BuildAll(s)`) is not caught. Following returned values would need
    /// the value analysis C2's indexed branch also lacks; not flagging is the
    /// safe direction, and this comment is the record that it is a gap rather
    /// than a decision.
    fn collect_whole_array_writes(
        &self,
        expr: &TlaExpr,
        per_node: &BTreeSet<&str>,
        node_set: &str,
        out: &mut Vec<String>,
    ) {
        if let TlaExpr::BinOp { op, left, right } = expr {
            if matches!(op, TlaBinOp::Eq) {
                if let TlaExpr::Prime(inner) = &**left {
                    if let TlaExpr::Ident(v) = &**inner {
                        if per_node.contains(v.as_str()) {
                            if let TlaExpr::FnConstruct { domain, .. } = &**right {
                                if self.show(domain) == node_set {
                                    out.push(v.clone());
                                }
                            }
                        }
                    }
                }
            }
        }
        walk_children(expr, &mut |child| {
            self.collect_whole_array_writes(child, per_node, node_set, out)
        });
    }

    /// Per-node variables read *as a whole array* -- named without an index.
    ///
    /// `Cardinality(state)` observes every node at once, which the contract
    /// calls a cross-node read even though no index appears
    /// (`docs/clean_tla_subset.md`, C2: "Reading the whole array is a cross-node
    /// read, even without an index").
    ///
    /// Frame conditions are exempt, and that exemption is the whole difficulty:
    /// `x' = x` names `x` bare but carries no information across nodes, and P5
    /// regenerates it anyway. So the right-hand side of an equality whose left
    /// side is that same variable primed is not a read, and neither is anything
    /// under `UNCHANGED`.
    fn collect_whole_array_reads(
        &self,
        expr: &TlaExpr,
        per_node: &BTreeSet<&str>,
        out: &mut Vec<String>,
    ) {
        match expr {
            // `x' = x` and `x' = [x EXCEPT ..]`: the frame/update form. The
            // left side is not a read at all, and a bare mention of the same
            // variable on the right is the frame condition.
            TlaExpr::BinOp {
                op: TlaBinOp::Eq,
                left,
                right,
            } => {
                if let TlaExpr::Prime(inner) = &**left {
                    if let TlaExpr::Ident(v) = &**inner {
                        self.collect_whole_array_reads_skipping(right, per_node, v, out);
                        return;
                    }
                }
                self.collect_whole_array_reads(left, per_node, out);
                self.collect_whole_array_reads(right, per_node, out);
            }
            // `f[i]` reads one element; C2's indexed check owns it. Descend into
            // the index but not into the function position, or every indexed
            // read would also count as a whole-array read.
            TlaExpr::FnApply { func, arg } => {
                if !matches!(
                    Self::index_base(func),
                    Some(TlaExpr::Ident(v)) if per_node.contains(v.as_str())
                ) {
                    self.collect_whole_array_reads(func, per_node, out);
                }
                self.collect_whole_array_reads(arg, per_node, out);
            }
            // `[f EXCEPT ![i] = v]` names `f` bare but touches exactly entry
            // `i`; it is the ordinary per-node update, not a whole-array read.
            // Counting the base flagged three of Lamport-mutex's helpers
            // (`AdvanceAll`, `AdvanceOne`, `Accept`) on a spec that is clean.
            // The forbidden whole-array *write* is a function constructor over
            // the node set, `x' = [i \in Node |-> ..]`, which is a different
            // shape and is not this.
            TlaExpr::FnExcept { func, updates } => {
                if !matches!(&**func, TlaExpr::Ident(v) if per_node.contains(v.as_str())) {
                    self.collect_whole_array_reads(func, per_node, out);
                }
                for update in updates {
                    for step in &update.path {
                        if let crate::tla::ast::TlaExceptPath::Index(idx) = step {
                            self.collect_whole_array_reads(idx, per_node, out);
                        }
                    }
                    self.collect_whole_array_reads(&update.value, per_node, out);
                }
            }
            TlaExpr::Unchanged(_) => {}
            TlaExpr::Ident(v) if per_node.contains(v.as_str()) => out.push(v.clone()),
            other => walk_children(other, &mut |child| {
                self.collect_whole_array_reads(child, per_node, out)
            }),
        }
    }

    /// As above, but `skip` names the variable whose bare mention is this
    /// expression's frame condition.
    fn collect_whole_array_reads_skipping(
        &self,
        expr: &TlaExpr,
        per_node: &BTreeSet<&str>,
        skip: &str,
        out: &mut Vec<String>,
    ) {
        if matches!(expr, TlaExpr::Ident(v) if v == skip) {
            return;
        }
        let mut found = Vec::new();
        self.collect_whole_array_reads(expr, per_node, &mut found);
        out.extend(found.into_iter().filter(|v| v != skip));
    }

    /// The variable a function application indexes into, unpriming it.
    fn index_base(func: &TlaExpr) -> Option<&TlaExpr> {
        match func {
            TlaExpr::Prime(inner) => Some(inner),
            other => Some(other),
        }
    }

    /// `collect_foreign_reads`, but stopping at a call to an operator this
    /// module defines -- that body is checked in its own right, and descending
    /// would report the same read twice.
    fn collect_inline_foreign_reads(
        &self,
        expr: &TlaExpr,
        node_param: &str,
        per_node: &BTreeSet<&str>,
        out: &mut Vec<(String, String)>,
    ) {
        if let TlaExpr::OpApply { op, .. } = expr {
            if matches!(&**op, TlaExpr::Ident(name) if self.operator(name).is_some()) {
                return;
            }
        }
        // The same test `collect_foreign_reads` makes, applied at this node
        // only; the recursion below is what differs.
        if let TlaExpr::FnApply { func, arg } = expr {
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
            self.collect_inline_foreign_reads(child, node_param, per_node, out)
        });
    }

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
            report.skipped_rules.push((
                CleanRule::C1,
                "no node set was identified, so variable domains cannot be \
                 compared against it"
                    .to_string(),
            ));
            return;
        };

        let mut per_node = Vec::new();
        let mut global = Vec::new();
        for var in &self.module.variables {
            // The network is state by design and is exempt: C4 owns it, and the
            // projection replaces it with framework send/receive.
            if report.network_variable.as_deref() == Some(var.as_str()) {
                continue;
            }
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
            // Anything else: the full walk, not a hand-rolled list of the
            // shapes that happened to come up.
            //
            // `collect_declared_domains` answers the same question -- "is `x`
            // declared over `S`?" -- with `walk_children`, and this covered only
            // BinOp / LetIn / Forall / Exists. When they disagreed the node set
            // was found and no variable was per-node, and C1 then reported
            // "this spec models shared state rather than a distributed
            // protocol" about a spec that is per-node: a false diagnosis of the
            // *spec* for a gap in the *linter*. `TypeOK == IF TRUE THEN x \in
            // [Proc -> Nat] ELSE TRUE` is enough to show it.
            other => {
                let mut found = false;
                walk_children(other, &mut |child| {
                    found |= self.states_per_node(child, var, node_set);
                });
                found
            }
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
        TlaExpr::Lambda { body, .. } => f(body),
        TlaExpr::SetMapMulti { expr, bindings } => {
            f(expr);
            for binding in bindings {
                if let Some(set) = &binding.set {
                    f(set);
                }
            }
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

/// Find the action named inside `[][Action]_vars`, which the parser desugars to
/// `Always(Action \/ UNCHANGED vars)`.
fn find_boxed_action(expr: &TlaExpr, out: &mut Option<String>) {
    if out.is_some() {
        return;
    }
    if let TlaExpr::Always(inner) = expr {
        if let TlaExpr::BinOp {
            op: TlaBinOp::Or,
            left,
            ..
        } = &**inner
        {
            if let TlaExpr::Ident(name) = &**left {
                *out = Some(name.clone());
                return;
            }
        }
    }
    walk_children(expr, &mut |child| find_boxed_action(child, out));
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
/// The operators that act on behalf of a node, mapped to the name that node
/// goes by inside each one.
///
/// C2 needs this to know which parameter is the node; the projection pass needs
/// the same answer to know which parameter to remove. Sharing it keeps the two
/// from disagreeing about what an action is.
pub fn node_parameterized_operators(module: &TlaModule) -> BTreeMap<String, String> {
    LintContext::new(module).node_parameterized_operators()
}

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
    // Implemented but not run on this module. Without this a reader cannot tell
    // a low violation count that means "clean" from one that means "barely
    // anything executed".
    let rules_skipped = report
        .skipped_rules
        .iter()
        .map(|(r, why)| {
            format!(
                r#"{{"rule":"{}","reason":"{}"}}"#,
                r.as_str(),
                escape_json(why)
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let rules_executed = RULES_CHECKED
        .iter()
        .filter(|r| !report.skipped_rules.iter().any(|(s, _)| s == *r))
        .map(|r| format!(r#""{}""#, r.as_str()))
        .collect::<Vec<_>>()
        .join(",");

    format!(
        r#"{{"clean":{},"violations":{},"rules_checked":[{rules_checked}],"rules_executed":[{rules_executed}],"rules_skipped":[{rules_skipped}],"rules_not_implemented":[{rules_unchecked}],"node_set":{},"network_variable":{},"per_node_variables":[{}],"global_variables":[{}],"findings":[{}]}}"#,
        report.is_clean(),
        report.violations(),
        quoted(&report.node_set),
        quoted(&report.network_variable),
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

/// Every operator name applied or referenced in an expression.
fn collect_called_names(expr: &TlaExpr, out: &mut Vec<String>) {
    match expr {
        TlaExpr::OpApply { op, .. } => {
            if let TlaExpr::Ident(name) = &**op {
                out.push(name.clone());
            }
        }
        TlaExpr::Ident(name) => out.push(name.clone()),
        _ => {}
    }
    walk_children(expr, &mut |child| collect_called_names(child, out));
}

/// Whether a body stands for a *group* of actions rather than for one action.
///
/// The distinction decides what gets inlined into `Next`. `ReplicaAction ==
/// \E replica \in Replicas : ...` and `CommandLeaderAction == \/ .. \/ ..`
/// are groups, and analysing them unexpanded loses the node binder. A leaf
/// like `Terminating == pc' = pc` is one action with a name, and inlining it
/// would replace a recognisable environment action with a bare state formula
/// -- which C5 would then reject, because a name is exactly how a spec says
/// "this disjunct is deliberate".
fn groups_actions(body: &TlaExpr) -> bool {
    matches!(
        body,
        TlaExpr::Exists { .. }
            | TlaExpr::BinOp {
                op: TlaBinOp::Or,
                ..
            }
    )
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

    /// Phase 52: `clean_distance` degraded to silence. C1, C2 and C3 all need a
    /// node set and return early without one, so a spec the linter understands
    /// *less* ran fewer rules, reported fewer findings, and scored as *cleaner*.
    /// Jetpack's original reports 2 violations with three rules never executed --
    /// reading that as "nearly clean" is precisely the mistake.
    #[test]
    fn records_which_rules_did_not_run_when_the_node_set_is_unknown() {
        let source = r#"---- MODULE Test ----
VARIABLES clock
Init == clock = 0
Next == clock' = clock + 1
===="#;
        let report = lint(source);
        let skipped: Vec<CleanRule> = report.skipped_rules.iter().map(|(r, _)| *r).collect();
        assert!(
            skipped.contains(&CleanRule::C1)
                && skipped.contains(&CleanRule::C2)
                && skipped.contains(&CleanRule::C3),
            "C1/C2/C3 all need a node set and must say they did not run: {:?}",
            report.skipped_rules
        );
        for (rule, why) in &report.skipped_rules {
            assert!(
                !why.is_empty(),
                "{} must say *why* it did not run",
                rule.as_str()
            );
        }
    }

    #[test]
    fn a_fully_understood_spec_skips_nothing() {
        let source = r#"---- MODULE Test ----
VARIABLES clock
TypeOK == clock \in [Proc -> Nat]
Step(p) == clock' = [clock EXCEPT ![p] = clock[p] + 1]
Next == \E p \in Proc : Step(p)
===="#;
        let report = lint(source);
        assert!(
            report.skipped_rules.is_empty(),
            "with a node set every rule runs: {:?}",
            report.skipped_rules
        );
        assert!(report.is_clean(), "got {:?}", report.findings);
    }

    #[test]
    fn json_separates_rules_that_ran_from_rules_that_did_not() {
        let source = r#"---- MODULE Test ----
VARIABLES clock
Init == clock = 0
Next == clock' = clock + 1
===="#;
        let json = report_to_json(&lint(source));
        assert!(json.contains(r#""rules_executed""#), "{json}");
        assert!(json.contains(r#""rules_skipped""#), "{json}");
        // a consumer reading only `violations` cannot tell the difference; the
        // two lists are what make the number interpretable
        assert!(json.contains(r#""rule":"C1","reason":"#), "{json}");
    }

    /// Phase 52: a bare-`Ident` disjunct in `Next` was whitelisted with no
    /// inspection of its body. That is what blessed `t0_01_simple`'s
    /// `Terminating`, whose guard `\A i \in Proc : pc[i] = "Done"` reads every
    /// node's `pc` -- and whose own golden header already documented it as *"one
    /// node cannot observe that, so the guard is not projectable"*. Unchecked
    /// prose is exactly what a linter exists to replace.
    #[test]
    fn rejects_a_parameterless_disjunct_that_reads_node_state() {
        let source = r#"---- MODULE Test ----
EXTENDS Naturals
VARIABLES pc
TypeOK == pc \in [Proc -> Nat]
Step(p) == pc' = [pc EXCEPT ![p] = 1]
Terminating == /\ \A i \in Proc : pc[i] = 1
               /\ UNCHANGED <<pc>>
Next == \/ \E p \in Proc : Step(p)
        \/ Terminating
===="#;
        let report = lint(source);
        assert!(
            report
                .findings
                .iter()
                .any(|f| f.rule == CleanRule::C2 && f.message.contains("no node parameter")),
            "a parameterless disjunct reading node state must be reported: {:?}",
            report.findings
        );
    }

    /// The same disjunct guarded on its own node is projectable, which is the
    /// rewrite `t0_01_simple/clean.tla` now carries. Behaviour is unchanged:
    /// `[][Next]_vars` already permits stuttering.
    #[test]
    fn a_per_node_stuttering_action_is_fine() {
        let source = r#"---- MODULE Test ----
EXTENDS Naturals
VARIABLES pc
TypeOK == pc \in [Proc -> Nat]
Step(p) == pc' = [pc EXCEPT ![p] = 1]
Terminating(self) == /\ pc[self] = 1
                     /\ UNCHANGED <<pc>>
Next == \E p \in Proc : Step(p) \/ Terminating(p)
===="#;
        let report = lint(source);
        assert!(report.is_clean(), "got {:?}", report.findings);
    }

    /// A genuine environment action -- one the framework performs, touching no
    /// node state -- must stay permitted. Rejecting these would break the
    /// contract's own allowance for message delivery, loss and crash.
    #[test]
    fn a_parameterless_action_touching_no_node_state_stays_permitted() {
        let source = r#"---- MODULE Test ----
EXTENDS Naturals
VARIABLES pc, msgs
TypeOK == pc \in [Proc -> Nat]
Step(p) == /\ pc' = [pc EXCEPT ![p] = 1]
           /\ msgs' = msgs \cup {[dst |-> p]}
Recv(p) == \E m \in msgs : m.dst = p /\ msgs' = msgs \ {m} /\ UNCHANGED <<pc>>
DropMessage == \E m \in msgs : msgs' = msgs \ {m} /\ UNCHANGED <<pc>>
Next == \/ \E p \in Proc : Step(p) \/ Recv(p)
        \/ DropMessage
===="#;
        let report = lint(source);
        assert!(
            !report
                .findings
                .iter()
                .any(|f| f.message.contains("no node parameter")),
            "message loss touches only the network: {:?}",
            report.findings
        );
    }

    /// Phase 52: "each message carries enough addressing to say who it is for"
    /// (`docs/clean_tla_subset.md`, C4). A message with no destination cannot be
    /// routed once P3 replaces the network with framework send/receive.
    #[test]
    fn rejects_a_message_with_no_addressing_field() {
        let source = r#"---- MODULE Test ----
EXTENDS Naturals
VARIABLES msgs, state
TypeOK == state \in [Proc -> Nat]
Ping(s) == [kind |-> "ping", src |-> s]
Send(s) == msgs' = msgs \cup {Ping(s)}
Recv(p) == \E m \in msgs : /\ m.dst = p
                           /\ state' = [state EXCEPT ![p] = 1]
                           /\ msgs' = msgs \ {m}
Next == \E p \in Proc : Send(p) \/ Recv(p)
===="#;
        let report = lint(source);
        assert!(
            report
                .findings
                .iter()
                .any(|f| f.rule == CleanRule::C4 && f.message.contains("carries no")),
            "an unaddressed message must be C4: {:?}",
            report.findings
        );
    }

    /// The addressing field is inferred from the receive guard, not named.
    /// Hardcoding `dst` reported four clean corpus specs as violations: Raft,
    /// EPaxos, dining philosophers and Jetpack all use the Raft-lineage
    /// `mdest`, and the name was never the point.
    #[test]
    fn the_addressing_field_is_whatever_the_receive_guard_routes_on() {
        let source = r#"---- MODULE Test ----
EXTENDS Naturals
VARIABLES msgs, state
TypeOK == state \in [Proc -> Nat]
Req(s, d) == [mtype |-> "req", msource |-> s, mdest |-> d]
Send(s) == \E d \in Proc : msgs' = msgs \cup {Req(s, d)}
Recv(p) == \E m \in msgs : /\ m.mdest = p
                           /\ state' = [state EXCEPT ![p] = 1]
                           /\ msgs' = msgs \ {m}
Next == \E p \in Proc : Send(p) \/ Recv(p)
===="#;
        let report = lint(source);
        assert!(
            !report
                .findings
                .iter()
                .any(|f| f.message.contains("carries no")),
            "`mdest` addresses the message just as well as `dst`: {:?}",
            report.findings
        );
    }

    /// **This test used to assert the opposite, and the change is deliberate.**
    ///
    /// It read: "A spec whose receive guard tests no field of the message gives
    /// nothing to infer from. Staying silent is the honest answer -- guessing a
    /// field name is what produced the false positives above." That reasoning
    /// is right about *guessing which field routes* and it left the rule unable
    /// to fire on a network that is not addressed at all: remove `dst` from
    /// every constructor **and** from the guard, and a spec went from three C4
    /// findings back to `clean`.
    ///
    /// The distinction that makes reporting honest here: this does not pick a
    /// field and demand it. It observes that the message carries **no
    /// candidate at all** -- neither a field some receive routes on, nor any of
    /// the recognised spellings. A receive that guards on nothing lets any node
    /// consume any message, which is not something framework delivery can
    /// implement whatever the fields are called.
    #[test]
    fn a_network_with_no_addressing_anywhere_is_reported() {
        let source = r#"---- MODULE Test ----
EXTENDS Naturals
VARIABLES msgs, state
TypeOK == state \in [Proc -> Nat]
Send(s) == msgs' = msgs \cup {[kind |-> "ping"]}
Recv(p) == \E m \in msgs : /\ state' = [state EXCEPT ![p] = 1]
                           /\ msgs' = msgs \ {m}
Next == \E p \in Proc : Send(p) \/ Recv(p)
===="#;
        let report = lint(source);
        assert!(
            report.findings.iter().any(|f| f.rule == CleanRule::C4),
            "no message carries any addressing and no receive routes on \
             anything, so nothing can be delivered: {:?}",
            report.findings
        );
    }

    /// Phase 52: "Writing the whole array is out ... a step that updates every
    /// node. Only `Init` may do it" (`docs/clean_tla_subset.md`, C2).
    #[test]
    fn rejects_assigning_a_per_node_variable_as_a_whole_array() {
        let source = r#"---- MODULE Test ----
EXTENDS Naturals
VARIABLES state
TypeOK == state \in [Proc -> Nat]
Step(p) == state' = [i \in Proc |-> state[i] + 1]
Next == \E p \in Proc : Step(p)
===="#;
        let report = lint(source);
        assert!(
            report
                .findings
                .iter()
                .any(|f| f.rule == CleanRule::C2 && f.message.contains("assigns")),
            "a whole-array write must be C2: {:?}",
            report.findings
        );
    }

    /// `Init` builds the whole function by definition, and must stay clean. The
    /// exemption is structural rather than special-cased: C2 only walks the
    /// operators reachable from `Next`.
    #[test]
    fn init_may_build_the_whole_array() {
        let source = r#"---- MODULE Test ----
EXTENDS Naturals
VARIABLES state
TypeOK == state \in [Proc -> Nat]
Init == state = [i \in Proc |-> 0]
Step(p) == state' = [state EXCEPT ![p] = state[p] + 1]
Next == \E p \in Proc : Step(p)
===="#;
        let report = lint(source);
        assert!(
            !report
                .findings
                .iter()
                .any(|f| f.message.contains("assigns")),
            "Init is where the whole function is built: {:?}",
            report.findings
        );
    }

    /// The exemption that keeps the rule usable, and the reason it keys on the
    /// *direct* right-hand side: a constructor over the node set nested inside
    /// an `EXCEPT` updates one node's inner table. Lamport-mutex's `AdvanceAll`
    /// advances every destination counter within node `s` -- a single-node step.
    #[test]
    fn a_constructor_nested_in_an_except_is_not_a_whole_array_write() {
        let source = r#"---- MODULE Test ----
EXTENDS Naturals
VARIABLES sendSeq
TypeOK == sendSeq \in [Proc -> [Proc -> Nat]]
Step(s) == sendSeq' = [sendSeq EXCEPT ![s] = [d \in Proc |-> sendSeq[s][d] + 1]]
Next == \E s \in Proc : Step(s)
===="#;
        let report = lint(source);
        assert!(
            report.is_clean(),
            "updating one node's inner table is a single-node step: {:?}",
            report.findings
        );
    }

    /// Phase 52: "Reading the whole array is a cross-node read, even without an
    /// index" (`docs/clean_tla_subset.md`, C2). `Cardinality(state)` observes
    /// every node at once. The contract stated this; the linter did not check it.
    #[test]
    fn rejects_reading_a_per_node_variable_as_a_whole_array() {
        let source = r#"---- MODULE Test ----
EXTENDS FiniteSets, Naturals
VARIABLES state
TypeOK == state \in [Proc -> Nat]
Step(p) == /\ Cardinality(state) > 0
           /\ state' = [state EXCEPT ![p] = state[p] + 1]
Next == \E p \in Proc : Step(p)
===="#;
        let report = lint(source);
        assert!(
            rules(&report).contains(&CleanRule::C2),
            "a whole-array read must be C2: {:?}",
            report.findings
        );
        assert!(
            report
                .findings
                .iter()
                .any(|f| f.message.contains("whole array")),
            "the message should say which shape was found: {:?}",
            report.findings
        );
    }

    /// The exemption that makes the rule usable. `[f EXCEPT ![i] = v]` names `f`
    /// bare but touches exactly entry `i` -- it is the ordinary per-node update.
    /// Counting the base flagged three of Lamport-mutex's helpers on a spec that
    /// is clean, which is how this was caught.
    #[test]
    fn an_except_base_is_not_a_whole_array_read() {
        let source = r#"---- MODULE Test ----
EXTENDS Naturals
VARIABLES sendSeq
TypeOK == sendSeq \in [Proc -> Nat]
Advance(s) == [sendSeq EXCEPT ![s] = sendSeq[s] + 1]
Step(p) == sendSeq' = Advance(p)
Next == \E p \in Proc : Step(p)
===="#;
        let report = lint(source);
        assert!(
            !report
                .findings
                .iter()
                .any(|f| f.message.contains("whole array")),
            "an EXCEPT base is an update of one entry, not a whole-array read: {:?}",
            report.findings
        );
    }

    /// The other exemption the contract names: "Frame conditions are exempt.
    /// `x' = x` ... carries no information across nodes".
    #[test]
    fn a_frame_condition_is_not_a_whole_array_read() {
        let source = r#"---- MODULE Test ----
EXTENDS Naturals
VARIABLES clock, flag
TypeOK == /\ clock \in [Proc -> Nat]
          /\ flag \in [Proc -> Nat]
Step(p) == /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
           /\ flag' = flag
Next == \E p \in Proc : Step(p)
===="#;
        let report = lint(source);
        assert!(
            !report
                .findings
                .iter()
                .any(|f| f.message.contains("whole array")),
            "`flag' = flag` is a frame condition: {:?}",
            report.findings
        );
    }

    /// An indexed read is C2's *other* branch; it must not also be counted as a
    /// whole-array read, or every cross-node read would report twice.
    #[test]
    fn an_indexed_read_is_not_also_reported_as_a_whole_array_read() {
        let source = r#"---- MODULE Test ----
EXTENDS Naturals
VARIABLES clock
TypeOK == clock \in [Proc -> Nat]
Step(p) == \E q \in Proc : clock' = [clock EXCEPT ![p] = clock[q]]
Next == \E p \in Proc : Step(p)
===="#;
        let report = lint(source);
        let whole = report
            .findings
            .iter()
            .filter(|f| f.message.contains("whole array"))
            .count();
        assert_eq!(
            whole, 0,
            "indexed reads belong to the other branch: {:?}",
            report.findings
        );
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
    fn reports_a_spec_with_no_per_node_state_as_having_no_node_set() {
        // ReadersWriters: nothing is declared per-node, so no set qualifies as
        // the node set and the spec has no projection at all. Reporting the
        // missing node set names the root cause; listing each variable would
        // only describe the symptom.
        let source = r#"---- MODULE Test ----
VARIABLES readers, writers
Init == /\ readers = {}
        /\ writers = {}
Acquire(p) == readers' = readers \union {p}
Next == \E p \in Proc : Acquire(p)
===="#;
        let report = lint(source);
        assert_eq!(rules(&report), vec![CleanRule::C5]);
        assert!(
            report.findings[0]
                .message
                .contains("cannot identify the node set"),
            "got {}",
            report.findings[0].message
        );
        assert!(report.node_set.is_none());
    }

    #[test]
    fn rejects_next_without_node_quantification() {
        // The node set is inferred from the declaration, then `Next` is checked
        // against it: the second disjunct names a node instead of binding one.
        let source = r#"---- MODULE Test ----
VARIABLES x
TypeOK == x \in [Proc -> Nat]
Step(p) == x' = x
Next == (\E p \in Proc : Step(p)) \/ Step(1)
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
    fn a_second_node_binder_is_a_destination_not_a_violation() {
        let source = r#"---- MODULE Test ----
VARIABLES x
TypeOK == x \in [Proc -> Nat]
Transfer(p, q) == x' = x
Next == \E p, q \in Proc : Transfer(p, q)
===="#;
        // Binding a second node is how a spec names a message's destination --
        // Raft's `\E i, j \in Server : RequestVote(i, j)` reads only i's state.
        // Whether the action reaches into the other node is C2's question.
        let report = lint(source);
        assert!(
            !report.findings.iter().any(|f| f.rule == CleanRule::C5),
            "a second node binder is a destination, not a C5 violation: {:?}",
            report.findings
        );
    }

    #[test]
    fn a_read_at_the_second_node_is_still_caught() {
        // The shape is allowed; reaching into the other node's state is not,
        // and that is C2's job.
        let source = r#"---- MODULE Test ----
VARIABLES x
TypeOK == x \in [Proc -> Nat]
Transfer(p, q) == x' = [x EXCEPT ![p] = x[q]]
Next == \E p, q \in Proc : Transfer(p, q)
===="#;
        let report = lint(source);
        assert!(
            report.findings.iter().any(|f| f.rule == CleanRule::C2),
            "reading x[q] at a second bound node must be a C2 finding: {:?}",
            report.findings
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
            json.contains(r#""rules_checked":["C1","C2","C3","C4","C5"]"#),
            "{json}"
        );
        assert!(json.contains(r#""rules_not_implemented":[]"#), "{json}");
        assert!(json.contains(r#""network_variable":null"#), "{json}");
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

    #[test]
    fn designates_a_message_set_as_the_network() {
        // Paxos's `msgs`: sent with \cup, received with `\E m \in msgs`.
        let source = r#"---- MODULE Test ----
VARIABLES maxBal, msgs
TypeOK == maxBal \in [Acceptor -> Nat]
Send(m) == msgs' = msgs \cup {m}
Phase1b(a) == \E m \in msgs : maxBal' = [maxBal EXCEPT ![a] = m.bal]
Next == \E a \in Acceptor : Phase1b(a)
===="#;
        let report = lint(source);
        assert_eq!(report.network_variable.as_deref(), Some("msgs"));
        assert!(
            !report.global_variables.contains(&"msgs".to_string()),
            "the network is not unexplained global state: {:?}",
            report.global_variables
        );
    }

    #[test]
    fn a_shared_set_without_receives_is_not_the_network() {
        // LamportMutex's `crit` is updated with exactly the network idiom
        // (\cup / \) but nothing ever receives from it. Designating it would
        // suppress the C1 finding that is the real problem with it.
        let source = r#"---- MODULE Test ----
VARIABLES clock, crit
TypeOK == clock \in [Proc -> Nat]
Enter(p) == crit' = crit \cup {p}
Exit(p) == crit' = crit \ {p}
Next == \E p \in Proc : Enter(p) \/ Exit(p)
===="#;
        let report = lint(source);
        assert_eq!(report.network_variable, None);
        let c1 = report
            .findings
            .iter()
            .find(|f| f.rule == CleanRule::C1)
            .unwrap_or_else(|| panic!("expected C1 for crit, got {:?}", report.findings));
        assert!(c1.message.contains("crit"), "got {}", c1.message);
    }

    #[test]
    fn reports_a_network_that_is_not_a_message_set() {
        // LamportMutex: `network` is [Proc -> [Proc -> Seq(Msg)]], a queue per
        // connection. It IS the network, so say what is wrong with it rather
        // than reporting each read of it.
        let source = r#"---- MODULE Test ----
VARIABLES clock, network
TypeOK == /\ clock \in [Proc -> Nat]
          /\ network \in [Proc -> [Proc -> Seq(Msg)]]
Send(p, q) == network' = [network EXCEPT ![p][q] = Append(@, m)]
Recv(p, q) == /\ network[q][p] # << >>
              /\ network' = [network EXCEPT ![q][p] = Tail(@)]
Next == \E p \in Proc : \A q \in Proc : Recv(p, q)
===="#;
        let report = lint(source);
        let c4 = report
            .findings
            .iter()
            .find(|f| f.rule == CleanRule::C4)
            .unwrap_or_else(|| panic!("expected a C4 finding, got {:?}", report.findings));
        assert!(
            c4.message.contains("not a message set") && c4.message.contains("ordering"),
            "the finding must name the shape problem and the ordering it costs: {}",
            c4.message
        );
        assert!(
            !report
                .findings
                .iter()
                .any(|f| f.rule == CleanRule::C2 && f.message.contains("network")),
            "a malformed network is one decision, not one C2 finding per read: {:?}",
            report.findings
        );
    }

    #[test]
    fn rejects_a_history_variable() {
        // Raft's allLogs: built by gathering every node's log. No node can
        // maintain it and the protocol never consults it.
        let source = r#"---- MODULE Test ----
VARIABLES log, allLogs
TypeOK == log \in [Server -> Seq(Nat)]
Append(i) == /\ log' = [log EXCEPT ![i] = Append(log[i], 1)]
             /\ allLogs' = allLogs \cup {log[j] : j \in Server}
Next == \E i \in Server : Append(i)
===="#;
        let report = lint(source);
        let c3 = report
            .findings
            .iter()
            .find(|f| f.rule == CleanRule::C3)
            .unwrap_or_else(|| panic!("expected a C3 finding, got {:?}", report.findings));
        assert!(
            c3.message.contains("allLogs") && c3.message.contains("history variable"),
            "got {}",
            c3.message
        );
    }

    #[test]
    fn infers_the_node_set_from_declarations_not_from_next() {
        // Real Paxos quantifies over Ballot and Value in `Next` alongside
        // Acceptor. Only Acceptor indexes per-node state, so only it is the
        // node set.
        let source = r#"---- MODULE Test ----
VARIABLES maxBal
TypeOK == maxBal \in [Acceptor -> Nat]
Phase1a(b) == maxBal' = maxBal
Phase1b(a) == maxBal' = [maxBal EXCEPT ![a] = 0]
Next == \/ \E b \in Ballot : Phase1a(b)
        \/ \E a \in Acceptor : Phase1b(a)
===="#;
        let report = lint(source);
        assert_eq!(report.node_set.as_deref(), Some("Acceptor"));
        let c5 = report
            .findings
            .iter()
            .find(|f| f.rule == CleanRule::C5)
            .unwrap_or_else(|| panic!("expected C5 for the node-less disjunct"));
        assert!(
            c5.message.contains("never binds a node"),
            "a disjunct that binds only a value domain must be reported: {}",
            c5.message
        );
    }
}
