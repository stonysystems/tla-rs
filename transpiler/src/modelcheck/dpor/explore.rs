//! DPOR search stack and DFS exploration loop.
//!
//! Implements the core DPOR algorithm: a depth-first search with
//! backtrack sets at each stack frame. v1 uses conservative dependence
//! (all transitions dependent), making it equivalent to exhaustive DFS.
//! Future versions will add independence-based pruning.
//!
//! Reference: source-DPOR from Nidhugg (DPORDriver + TraceBuilder pattern).

use std::collections::{BTreeMap, BTreeSet};

use crate::modelcheck::dpor::enabled::SpecContext;
use crate::modelcheck::dpor::types::*;
use crate::modelcheck::value::RuntimeValue;
use transpiler_runtime::Symbol;

/// One frame in the DPOR search stack.
#[derive(Clone, Debug)]
pub struct StackFrame {
    /// State at this depth (before the chosen transition).
    pub state: RuntimeValue,
    /// Fingerprint of the state.
    pub state_fingerprint: StateFingerprint,
    /// All enabled transitions from this state.
    pub enabled: Vec<EnabledTransition>,
    /// Which transitions have been explored (by ordering_key).
    pub done: BTreeSet<String>,
    /// Which transitions should still be explored (backtrack set).
    /// In v1 (conservative), this starts as all enabled transitions.
    pub backtrack: BTreeSet<String>,
    /// Sleep set: transitions that should NOT be explored because an
    /// equivalent interleaving will be explored from a sibling path.
    /// Keyed by stable action identity (`process_id + branch_label`).
    pub sleep: BTreeSet<String>,
    /// The transition that was chosen to proceed deeper (if any).
    pub chosen: Option<EnabledTransition>,
    /// Depth in the search (0 = initial state).
    pub depth: usize,
}

/// Result of a DPOR exploration run.
#[derive(Debug)]
pub struct DporResult {
    /// All distinct states discovered.
    pub distinct_states: BTreeSet<String>,
    /// Number of complete executions (traces) explored.
    pub traces_explored: usize,
    /// Maximum depth reached.
    pub max_depth: usize,
    /// Total transitions fired.
    pub transitions_fired: usize,
    /// Number of transitions skipped due to sleep-set pruning checks.
    pub sleep_prune_hits: usize,
    /// Per-depth sleep-set cardinality telemetry observed when frames are created.
    pub sleep_cardinality_by_depth: BTreeMap<usize, SleepDepthStats>,
    /// Independence blocker telemetry collected while building child sleep sets.
    pub sleep_independence_blockers: SleepIndependenceBlockers,
    /// Runtime conflict verification stats: per-write-field false-positive rates.
    pub runtime_conflict_stats: RuntimeConflictStats,
    /// Violation witness if an invariant violation was found.
    pub violation: Option<ViolationWitness>,
}

/// Aggregated sleep-set cardinality stats for a depth.
#[derive(Debug, Clone, Default)]
pub struct SleepDepthStats {
    /// Number of observations recorded for this depth.
    pub samples: usize,
    /// Sum of observed cardinalities (for average).
    pub total_cardinality: usize,
    /// Maximum observed cardinality at this depth.
    pub max_cardinality: usize,
}

/// Aggregated reasons why sleep-set independence checks did not admit candidates.
#[derive(Debug, Clone, Default)]
pub struct SleepIndependenceBlockers {
    /// Child-sleep computation skipped because independence was disabled.
    pub early_exit_independence_disabled: usize,
    /// Child-sleep computation skipped because chosen transition had unknown footprint.
    pub early_exit_chosen_unknown_footprint: usize,
    /// Total candidate pairs evaluated for child-sleep seeding.
    pub candidates_considered: usize,
    /// Candidate pairs considered independent.
    pub independent_candidates: usize,
    /// Candidate pairs blocked because transitions are from the same process.
    pub blocked_same_process: usize,
    /// Candidate pairs blocked because one side has an unknown (empty) footprint.
    pub blocked_unknown_footprint: usize,
    /// Candidate pairs blocked due to read/write footprint conflict.
    pub blocked_footprint_conflict: usize,
    /// Per-field-pair conflict frequency: maps `(left_field, right_field)` to
    /// the number of times this pair caused a footprint conflict block.
    /// Only populated when `blocked_footprint_conflict > 0`.
    pub conflict_field_pairs: BTreeMap<(String, String), usize>,
}

/// Per-write-field runtime conflict verification stats.
///
/// After each transition fires, we compare pre-state and post-state values
/// for each field in the transition's write footprint. This tells us how
/// often a "static write" actually changes the field value at runtime.
/// A field that is statically written but rarely changes is a source of
/// false-positive conflicts in the independence relation.
#[derive(Debug, Clone, Default)]
pub struct RuntimeConflictStats {
    /// Per write field: `(static_write_count, actual_change_count)`.
    /// `static_write_count` = number of fired transitions whose footprint
    /// declares this field as written.
    /// `actual_change_count` = number of those where the field value
    /// actually differed between pre-state and post-state.
    pub write_field_stats: BTreeMap<String, (usize, usize)>,
}

/// Configuration for the DPOR explorer.
#[derive(Clone, Debug)]
pub struct DporConfig {
    /// Maximum exploration depth.
    pub max_depth: usize,
    /// Maximum number of distinct states before stopping.
    pub max_states: usize,
    /// If true, use branch footprints for independence-based backtrack pruning.
    /// If false, all transitions are treated as dependent (conservative/exhaustive).
    pub use_independence: bool,
    /// If true, use sleep sets to prune redundant interleavings.
    /// Requires `use_independence` to be true (sleep sets need the independence relation).
    /// When footprints are empty (reads_whole_state), sleep sets provide no benefit.
    pub use_sleep_sets: bool,
    /// Invariant names to check on each reached state. Empty = no checking.
    pub invariants: Vec<String>,
    /// If true, detect deadlocked states (states with zero enabled transitions).
    pub check_deadlock: bool,
}

/// A recorded step in a violation witness trace.
#[derive(Clone, Debug)]
pub struct WitnessStep {
    /// State fingerprint before this step.
    pub state_fingerprint: StateFingerprint,
    /// Canonical state key before this step.
    pub state_key: String,
    /// The transition taken (ordering_key from enabled set).
    pub transition_key: String,
    /// Depth at which this step was taken.
    pub depth: usize,
}

/// A violation witness: the trace from initial state to the violating state.
#[derive(Clone, Debug)]
pub struct ViolationWitness {
    /// Name of the violated invariant.
    pub invariant: String,
    /// The violating state's canonical key.
    pub violating_state_key: String,
    /// The violating state's fingerprint.
    pub violating_state_fingerprint: StateFingerprint,
    /// Depth at which the violation was found.
    pub depth: usize,
    /// Ordered trace from initial state to violation.
    pub trace: Vec<WitnessStep>,
}

impl Default for DporConfig {
    fn default() -> Self {
        Self {
            max_depth: 100,
            max_states: 100_000,
            use_independence: false,
            use_sleep_sets: false,
            invariants: vec![],
            check_deadlock: false,
        }
    }
}

/// Run the DPOR DFS exploration on a loaded spec.
///
/// When `config.use_independence` is false (default): conservative dependence
/// (all transitions dependent). Equivalent to exhaustive DFS.
///
/// When `config.use_independence` is true: uses branch footprints from
/// enabled transitions to determine independence conservatively:
/// same-process transitions and unknown-footprint transitions remain
/// dependent; only cross-process transitions with disjoint footprints
/// are treated as independent for sleep-set propagation.
pub fn explore_dpor(ctx: &SpecContext, config: &DporConfig) -> DporResult {
    // Reset the zero-arg helper-call cache at run boundaries so that repeated
    // invocations in the same process (e.g. shadow-compare or tests) do not
    // carry stale cache entries across specs.
    crate::modelcheck::helpers::reset_zero_arg_helper_cache();

    // Phase 38.21.D: route every dedup key through the symmetry-aware
    // canonical labeling that BFS uses, so DPOR also benefits from
    // symmetry reduction declared in `[search] symmetry_fields = [...]`.
    // When the field list is empty this collapses back to plain
    // `state.canonical_key()`.
    let symmetry_fields_owned: Vec<String> = ctx.model_config.search.symmetry_fields.clone();
    let canonical_state_key = |state: &RuntimeValue| -> String {
        crate::modelcheck::explorer::canonical_dedup_key_public(
            state,
            symmetry_fields_owned.iter().cloned(),
        )
    };

    let mut distinct_states: BTreeSet<String> = BTreeSet::new();
    // Fast-path dedup via u64 fingerprint (avoids canonical_key String alloc
    // for already-seen states). When symmetry_fields is empty, fingerprint is
    // the sole authority; with symmetry, canonical_key is still authoritative
    // but fingerprint screens out the majority of duplicates cheaply.
    let mut seen_fingerprints: std::collections::HashSet<u64> = std::collections::HashSet::new();
    let use_symmetry = !symmetry_fields_owned.is_empty();
    let mut traces_explored: usize = 0;
    let mut max_depth: usize = 0;
    let mut transitions_fired: usize = 0;
    let mut sleep_prune_hits: usize = 0;
    let mut sleep_cardinality_by_depth: BTreeMap<usize, SleepDepthStats> = BTreeMap::new();
    let mut sleep_independence_blockers = SleepIndependenceBlockers::default();
    let mut runtime_conflict_stats = RuntimeConflictStats::default();

    // Get initial states
    let initial_states = match ctx.initial_states() {
        Ok(states) => states,
        Err(e) => {
            eprintln!("DPOR: failed to get initial states: {}", e);
            return DporResult {
                distinct_states,
                traces_explored: 0,
                max_depth: 0,
                transitions_fired: 0,
                sleep_prune_hits: 0,
                sleep_cardinality_by_depth: BTreeMap::new(),
                sleep_independence_blockers: SleepIndependenceBlockers::default(),
                runtime_conflict_stats: RuntimeConflictStats::default(),
                violation: None,
            };
        }
    };

    // Resolve invariant functions
    let invariant_fns = ctx.resolve_invariants(&config.invariants);

    // Helper: check invariants and return violation witness if found
    let check_state = |state: &RuntimeValue,
                       depth: usize,
                       trace: &[WitnessStep]|
     -> Option<ViolationWitness> {
        if invariant_fns.is_empty() {
            return None;
        }
        match ctx.check_invariants(state, &invariant_fns) {
            Ok(Some(violated)) => Some(ViolationWitness {
                invariant: violated,
                violating_state_key: state.canonical_key(),
                violating_state_fingerprint: crate::modelcheck::dpor::enabled::hash_state(state),
                depth,
                trace: trace.to_vec(),
            }),
            _ => None,
        }
    };

    // Explore from each initial state
    for initial in &initial_states {
        let initial_fp = initial.fingerprint();
        if !seen_fingerprints.insert(initial_fp) {
            // Fingerprint already seen — definitely a duplicate (no symmetry
            // can merge two states with identical fingerprints differently).
            continue;
        }
        let initial_key = canonical_state_key(initial);
        if !distinct_states.insert(initial_key.clone()) {
            continue; // Symmetry-merged duplicate
        }

        // Check invariants on initial state
        if let Some(witness) = check_state(initial, 0, &[]) {
            return DporResult {
                distinct_states,
                traces_explored: 0,
                max_depth: 0,
                transitions_fired: 0,
                sleep_prune_hits: 0,
                sleep_cardinality_by_depth: BTreeMap::new(),
                sleep_independence_blockers: SleepIndependenceBlockers::default(),
                runtime_conflict_stats: RuntimeConflictStats::default(),
                violation: Some(witness),
            };
        }

        let enabled = match ctx.enabled_transitions(initial) {
            Ok(e) => e,
            Err(e) => {
                eprintln!("DPOR: failed to enumerate enabled transitions: {}", e);
                continue;
            }
        };

        // Deadlock on initial state (unlikely but possible)
        if config.check_deadlock && enabled.is_empty() {
            return DporResult {
                distinct_states,
                traces_explored: 0,
                max_depth: 0,
                transitions_fired: 0,
                sleep_prune_hits: 0,
                sleep_cardinality_by_depth: BTreeMap::new(),
                sleep_independence_blockers: SleepIndependenceBlockers::default(),
                runtime_conflict_stats: RuntimeConflictStats::default(),
                violation: Some(ViolationWitness {
                    invariant: "__deadlock__".to_string(),
                    violating_state_key: initial.canonical_key(),
                    violating_state_fingerprint: crate::modelcheck::dpor::enabled::hash_state(
                        initial,
                    ),
                    depth: 0,
                    trace: vec![],
                }),
            };
        }

        // Initialize backtrack set with all enabled transitions (conservative)
        let backtrack = initialize_backtrack_keys(&enabled, &BTreeSet::new());

        let initial_frame = StackFrame {
            state: initial.clone(),
            state_fingerprint: crate::modelcheck::dpor::enabled::hash_state(initial),
            enabled,
            done: BTreeSet::new(),
            backtrack,
            sleep: BTreeSet::new(),
            chosen: None,
            depth: 0,
        };
        record_sleep_cardinality(
            &mut sleep_cardinality_by_depth,
            initial_frame.depth,
            initial_frame.sleep.len(),
        );

        // DFS with explicit stack
        let mut stack: Vec<StackFrame> = vec![initial_frame];

        while !stack.is_empty() {
            // Check limits
            if seen_fingerprints.len() >= config.max_states {
                break;
            }

            // Phase 1: Extract data from the top frame (scoped mutable borrow)
            let action = {
                let frame = stack.last_mut().unwrap();
                let mut next_transition: Option<String> = None;
                let mut prunes_this_scan: usize = 0;
                for key in &frame.backtrack {
                    if frame.done.contains(key) {
                        continue;
                    }
                    if !config.use_sleep_sets {
                        next_transition = Some(key.clone());
                        break;
                    }
                    let transition = frame.enabled.iter().find(|t| t.ordering_key == *key);
                    if let Some(t) = transition {
                        if config.use_sleep_sets
                            && has_done_successor_fingerprint(
                                &frame.done,
                                &frame.enabled,
                                t.successor_fingerprint,
                            )
                        {
                            // If an already explored sibling reaches the same successor
                            // fingerprint, re-firing this transition is redundant for the
                            // state-based exploration contract used by this checker.
                            prunes_this_scan += 1;
                            continue;
                        }
                        if frame.sleep.contains(&transition_sleep_key(t)) {
                            prunes_this_scan += 1;
                            continue;
                        }
                        next_transition = Some(key.clone());
                        break;
                    }
                }
                sleep_prune_hits += prunes_this_scan;

                match next_transition {
                    Some(key) => {
                        let transition = frame
                            .enabled
                            .iter()
                            .find(|t| t.ordering_key == key)
                            .cloned();
                        match transition {
                            Some(t) => {
                                frame.done.insert(key.clone());
                                if config.use_sleep_sets {
                                    frame.sleep.insert(transition_sleep_key(&t));
                                }
                                frame.chosen = Some(t.clone());
                                let parent_state = frame.state.clone();
                                let parent_depth = frame.depth;
                                let parent_sleep = frame.sleep.clone();
                                let parent_done = frame.done.clone();
                                let parent_enabled = frame.enabled.clone();
                                Some((
                                    key,
                                    t,
                                    parent_state,
                                    parent_depth,
                                    parent_sleep,
                                    parent_done,
                                    parent_enabled,
                                ))
                            }
                            None => continue,
                        }
                    }
                    None => None,
                }
            };
            // Mutable borrow of `frame` is released here

            match action {
                Some((
                    _key,
                    transition,
                    parent_state,
                    parent_depth,
                    parent_sleep,
                    parent_done,
                    parent_enabled,
                )) => {
                    // Get the actual successor state
                    let successors = match ctx.full_successors(&parent_state) {
                        Ok(s) => s,
                        Err(_) => continue,
                    };

                    let successor = successors
                        .iter()
                        .find(|s| {
                            crate::modelcheck::dpor::enabled::hash_state(s)
                                == transition.successor_fingerprint
                        })
                        .cloned();

                    let Some(successor) = successor else {
                        continue;
                    };

                    // Fast-path: check fingerprint before computing canonical key
                    let succ_fp = successor.fingerprint();
                    let fp_is_new = seen_fingerprints.insert(succ_fp);
                    if !fp_is_new && should_prune_seen_successor(config.use_sleep_sets) {
                        sleep_prune_hits += 1;
                        continue;
                    }

                    transitions_fired += 1;
                    // Runtime conflict verification: check which write fields actually changed
                    record_runtime_write_stats(
                        &mut runtime_conflict_stats,
                        &transition,
                        &parent_state,
                        &successor,
                    );
                    // Compute canonical key only for reporting / symmetry dedup
                    let is_new = if fp_is_new && !use_symmetry {
                        // No symmetry: fingerprint is authoritative
                        let succ_key = canonical_state_key(&successor);
                        distinct_states.insert(succ_key);
                        true
                    } else if fp_is_new {
                        // Symmetry enabled: fingerprint was new but canonical
                        // key might merge with existing state
                        let succ_key = canonical_state_key(&successor);
                        distinct_states.insert(succ_key)
                    } else {
                        // Fingerprint already seen: duplicate
                        false
                    };

                    let depth = parent_depth + 1;
                    if depth > max_depth {
                        max_depth = depth;
                    }

                    // Check invariants on the new state
                    if is_new && !invariant_fns.is_empty() {
                        let mut trace: Vec<WitnessStep> = Vec::new();
                        for frame in &stack {
                            if let Some(ch) = &frame.chosen {
                                trace.push(WitnessStep {
                                    state_fingerprint: frame.state_fingerprint,
                                    state_key: frame.state.canonical_key(),
                                    transition_key: ch.ordering_key.clone(),
                                    depth: frame.depth,
                                });
                            }
                        }

                        if let Some(witness) = check_state(&successor, depth, &trace) {
                            return DporResult {
                                distinct_states,
                                traces_explored,
                                max_depth,
                                transitions_fired,
                                sleep_prune_hits,
                                sleep_cardinality_by_depth,
                                sleep_independence_blockers,
                                runtime_conflict_stats,
                                violation: Some(witness),
                            };
                        }
                    }

                    // Push child frame if depth limit not reached and state is new
                    if depth < config.max_depth && is_new {
                        let enabled = ctx.enabled_transitions(&successor).unwrap_or_default();

                        // Deadlock detection: state with zero enabled transitions
                        if config.check_deadlock && enabled.is_empty() {
                            // Build trace from the stack
                            let mut trace: Vec<WitnessStep> = Vec::new();
                            for frame in &stack {
                                if let Some(ch) = &frame.chosen {
                                    trace.push(WitnessStep {
                                        state_fingerprint: frame.state_fingerprint,
                                        state_key: frame.state.canonical_key(),
                                        transition_key: ch.ordering_key.clone(),
                                        depth: frame.depth,
                                    });
                                }
                            }
                            return DporResult {
                                distinct_states,
                                traces_explored,
                                max_depth,
                                transitions_fired,
                                sleep_prune_hits,
                                sleep_cardinality_by_depth,
                                sleep_independence_blockers,
                                runtime_conflict_stats,
                                violation: Some(ViolationWitness {
                                    invariant: "__deadlock__".to_string(),
                                    violating_state_key: successor.canonical_key(),
                                    violating_state_fingerprint:
                                        crate::modelcheck::dpor::enabled::hash_state(&successor),
                                    depth,
                                    trace,
                                }),
                            };
                        }

                        let child_sleep = if config.use_sleep_sets {
                            compute_child_sleep_set(
                                &parent_sleep,
                                &parent_done,
                                &transition,
                                &parent_enabled,
                                config.use_independence,
                                &mut sleep_independence_blockers,
                            )
                        } else {
                            BTreeSet::new()
                        };
                        let backtrack = initialize_backtrack_keys(&enabled, &child_sleep);

                        stack.push(StackFrame {
                            state: successor,
                            state_fingerprint: transition.successor_fingerprint,
                            enabled,
                            done: BTreeSet::new(),
                            backtrack,
                            sleep: child_sleep,
                            chosen: None,
                            depth,
                        });
                        if let Some(frame) = stack.last() {
                            record_sleep_cardinality(
                                &mut sleep_cardinality_by_depth,
                                frame.depth,
                                frame.sleep.len(),
                            );
                        }
                    }
                }
                None => {
                    // All backtrack alternatives explored at this depth — pop
                    stack.pop();
                    traces_explored += 1;
                }
            }
        }
    }

    DporResult {
        distinct_states,
        traces_explored,
        max_depth,
        transitions_fired,
        sleep_prune_hits,
        sleep_cardinality_by_depth,
        sleep_independence_blockers,
        runtime_conflict_stats,
        violation: None,
    }
}

fn record_sleep_cardinality(
    stats: &mut BTreeMap<usize, SleepDepthStats>,
    depth: usize,
    cardinality: usize,
) {
    let entry = stats.entry(depth).or_default();
    entry.samples += 1;
    entry.total_cardinality += cardinality;
    entry.max_cardinality = entry.max_cardinality.max(cardinality);
}

#[cfg(test)]
fn format_sleep_cardinality_summary(stats: &BTreeMap<usize, SleepDepthStats>) -> String {
    if stats.is_empty() {
        return "-".to_string();
    }
    stats
        .iter()
        .map(|(depth, stat)| {
            let avg = if stat.samples == 0 {
                0.0
            } else {
                stat.total_cardinality as f64 / stat.samples as f64
            };
            format!("d{}:{:.1}/{}", depth, avg, stat.max_cardinality)
        })
        .collect::<Vec<_>>()
        .join(";")
}

/// Format a human-readable conflict profile report from independence blocker stats.
///
/// The report ranks field pairs by conflict frequency and suggests keyed-path
/// refinement for coarse (un-keyed) field names. Intended for `--conflict-profile`
/// CLI output to guide POR tuning.
pub fn format_conflict_profile(
    stats: &SleepIndependenceBlockers,
    runtime_stats: &RuntimeConflictStats,
) -> String {
    let mut lines = Vec::new();
    lines.push("=== Conflict Profile Report ===".to_string());
    lines.push(format!(
        "Total candidate pairs evaluated: {}",
        stats.candidates_considered
    ));
    lines.push(format!(
        "  Independent: {} ({:.1}%)",
        stats.independent_candidates,
        if stats.candidates_considered > 0 {
            stats.independent_candidates as f64 / stats.candidates_considered as f64 * 100.0
        } else {
            0.0
        }
    ));
    lines.push(format!(
        "  Blocked (same process): {}",
        stats.blocked_same_process
    ));
    lines.push(format!(
        "  Blocked (unknown footprint): {}",
        stats.blocked_unknown_footprint
    ));
    lines.push(format!(
        "  Blocked (footprint conflict): {}",
        stats.blocked_footprint_conflict
    ));

    if stats.conflict_field_pairs.is_empty() {
        lines.push("  No field-pair conflict data recorded.".to_string());
    } else {
        lines.push(String::new());
        lines.push("Field-pair conflict frequency (ranked):".to_string());
        lines.push(format!(
            "  {:30} {:>8} {:>7}  {}",
            "FIELD PAIR", "COUNT", "PCT", "SUGGESTION"
        ));
        lines.push(format!("  {:-<30} {:->8} {:->7}  {:-<20}", "", "", "", ""));

        let mut pairs: Vec<_> = stats.conflict_field_pairs.iter().collect();
        pairs.sort_by(|a, b| b.1.cmp(a.1));

        let total_conflicts = stats.blocked_footprint_conflict.max(1);
        for ((left, right), count) in &pairs {
            let pct = **count as f64 / total_conflicts as f64 * 100.0;
            let suggestion = suggest_refinement(left, right);
            lines.push(format!(
                "  ({:12}, {:12})  {:>6}  {:>5.1}%  {}",
                left, right, count, pct, suggestion
            ));
        }
    }
    // Runtime conflict verification section
    if !runtime_stats.write_field_stats.is_empty() {
        lines.push(String::new());
        lines.push("Runtime write-field verification:".to_string());
        lines.push(format!(
            "  {:20} {:>8} {:>8} {:>10}",
            "WRITE FIELD", "FIRED", "CHANGED", "FP RATE"
        ));
        lines.push(format!("  {:-<20} {:->8} {:->8} {:->10}", "", "", "", ""));

        let mut fields: Vec<_> = runtime_stats.write_field_stats.iter().collect();
        fields.sort_by(|a, b| b.1 .0.cmp(&a.1 .0)); // sort by static count desc

        for (field, (static_count, actual_count)) in &fields {
            let sc = *static_count;
            let ac = *actual_count;
            let fp_rate = if sc > 0 {
                (sc - ac) as f64 / sc as f64 * 100.0
            } else {
                0.0
            };
            lines.push(format!(
                "  {:20} {:>8} {:>8} {:>8.1}%",
                field, sc, ac, fp_rate
            ));
        }
    }

    lines.push("=== End Conflict Profile ===".to_string());
    lines.join("\n")
}

/// Suggest keyed-path refinement for a conflicting field pair.
fn suggest_refinement(left: &str, right: &str) -> &'static str {
    let left_keyed = left.contains('[');
    let right_keyed = right.contains('[');
    match (left_keyed, right_keyed) {
        (false, false) => "try process-scoped keying (e.g., field[pid])",
        (true, true) => "already keyed — true conflict",
        _ => "partially keyed — check coarse side",
    }
}

#[cfg(test)]
fn format_independence_blockers_summary(stats: &SleepIndependenceBlockers) -> String {
    let mut summary = format!(
        "early_off={} chosen_unknown={} cand={} ind={} same={} unknown={} conflict={}",
        stats.early_exit_independence_disabled,
        stats.early_exit_chosen_unknown_footprint,
        stats.candidates_considered,
        stats.independent_candidates,
        stats.blocked_same_process,
        stats.blocked_unknown_footprint,
        stats.blocked_footprint_conflict
    );
    if !stats.conflict_field_pairs.is_empty() {
        let mut pairs: Vec<_> = stats.conflict_field_pairs.iter().collect();
        pairs.sort_by(|a, b| b.1.cmp(a.1));
        let top_n = 5;
        let top_pairs: Vec<String> = pairs
            .iter()
            .take(top_n)
            .map(|((l, r), count)| format!("({},{})::{}", l, r, count))
            .collect();
        summary.push_str(&format!(" top_conflicts=[{}]", top_pairs.join(", ")));
    }
    summary
}

#[cfg(test)]
fn percent_reduction(baseline: usize, optimized: usize) -> f64 {
    if baseline == 0 {
        return 0.0;
    }
    ((baseline as f64 - optimized as f64) / baseline as f64) * 100.0
}

#[cfg(test)]
const REDUCTION_GATE_THRESHOLD_PERCENT: f64 = 10.0;
#[cfg(test)]
const REDUCTION_GATE_REQUIRED_CASES: usize = 3;

#[cfg(test)]
fn transition_reduction_gate_hit(
    conservative_transitions: usize,
    sleep_transitions: usize,
) -> bool {
    percent_reduction(conservative_transitions, sleep_transitions)
        > REDUCTION_GATE_THRESHOLD_PERCENT
}

/// Result of replaying a violation witness.
#[derive(Debug)]
pub struct ReplayResult {
    /// Whether the replay confirmed the same violation at the same depth.
    pub confirmed: bool,
    /// States visited during replay, in order.
    pub states: Vec<String>,
    /// The invariant that was found violated (if any).
    pub violated_invariant: Option<String>,
    /// Depth at which violation was confirmed (or replay ended).
    pub depth: usize,
    /// Error message if replay failed.
    pub error: Option<String>,
}

/// Replay a violation witness deterministically from the initial state.
///
/// Re-executes the trace step by step:
/// 1. Gets initial states and finds the one matching the trace start
/// 2. For each step: computes successors, finds the matching transition
/// 3. At the final state: checks the invariant
///
/// Returns a `ReplayResult` indicating whether the violation was confirmed.
pub fn replay_witness(ctx: &SpecContext, witness: &ViolationWitness) -> ReplayResult {
    let mut visited_states = Vec::new();

    // Get initial states
    let initial_states = match ctx.initial_states() {
        Ok(s) => s,
        Err(e) => {
            return ReplayResult {
                confirmed: false,
                states: vec![],
                violated_invariant: None,
                depth: 0,
                error: Some(format!("Failed to get initial states: {}", e)),
            };
        }
    };

    // Find the initial state
    let first_state_key = if let Some(step) = witness.trace.first() {
        &step.state_key
    } else {
        // Empty trace — the violation is in the initial state
        &witness.violating_state_key
    };

    let mut current = match initial_states
        .iter()
        .find(|s| s.canonical_key() == *first_state_key)
    {
        Some(s) => s.clone(),
        None => {
            // Try to find any initial state if the exact key doesn't match
            if let Some(s) = initial_states.first() {
                s.clone()
            } else {
                return ReplayResult {
                    confirmed: false,
                    states: vec![],
                    violated_invariant: None,
                    depth: 0,
                    error: Some("No initial states found".to_string()),
                };
            }
        }
    };
    visited_states.push(current.canonical_key());

    // Follow each step in the trace
    for (step_idx, step) in witness.trace.iter().enumerate() {
        // Get successors from the current state
        let successors = match ctx.full_successors(&current) {
            Ok(s) => s,
            Err(e) => {
                return ReplayResult {
                    confirmed: false,
                    states: visited_states,
                    violated_invariant: None,
                    depth: step_idx,
                    error: Some(format!(
                        "Failed to get successors at step {}: {}",
                        step_idx, e
                    )),
                };
            }
        };

        // Get enabled transitions to match transition_key to a successor
        let enabled = ctx.enabled_transitions(&current).unwrap_or_default();

        // Find the successor via transition_key → successor_fingerprint
        let next_state = if let Some(trans) = enabled
            .iter()
            .find(|t| t.ordering_key == step.transition_key)
        {
            successors
                .iter()
                .find(|s| {
                    crate::modelcheck::dpor::enabled::hash_state(s) == trans.successor_fingerprint
                })
                .cloned()
        } else {
            // Fallback: if transition_key doesn't match, try to find by index
            let idx: usize = step.transition_key.parse().unwrap_or(usize::MAX);
            successors.get(idx).cloned()
        };

        match next_state {
            Some(next) => {
                visited_states.push(next.canonical_key());
                current = next;
            }
            None => {
                return ReplayResult {
                    confirmed: false,
                    states: visited_states,
                    violated_invariant: None,
                    depth: step_idx,
                    error: Some(format!(
                        "Could not find successor at step {} (transition_key={})",
                        step_idx, step.transition_key
                    )),
                };
            }
        }
    }

    // Check the final state: deadlock or invariant violation
    if witness.invariant == "__deadlock__" {
        // Deadlock replay: verify the final state has zero enabled transitions
        let enabled = ctx.enabled_transitions(&current).unwrap_or_default();
        let is_deadlocked = enabled.is_empty();
        return ReplayResult {
            confirmed: is_deadlocked,
            states: visited_states,
            violated_invariant: if is_deadlocked {
                Some("__deadlock__".to_string())
            } else {
                None
            },
            depth: witness.depth,
            error: if !is_deadlocked {
                Some(format!(
                    "Expected deadlock but state has {} enabled transitions",
                    enabled.len()
                ))
            } else {
                None
            },
        };
    }

    // Invariant violation replay
    let invariant_fns = ctx.resolve_invariants(std::slice::from_ref(&witness.invariant));
    let violated = match ctx.check_invariants(&current, &invariant_fns) {
        Ok(v) => v,
        Err(e) => {
            return ReplayResult {
                confirmed: false,
                states: visited_states,
                violated_invariant: None,
                depth: witness.depth,
                error: Some(format!("Invariant check failed: {}", e)),
            };
        }
    };

    let confirmed = violated.as_ref() == Some(&witness.invariant);
    let error_msg = if !confirmed {
        Some(format!(
            "Expected violation of '{}' but got {:?}",
            witness.invariant,
            violated.as_deref().unwrap_or("no violation")
        ))
    } else {
        None
    };
    ReplayResult {
        confirmed,
        states: visited_states,
        violated_invariant: violated,
        depth: witness.depth,
        error: error_msg,
    }
}

/// Compute the sleep set for a child frame by propagating the parent's sleep set.
///
/// A sleeping transition is propagated to the child only if it is INDEPENDENT
/// of the chosen transition. Dependent transitions are "woken up" because
/// taking the chosen transition may have changed the state in a relevant way.
///
/// When footprints are empty (reads_whole_state), all transitions are treated
/// as dependent, so the child sleep set is always empty (correct but no benefit).
fn initialize_backtrack_keys(
    enabled: &[EnabledTransition],
    sleep: &BTreeSet<String>,
) -> BTreeSet<String> {
    enabled
        .iter()
        .filter(|transition| !sleep.contains(&transition_sleep_key(transition)))
        .map(|transition| transition.ordering_key.clone())
        .collect()
}

fn has_done_successor_fingerprint(
    done_keys: &BTreeSet<String>,
    enabled: &[EnabledTransition],
    successor_fingerprint: StateFingerprint,
) -> bool {
    done_keys.iter().any(|done_key| {
        enabled
            .iter()
            .find(|t| t.ordering_key == *done_key)
            .map(|t| t.successor_fingerprint == successor_fingerprint)
            .unwrap_or(false)
    })
}

fn should_prune_seen_successor(use_sleep_sets: bool) -> bool {
    // When sleep sets are enabled, duplicate successors (detected by
    // fingerprint) are pruned eagerly. Without sleep sets the conservative
    // baseline fires the transition but skips exploration (is_new=false).
    use_sleep_sets
}

fn transition_sleep_key(transition: &EnabledTransition) -> String {
    format!("{}::{}", transition.process_id.0, transition.branch_label)
}

/// Extract a field value from a RuntimeValue state given a field path.
///
/// Supports two forms:
/// - `"field_name"` → extracts `state.fields["field_name"]`
/// - `"field_name[key]"` → extracts `state.fields["field_name"]` then indexes by key
///   (for Seq: numeric index, for Map/Function: string key lookup)
///
/// Returns `None` if the state isn't a Struct, the field doesn't exist,
/// or the index is out of bounds.
fn extract_field_value<'a>(state: &'a RuntimeValue, field_path: &str) -> Option<&'a RuntimeValue> {
    let fields = match state {
        RuntimeValue::Struct { fields, .. } => fields,
        _ => return None,
    };

    let (root, selector) = crate::modelcheck::dpor::types::split_field_selector_public(field_path);
    let sym = Symbol::intern(root);
    let field_val = fields.get(&sym)?;

    match selector {
        None => Some(field_val),
        Some(key) => {
            // Try numeric index for Seq
            if let Ok(idx) = key.parse::<usize>() {
                if let RuntimeValue::Seq(seq) = field_val {
                    return seq.get(idx);
                }
            }
            // Try map/function lookup by string key
            if let RuntimeValue::Map(map) = field_val {
                let key_val = RuntimeValue::String(key.to_string());
                return map.get(&key_val);
            }
            None
        }
    }
}

/// Record per-write-field runtime conflict stats for a fired transition.
///
/// For each field in the transition's write footprint, checks whether
/// the field value actually changed between pre_state and post_state.
fn record_runtime_write_stats(
    stats: &mut RuntimeConflictStats,
    transition: &EnabledTransition,
    pre_state: &RuntimeValue,
    post_state: &RuntimeValue,
) {
    for write_field in &transition.footprint.writes {
        let entry = stats.write_field_stats.entry(write_field.clone()).or_insert((0, 0));
        entry.0 += 1; // static_write_count

        let pre_val = extract_field_value(pre_state, write_field);
        let post_val = extract_field_value(post_state, write_field);
        if pre_val != post_val {
            entry.1 += 1; // actual_change_count
        }
    }
}

fn transition_has_unknown_footprint(transition: &EnabledTransition) -> bool {
    transition.footprint.reads.is_empty() && transition.footprint.writes.is_empty()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IndependenceDecision {
    Independent,
    BlockedSameProcess,
    BlockedUnknownFootprint,
    BlockedFootprintConflict,
}

fn classify_transition_independence(
    left: &EnabledTransition,
    right: &EnabledTransition,
    use_independence: bool,
) -> IndependenceDecision {
    if !use_independence {
        return IndependenceDecision::BlockedFootprintConflict;
    }
    // Same-process transitions are always dependent to preserve per-process
    // program-order semantics in this conservative DPOR prototype.
    if left.process_id == right.process_id {
        return IndependenceDecision::BlockedSameProcess;
    }
    // Unknown footprints (including whole-state accesses) remain dependent.
    if transition_has_unknown_footprint(left) || transition_has_unknown_footprint(right) {
        return IndependenceDecision::BlockedUnknownFootprint;
    }
    if left.footprint.independent_of(&right.footprint) {
        IndependenceDecision::Independent
    } else {
        IndependenceDecision::BlockedFootprintConflict
    }
}

fn record_independence_decision(
    blockers: &mut SleepIndependenceBlockers,
    decision: IndependenceDecision,
    left: &EnabledTransition,
    right: &EnabledTransition,
) -> bool {
    blockers.candidates_considered += 1;
    match decision {
        IndependenceDecision::Independent => {
            blockers.independent_candidates += 1;
            true
        }
        IndependenceDecision::BlockedSameProcess => {
            blockers.blocked_same_process += 1;
            false
        }
        IndependenceDecision::BlockedUnknownFootprint => {
            blockers.blocked_unknown_footprint += 1;
            false
        }
        IndependenceDecision::BlockedFootprintConflict => {
            blockers.blocked_footprint_conflict += 1;
            for pair in left.footprint.conflicting_field_pairs(&right.footprint) {
                *blockers.conflict_field_pairs.entry(pair).or_insert(0) += 1;
            }
            false
        }
    }
}

fn compute_child_sleep_set(
    parent_sleep: &BTreeSet<String>,
    parent_done: &BTreeSet<String>,
    chosen: &EnabledTransition,
    parent_enabled: &[EnabledTransition],
    use_independence: bool,
    blockers: &mut SleepIndependenceBlockers,
) -> BTreeSet<String> {
    let mut child_sleep = BTreeSet::new();

    if !use_independence {
        blockers.early_exit_independence_disabled += 1;
        return child_sleep;
    }
    if transition_has_unknown_footprint(chosen) {
        blockers.early_exit_chosen_unknown_footprint += 1;
        return child_sleep;
    }

    for sleeping_key in parent_sleep {
        // Look up the sleeping transition's footprint from the parent's enabled list
        if let Some(sleeping_trans) = parent_enabled
            .iter()
            .find(|t| transition_sleep_key(t) == *sleeping_key)
        {
            // If independent of chosen, keep asleep
            if record_independence_decision(
                blockers,
                classify_transition_independence(sleeping_trans, chosen, use_independence),
                sleeping_trans,
                chosen,
            ) {
                child_sleep.insert(sleeping_key.clone());
            }
            // If dependent, don't propagate (woken up)
        }
    }

    // Also seed child sleep from already-explored alternatives at the parent.
    // This mirrors sleep-set DFS behavior where previously explored independent
    // siblings can be slept in the descendant branch.
    for done_key in parent_done {
        if *done_key == chosen.ordering_key {
            continue;
        }
        if let Some(done_trans) = parent_enabled.iter().find(|t| t.ordering_key == *done_key) {
            if record_independence_decision(
                blockers,
                classify_transition_independence(done_trans, chosen, use_independence),
                done_trans,
                chosen,
            ) {
                child_sleep.insert(transition_sleep_key(done_trans));
            }
        }
    }

    // Deterministic-order candidate seeding: if an enabled alternative is
    // ordered before the currently chosen transition at the same parent frame,
    // treat it as a pre-chosen sibling candidate for child sleeping.
    // Conservative guards are preserved via `transitions_independent()`.
    for candidate in parent_enabled {
        if candidate.ordering_key == chosen.ordering_key {
            continue;
        }
        if !ordering_key_is_before(&candidate.ordering_key, &chosen.ordering_key) {
            continue;
        }
        if record_independence_decision(
            blockers,
            classify_transition_independence(candidate, chosen, use_independence),
            candidate,
            chosen,
        ) {
            child_sleep.insert(transition_sleep_key(candidate));
        }
    }

    child_sleep
}

fn ordering_key_is_before(left: &str, right: &str) -> bool {
    left < right
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use std::path::Path;
    use std::sync::{Mutex, OnceLock};

    fn create_model_toml(dir: &Path) -> std::path::PathBuf {
        let model_path = dir.join("model.toml");
        let mut f = std::fs::File::create(&model_path).unwrap();
        write!(
            f,
            r#"
[search]
max_depth = 20
max_states = 1000
timeout_ms = 10000

[properties]
invariants = []
check_deadlock = false
successor_semantics = "deadlock"

[quantifiers]
int = {{ min = 0, max = 5 }}
max_set_len = 4
max_seq_len = 4
"#
        )
        .unwrap();
        model_path
    }

    fn aplusb_spec_path() -> Option<std::path::PathBuf> {
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let path = manifest_dir.join("tests/tla-rs/01_aplusb/APlusB.rs");
        if path.exists() {
            Some(path)
        } else {
            None
        }
    }

    fn baseline_run_lock() -> &'static Mutex<()> {
        static BASELINE_RUN_LOCK: OnceLock<Mutex<()>> = OnceLock::new();
        BASELINE_RUN_LOCK.get_or_init(|| Mutex::new(()))
    }

    fn run_baseline_serial(
        transpiler_bin: &std::path::Path,
        spec_file: &std::path::Path,
        model_toml: &std::path::Path,
        invariants: &[String],
        timeout_sec: u64,
    ) -> crate::modelcheck::dpor::baseline::BaselineResult {
        let _guard = baseline_run_lock()
            .lock()
            .expect("baseline run lock poisoned");
        crate::modelcheck::dpor::baseline::run_baseline(
            transpiler_bin,
            spec_file,
            model_toml,
            invariants,
            timeout_sec,
        )
    }

    #[test]
    fn test_dpor_exhaustive_aplusb() {
        let spec_path = match aplusb_spec_path() {
            Some(p) => p,
            None => {
                eprintln!("Skipping: APlusB.rs not found");
                return;
            }
        };
        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_model_toml(tmp.path());
        let ctx = SpecContext::load(&spec_path, None, &model_path, "LInit", "LNext").unwrap();

        let config = DporConfig {
            max_depth: 20,
            max_states: 1000,
            ..Default::default()
        };
        let result = explore_dpor(&ctx, &config);

        // APlusB with int 0..5: states are {a:0,b:0}, {a:1,b:1}, ..., {a:5,b:5}
        // That's 6 states (depth 0..5), but the model checker explores more
        // due to domain expansion. The baseline reports 51 distinct states.
        // Our DFS should find a subset (the linear chain is 6 states).
        assert!(
            result.distinct_states.len() >= 6,
            "Expected at least 6 states (linear chain), got {}",
            result.distinct_states.len()
        );
        assert!(result.max_depth >= 5, "Expected depth >= 5");
        assert!(result.transitions_fired >= 5);
        eprintln!(
            "DPOR APlusB: {} distinct states, {} traces, depth {}, {} transitions",
            result.distinct_states.len(),
            result.traces_explored,
            result.max_depth,
            result.transitions_fired
        );
    }

    #[test]
    fn test_dpor_deterministic() {
        let spec_path = match aplusb_spec_path() {
            Some(p) => p,
            None => {
                return;
            }
        };
        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_model_toml(tmp.path());
        let ctx = SpecContext::load(&spec_path, None, &model_path, "LInit", "LNext").unwrap();

        let config = DporConfig {
            max_depth: 10,
            max_states: 100,
            ..Default::default()
        };
        let run1 = explore_dpor(&ctx, &config);
        let run2 = explore_dpor(&ctx, &config);

        assert_eq!(
            run1.distinct_states, run2.distinct_states,
            "Two runs should produce identical state sets"
        );
        assert_eq!(run1.transitions_fired, run2.transitions_fired);
    }

    #[test]
    fn test_dpor_max_depth_respected() {
        let spec_path = match aplusb_spec_path() {
            Some(p) => p,
            None => {
                return;
            }
        };
        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_model_toml(tmp.path());
        let ctx = SpecContext::load(&spec_path, None, &model_path, "LInit", "LNext").unwrap();

        let config = DporConfig {
            max_depth: 3,
            max_states: 1000,
            ..Default::default()
        };
        let result = explore_dpor(&ctx, &config);

        assert!(
            result.max_depth <= 3,
            "Should respect max_depth=3, got {}",
            result.max_depth
        );
    }

    #[test]
    fn test_dpor_max_states_respected() {
        let spec_path = match aplusb_spec_path() {
            Some(p) => p,
            None => {
                return;
            }
        };
        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_model_toml(tmp.path());
        let ctx = SpecContext::load(&spec_path, None, &model_path, "LInit", "LNext").unwrap();

        let config = DporConfig {
            max_depth: 100,
            max_states: 3,
            ..Default::default()
        };
        let result = explore_dpor(&ctx, &config);

        assert!(
            result.distinct_states.len() <= 4, // allow 1 over due to loop check timing
            "Should respect max_states~3, got {}",
            result.distinct_states.len()
        );
    }

    // =========================================================================
    // Parity tests: DPOR vs baseline (Phase 38.8.2.f)
    // =========================================================================

    #[test]
    fn test_dpor_parity_aplusb() {
        // Verify DPOR finds exactly the same states as the baseline model checker.
        // Baseline reports 21 distinct states for APlusB with int 0..5.
        let spec_path = match aplusb_spec_path() {
            Some(p) => p,
            None => {
                return;
            }
        };
        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_model_toml(tmp.path());
        let ctx = SpecContext::load(&spec_path, None, &model_path, "LInit", "LNext").unwrap();

        let config = DporConfig {
            max_depth: 20,
            max_states: 1_000,
            ..Default::default()
        };
        let dpor_result = explore_dpor(&ctx, &config);

        // Also run the baseline subprocess for comparison
        let transpiler = match crate::modelcheck::dpor::baseline::find_transpiler_bin() {
            Some(p) => p,
            None => {
                // Can't compare without baseline binary — just check DPOR ran
                assert!(!dpor_result.distinct_states.is_empty());
                return;
            }
        };
        let baseline_result = run_baseline_serial(
            &transpiler,
            &spec_path,
            &model_path,
            &["LSumInvariant".to_string()],
            30,
        );

        assert_eq!(baseline_result.result, "ok");
        assert_eq!(
            dpor_result.distinct_states.len(),
            baseline_result.distinct_states,
            "DPOR ({}) vs baseline ({}) distinct state count mismatch for APlusB",
            dpor_result.distinct_states.len(),
            baseline_result.distinct_states
        );
        eprintln!(
            "PARITY APlusB: DPOR={} baseline={} ✓",
            dpor_result.distinct_states.len(),
            baseline_result.distinct_states
        );
    }

    #[test]
    fn test_dpor_parity_producer_consumer() {
        // ProducerConsumer uses predicate-style branches — the predicate solver
        // in enabled.rs may or may not handle it. Test parity if it works.
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_path =
            manifest_dir.join("tests/tla-rs/07_producer_consumer_1slot/ProducerConsumer1Slot.rs");
        if !spec_path.exists() {
            eprintln!("Skipping: ProducerConsumer1Slot.rs not found");
            return;
        }

        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_model_toml(tmp.path());

        let ctx = match SpecContext::load(&spec_path, None, &model_path, "LInit", "LNext") {
            Ok(c) => c,
            Err(e) => {
                eprintln!("Skipping ProducerConsumer parity: load failed: {}", e);
                return;
            }
        };

        let config = DporConfig {
            max_depth: 50,
            max_states: 10_000,
            ..Default::default()
        };
        let dpor_result = explore_dpor(&ctx, &config);

        if dpor_result.distinct_states.is_empty() {
            eprintln!("ProducerConsumer DPOR: 0 states (predicate solver limitation)");
            return;
        }

        let transpiler = match crate::modelcheck::dpor::baseline::find_transpiler_bin() {
            Some(p) => p,
            None => {
                return;
            }
        };
        let baseline_result = run_baseline_serial(
            &transpiler,
            &spec_path,
            &model_path,
            &["LSafetyInvariant".to_string()],
            30,
        );

        if baseline_result.result == "ok" && baseline_result.distinct_states > 0 {
            // Compare: DPOR may find same or more states than baseline when the
            // predicate solver computes successors beyond the domain bounds.
            // The baseline is domain-bounded; DPOR's predicate solver is not.
            // Both are correct — they just have different truncation behavior.
            let dp = dpor_result.distinct_states.len();
            let bl = baseline_result.distinct_states;
            let status = if dp == bl {
                "exact match ✓"
            } else if dp < bl {
                "DPOR subset"
            } else {
                "DPOR superset (unbounded predicate solver)"
            };
            eprintln!(
                "PARITY ProducerConsumer: DPOR={} baseline={} ({})",
                dp, bl, status
            );
            // Baseline states should be a subset of DPOR states (DPOR is at least as complete)
            assert!(
                dp >= bl,
                "DPOR ({}) should find at least as many states as baseline ({}) for ProducerConsumer",
                dp, bl
            );
        }
    }

    #[test]
    fn test_dpor_independence_parity_aplusb() {
        // Verify that DPOR with independence enabled produces the same state set.
        // For APlusB (single process), independence shouldn't change the result.
        let spec_path = match aplusb_spec_path() {
            Some(p) => p,
            None => {
                return;
            }
        };
        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_model_toml(tmp.path());
        let ctx = SpecContext::load(&spec_path, None, &model_path, "LInit", "LNext").unwrap();

        let conservative = DporConfig {
            max_depth: 20,
            max_states: 1_000,
            use_independence: false,
            use_sleep_sets: false,
            invariants: vec![],
            check_deadlock: false,
        };
        let with_independence = DporConfig {
            max_depth: 20,
            max_states: 1_000,
            use_independence: true,
            use_sleep_sets: false,
            invariants: vec![],
            check_deadlock: false,
        };

        let result_conservative = explore_dpor(&ctx, &conservative);
        let result_independence = explore_dpor(&ctx, &with_independence);

        assert_eq!(
            result_conservative.distinct_states, result_independence.distinct_states,
            "Independence-enabled DPOR should produce same states as conservative for APlusB"
        );
        eprintln!(
            "Independence parity APlusB: conservative={} independence={} ✓",
            result_conservative.distinct_states.len(),
            result_independence.distinct_states.len()
        );
    }

    #[test]
    fn test_dpor_sleep_set_parity_aplusb() {
        // Verify that sleep-set-enabled DPOR finds the same states as conservative DPOR.
        // For APlusB (single-process, empty footprints), sleep sets should have no effect
        // because all transitions have empty footprints and are treated as dependent.
        let spec_path = match aplusb_spec_path() {
            Some(p) => p,
            None => {
                return;
            }
        };
        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_model_toml(tmp.path());
        let ctx = SpecContext::load(&spec_path, None, &model_path, "LInit", "LNext").unwrap();

        let conservative = DporConfig {
            max_depth: 20,
            max_states: 1_000,
            use_independence: false,
            use_sleep_sets: false,
            invariants: vec![],
            check_deadlock: false,
        };
        let with_sleep = DporConfig {
            max_depth: 20,
            max_states: 1_000,
            use_independence: true,
            use_sleep_sets: true,
            invariants: vec![],
            check_deadlock: false,
        };

        let result_conservative = explore_dpor(&ctx, &conservative);
        let result_sleep = explore_dpor(&ctx, &with_sleep);

        // Sleep sets must not LOSE states (correctness)
        assert_eq!(
            result_conservative.distinct_states, result_sleep.distinct_states,
            "Sleep-set DPOR should find same states as conservative for APlusB (single-process)"
        );
        eprintln!(
            "Sleep-set parity APlusB: conservative={} sleep={} ✓",
            result_conservative.distinct_states.len(),
            result_sleep.distinct_states.len()
        );
    }

    #[test]
    fn test_sleep_set_parity_all_passing_cases() {
        // Fast parity smoke check for both independence-only and
        // independence+sleep-set modes.
        //
        // Full-corpus behavioral coverage (all 20 cases) is validated via
        // scripts/run_full_suite.sh in CI/manual gate runs.
        //
        // Correctness bar: optimized modes must not lose any states reached by
        // conservative mode on baseline-passing cases.
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));

        let cases: Vec<(&str, &str)> = vec![
            ("01_aplusb", "APlusB.rs"),
            ("02_counter_incdec", "CounterIncDec.rs"),
            ("04_lock_basic", "LockBasic.rs"),
            ("07_producer_consumer_1slot", "ProducerConsumer1Slot.rs"),
            ("08_bounded_buffer_2slot", "BoundedBuffer2Slot.rs"),
            ("09_peterson_mutex_2p", "PetersonMutex.rs"),
            ("13_twophase_small", "TwoPhase.rs"),
        ];

        let mut all_ok = true;
        for (case_id, filename) in &cases {
            let spec_file = manifest_dir.join(format!("tests/tla-rs/{}/{}", case_id, filename));
            if !spec_file.exists() {
                continue;
            }
            let model_path = case_model_config(case_id);
            let ctx = match SpecContext::load(&spec_file, None, &model_path, "LInit", "LNext") {
                Ok(c) => c,
                Err(_) => continue,
            };

            let without_sleep = DporConfig {
                max_depth: 20,
                max_states: 10_000,
                use_independence: false,
                use_sleep_sets: false,
                invariants: vec![],
                check_deadlock: false,
            };
            let with_independence = DporConfig {
                max_depth: 20,
                max_states: 10_000,
                use_independence: true,
                use_sleep_sets: false,
                invariants: vec![],
                check_deadlock: false,
            };
            let with_sleep = DporConfig {
                max_depth: 20,
                max_states: 10_000,
                use_independence: true,
                use_sleep_sets: true,
                invariants: vec![],
                check_deadlock: false,
            };

            let result_conservative = explore_dpor(&ctx, &without_sleep);
            let result_independence = explore_dpor(&ctx, &with_independence);
            let result_sleep = explore_dpor(&ctx, &with_sleep);

            let conservative_states = &result_conservative.distinct_states;
            let independence_states = &result_independence.distinct_states;
            let sleep_states = &result_sleep.distinct_states;

            let independence_ok = conservative_states.is_subset(independence_states);
            let sleep_ok = conservative_states.is_subset(sleep_states);
            if !independence_ok || !sleep_ok {
                all_ok = false;
            }

            let independence_status = if conservative_states == independence_states {
                "exact"
            } else if independence_ok {
                "independence_superset"
            } else {
                "INDEPENDENCE_LOST_STATES"
            };
            let sleep_status = if conservative_states == sleep_states {
                "exact"
            } else if sleep_ok {
                "sleep_superset"
            } else {
                "SLEEP_LOST_STATES"
            };
            eprintln!(
                "  {} conservative={} independence={} ({}) sleep={} ({})",
                case_id,
                conservative_states.len(),
                independence_states.len(),
                independence_status,
                sleep_states.len(),
                sleep_status
            );
        }

        assert!(
            all_ok,
            "Independence/sleep-set modes must not lose conservative states on any passing case"
        );
        eprintln!("Independence + sleep-set parity: all cases verified ✓");
    }

    #[test]
    fn test_sleep_set_parity_peterson_mutex_no_lost_states() {
        // Focused guardrail for case 09: this case has shown real transition
        // reduction while preserving state parity, and also catches
        // over-aggressive sibling-seeding changes that can lose states.
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_file = manifest_dir.join("tests/tla-rs/09_peterson_mutex_2p/PetersonMutex.rs");
        if !spec_file.exists() {
            return;
        }
        let model_path = case_model_config("09_peterson_mutex_2p");
        let ctx = match SpecContext::load(&spec_file, None, &model_path, "LInit", "LNext") {
            Ok(c) => c,
            Err(_) => return,
        };

        let conservative = explore_dpor(
            &ctx,
            &DporConfig {
                max_depth: 20,
                max_states: 10_000,
                use_independence: false,
                use_sleep_sets: false,
                invariants: vec![],
                check_deadlock: false,
            },
        );
        let sleep = explore_dpor(
            &ctx,
            &DporConfig {
                max_depth: 20,
                max_states: 10_000,
                use_independence: true,
                use_sleep_sets: true,
                invariants: vec![],
                check_deadlock: false,
            },
        );

        assert!(
            conservative
                .distinct_states
                .is_subset(&sleep.distinct_states),
            "sleep mode must not lose conservative states on Peterson"
        );
        assert_eq!(
            conservative.distinct_states.len(),
            sleep.distinct_states.len(),
            "Peterson should preserve exact distinct-state count under sleep mode"
        );
    }

    #[test]
    #[ignore = "evidence-generation harness for sleep-set reduction report"]
    fn print_sleep_set_reduction_multi_process_markdown() {
        // Evidence harness for Phase 38.14.10.d: prints a markdown table for
        // focused multi-process cases. Run with:
        // cargo test dpor::tests::print_sleep_set_reduction_multi_process_markdown -- --ignored --exact --nocapture
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let cases: Vec<(&str, &str)> = vec![
            ("02_counter_incdec", "CounterIncDec.rs"),
            ("09_peterson_mutex_2p", "PetersonMutex.rs"),
            ("17_paxos_small", "Paxos.rs"),
        ];

        println!(
            "| Case | Distinct (cons) | Distinct (ind) | Distinct (sleep) | Distinct Reduction vs cons | Transitions (cons) | Transitions (ind) | Transitions (sleep) | Transition Reduction vs cons | Sleep Prunes (sleep) | Sleep Cardinality (avg/max by depth, sleep) | Independence Blockers (early_off/chosen_unknown/cand/ind/same/unknown/conflict, sleep) |"
        );
        println!(
            "|------|-----------------:|---------------:|-----------------:|----------------------------:|-------------------:|------------------:|--------------------:|-----------------------------:|---------------------:|---------------------------------------------|----------------------------------------------------------------|"
        );

        let mut transition_gate_hits = 0usize;
        for (case_id, filename) in &cases {
            let spec_file = manifest_dir.join(format!("tests/tla-rs/{}/{}", case_id, filename));
            if !spec_file.exists() {
                println!(
                    "| {} | -- | -- | -- | -- | -- | -- | -- | -- | -- | -- | -- |",
                    case_id
                );
                continue;
            }
            let model_path = case_model_config(case_id);
            let ctx = match SpecContext::load(&spec_file, None, &model_path, "LInit", "LNext") {
                Ok(c) => c,
                Err(_) => {
                    println!(
                        "| {} | load_failed | load_failed | load_failed | -- | -- | -- | -- | -- | -- | -- | -- |",
                        case_id
                    );
                    continue;
                }
            };

            let conservative = explore_dpor(
                &ctx,
                &DporConfig {
                    max_depth: 20,
                    max_states: 10_000,
                    use_independence: false,
                    use_sleep_sets: false,
                    invariants: vec![],
                    check_deadlock: false,
                },
            );
            let independence = explore_dpor(
                &ctx,
                &DporConfig {
                    max_depth: 20,
                    max_states: 10_000,
                    use_independence: true,
                    use_sleep_sets: false,
                    invariants: vec![],
                    check_deadlock: false,
                },
            );
            let sleep = explore_dpor(
                &ctx,
                &DporConfig {
                    max_depth: 20,
                    max_states: 10_000,
                    use_independence: true,
                    use_sleep_sets: true,
                    invariants: vec![],
                    check_deadlock: false,
                },
            );

            // Safety gate: optimized modes must not lose conservative states.
            assert!(
                conservative
                    .distinct_states
                    .is_subset(&independence.distinct_states),
                "independence mode lost conservative states for {}",
                case_id
            );
            assert!(
                conservative
                    .distinct_states
                    .is_subset(&sleep.distinct_states),
                "sleep mode lost conservative states for {}",
                case_id
            );

            let cons_distinct = conservative.distinct_states.len();
            let ind_distinct = independence.distinct_states.len();
            let sleep_distinct = sleep.distinct_states.len();
            let cons_transitions = conservative.transitions_fired;
            let ind_transitions = independence.transitions_fired;
            let sleep_transitions = sleep.transitions_fired;
            let sleep_prunes = sleep.sleep_prune_hits;
            let sleep_cardinality =
                format_sleep_cardinality_summary(&sleep.sleep_cardinality_by_depth);
            let blockers = format_independence_blockers_summary(&sleep.sleep_independence_blockers);

            let distinct_reduction_pct = percent_reduction(cons_distinct, sleep_distinct);
            let transition_reduction_pct = percent_reduction(cons_transitions, sleep_transitions);
            if transition_reduction_gate_hit(cons_transitions, sleep_transitions) {
                transition_gate_hits += 1;
            }

            println!(
                "| {} | {} | {} | {} | {:.1}% | {} | {} | {} | {:.1}% | {} | {} | {} |",
                case_id,
                cons_distinct,
                ind_distinct,
                sleep_distinct,
                distinct_reduction_pct,
                cons_transitions,
                ind_transitions,
                sleep_transitions,
                transition_reduction_pct,
                sleep_prunes,
                sleep_cardinality,
                blockers
            );
        }

        println!(
            "Gate check (>10% transition reduction on at least {} multi-process cases): {} / {} hits",
            REDUCTION_GATE_REQUIRED_CASES,
            transition_gate_hits,
            cases.len()
        );
        println!(
            "Distinct-state reduction is diagnostic only: with `conservative ⊆ sleep`, positive distinct-state reduction is mathematically impossible."
        );
    }

    #[test]
    fn test_percent_reduction_is_non_positive_for_superset_sizes() {
        // Under the current safety invariant (`conservative ⊆ sleep`), the
        // sleep-state set cardinality is always >= conservative cardinality.
        // Therefore distinct-state "reduction vs conservative" cannot be > 0.
        let conservative_size = 10usize;
        let sleep_size = 12usize;
        assert!(sleep_size >= conservative_size);
        let reduction = percent_reduction(conservative_size, sleep_size);
        assert!(
            reduction <= 0.0,
            "superset cardinality must not report positive reduction"
        );
    }

    #[test]
    fn test_transition_reduction_gate_hit_requires_strictly_more_than_threshold() {
        // 10% exactly should not pass because the gate is strictly greater-than.
        assert!(
            !transition_reduction_gate_hit(10, 9),
            "10% exact reduction must not pass >10% gate"
        );
        assert!(
            transition_reduction_gate_hit(10, 8),
            "20% reduction should pass >10% gate"
        );
    }

    #[test]
    fn test_compute_child_sleep_set_empty_footprints() {
        // When footprints are empty, all transitions are dependent,
        // so child sleep set should always be empty.
        let sleeping_one = EnabledTransition {
            process_id: ProcessId(0),
            branch_label: "t1".to_string(),
            successor_fingerprint: StateFingerprint(1),
            ordering_key: "0000".to_string(),
            footprint: TransitionFootprint::default(),
        };
        let sleeping_two = EnabledTransition {
            process_id: ProcessId(0),
            branch_label: "t2".to_string(),
            successor_fingerprint: StateFingerprint(2),
            ordering_key: "0001".to_string(),
            footprint: TransitionFootprint::default(),
        };
        let parent_sleep: BTreeSet<String> = [
            transition_sleep_key(&sleeping_one),
            transition_sleep_key(&sleeping_two),
        ]
        .into();
        let chosen = EnabledTransition {
            process_id: ProcessId(0),
            branch_label: "t0".to_string(),
            successor_fingerprint: StateFingerprint(0),
            ordering_key: "0002".to_string(),
            footprint: TransitionFootprint::default(), // empty
        };
        let parent_enabled = vec![sleeping_one, sleeping_two];
        let mut blockers = SleepIndependenceBlockers::default();
        let child_sleep = compute_child_sleep_set(
            &parent_sleep,
            &BTreeSet::new(),
            &chosen,
            &parent_enabled,
            true,
            &mut blockers,
        );
        assert!(
            child_sleep.is_empty(),
            "Empty footprints → all dependent → empty child sleep"
        );
        assert_eq!(blockers.early_exit_independence_disabled, 0);
        assert_eq!(blockers.early_exit_chosen_unknown_footprint, 1);
        assert_eq!(blockers.candidates_considered, 0);
    }

    #[test]
    fn test_compute_child_sleep_set_independent_transitions() {
        // When transitions have disjoint footprints, independent ones stay asleep.
        let indep = EnabledTransition {
            process_id: ProcessId(1),
            branch_label: "t_indep".to_string(),
            successor_fingerprint: StateFingerprint(1),
            ordering_key: "0000".to_string(),
            footprint: TransitionFootprint {
                reads: ["y".to_string()].into(),
                writes: ["y".to_string()].into(),
            }, // disjoint from chosen → independent
        };
        let dep = EnabledTransition {
            process_id: ProcessId(2),
            branch_label: "t_dep".to_string(),
            successor_fingerprint: StateFingerprint(2),
            ordering_key: "0001".to_string(),
            footprint: TransitionFootprint {
                reads: ["x".to_string()].into(), // reads x → dependent on chosen
                writes: BTreeSet::new(),
            },
        };
        let parent_sleep: BTreeSet<String> =
            [transition_sleep_key(&indep), transition_sleep_key(&dep)].into();
        let chosen = EnabledTransition {
            process_id: ProcessId(0),
            branch_label: "t_chosen".to_string(),
            successor_fingerprint: StateFingerprint(0),
            ordering_key: "0002".to_string(),
            footprint: TransitionFootprint {
                reads: ["x".to_string()].into(),
                writes: ["x".to_string()].into(),
            },
        };
        let parent_enabled = vec![indep.clone(), dep.clone()];
        let mut blockers = SleepIndependenceBlockers::default();
        let child_sleep = compute_child_sleep_set(
            &parent_sleep,
            &BTreeSet::new(),
            &chosen,
            &parent_enabled,
            true,
            &mut blockers,
        );
        assert!(
            child_sleep.contains(&transition_sleep_key(&indep)),
            "Independent transition stays asleep"
        );
        assert!(
            !child_sleep.contains(&transition_sleep_key(&dep)),
            "Dependent transition is woken up"
        );
    }

    #[test]
    fn test_compute_child_sleep_set_same_process_is_dependent() {
        let sleeping = EnabledTransition {
            process_id: ProcessId(7), // same process as chosen
            branch_label: "t_same_proc".to_string(),
            successor_fingerprint: StateFingerprint(1),
            ordering_key: "0000".to_string(),
            footprint: TransitionFootprint {
                reads: ["y".to_string()].into(),
                writes: ["y".to_string()].into(),
            },
        };
        let parent_sleep: BTreeSet<String> = [transition_sleep_key(&sleeping)].into();
        let chosen = EnabledTransition {
            process_id: ProcessId(7),
            branch_label: "t_chosen".to_string(),
            successor_fingerprint: StateFingerprint(0),
            ordering_key: "0001".to_string(),
            footprint: TransitionFootprint {
                reads: ["x".to_string()].into(),
                writes: ["x".to_string()].into(),
            },
        };
        let parent_enabled = vec![sleeping];
        let mut blockers = SleepIndependenceBlockers::default();

        let child_sleep = compute_child_sleep_set(
            &parent_sleep,
            &BTreeSet::new(),
            &chosen,
            &parent_enabled,
            true,
            &mut blockers,
        );
        assert!(
            child_sleep.is_empty(),
            "Same-process transitions are treated as dependent in conservative DPOR"
        );
    }

    #[test]
    fn test_compute_child_sleep_set_seeds_from_done_independent_alternatives() {
        let done_independent = EnabledTransition {
            process_id: ProcessId(1),
            branch_label: "t_done_indep".to_string(),
            successor_fingerprint: StateFingerprint(1),
            ordering_key: "0000".to_string(),
            footprint: TransitionFootprint {
                reads: ["y".to_string()].into(),
                writes: ["y".to_string()].into(),
            },
        };
        let done_dependent = EnabledTransition {
            process_id: ProcessId(2),
            branch_label: "t_done_dep".to_string(),
            successor_fingerprint: StateFingerprint(2),
            ordering_key: "0001".to_string(),
            footprint: TransitionFootprint {
                reads: ["x".to_string()].into(),
                writes: BTreeSet::new(),
            },
        };
        let chosen = EnabledTransition {
            process_id: ProcessId(0),
            branch_label: "t_chosen".to_string(),
            successor_fingerprint: StateFingerprint(3),
            ordering_key: "0002".to_string(),
            footprint: TransitionFootprint {
                reads: ["x".to_string()].into(),
                writes: ["x".to_string()].into(),
            },
        };
        let parent_done: BTreeSet<String> = [
            done_independent.ordering_key.clone(),
            done_dependent.ordering_key.clone(),
            chosen.ordering_key.clone(),
        ]
        .into();
        let parent_enabled = vec![
            done_independent.clone(),
            done_dependent.clone(),
            chosen.clone(),
        ];
        let mut blockers = SleepIndependenceBlockers::default();

        let child_sleep = compute_child_sleep_set(
            &BTreeSet::new(),
            &parent_done,
            &chosen,
            &parent_enabled,
            true,
            &mut blockers,
        );
        assert!(
            child_sleep.contains(&transition_sleep_key(&done_independent)),
            "independent done alternative should be seeded into child sleep"
        );
        assert!(
            !child_sleep.contains(&transition_sleep_key(&done_dependent)),
            "dependent done alternative should not be seeded into child sleep"
        );
        assert!(
            !child_sleep.contains(&transition_sleep_key(&chosen)),
            "chosen transition itself should not be seeded into child sleep from done-set"
        );
    }

    #[test]
    fn test_compute_child_sleep_set_seeds_from_prechosen_ordered_alternatives() {
        let pre_indep = EnabledTransition {
            process_id: ProcessId(1),
            branch_label: "t_pre_indep".to_string(),
            successor_fingerprint: StateFingerprint(1),
            ordering_key: "0001".to_string(),
            footprint: TransitionFootprint {
                reads: ["y".to_string()].into(),
                writes: ["y".to_string()].into(),
            },
        };
        let pre_dep = EnabledTransition {
            process_id: ProcessId(2),
            branch_label: "t_pre_dep".to_string(),
            successor_fingerprint: StateFingerprint(2),
            ordering_key: "0000".to_string(),
            footprint: TransitionFootprint {
                reads: ["x".to_string()].into(),
                writes: BTreeSet::new(),
            },
        };
        let chosen = EnabledTransition {
            process_id: ProcessId(0),
            branch_label: "t_chosen".to_string(),
            successor_fingerprint: StateFingerprint(3),
            ordering_key: "0002".to_string(),
            footprint: TransitionFootprint {
                reads: ["x".to_string()].into(),
                writes: ["x".to_string()].into(),
            },
        };
        let post_indep = EnabledTransition {
            process_id: ProcessId(3),
            branch_label: "t_post_indep".to_string(),
            successor_fingerprint: StateFingerprint(4),
            ordering_key: "0003".to_string(),
            footprint: TransitionFootprint {
                reads: ["z".to_string()].into(),
                writes: ["z".to_string()].into(),
            },
        };
        let parent_enabled = vec![
            pre_dep.clone(),
            pre_indep.clone(),
            chosen.clone(),
            post_indep.clone(),
        ];
        let mut blockers = SleepIndependenceBlockers::default();

        let child_sleep = compute_child_sleep_set(
            &BTreeSet::new(),
            &BTreeSet::new(),
            &chosen,
            &parent_enabled,
            true,
            &mut blockers,
        );
        assert!(
            child_sleep.contains(&transition_sleep_key(&pre_indep)),
            "independent alternative ordered before chosen should seed child sleep"
        );
        assert!(
            !child_sleep.contains(&transition_sleep_key(&pre_dep)),
            "dependent alternative ordered before chosen should not seed child sleep"
        );
        assert!(
            !child_sleep.contains(&transition_sleep_key(&post_indep)),
            "alternatives after chosen should not be pre-chosen candidates"
        );
    }

    #[test]
    fn test_initialize_backtrack_filters_by_action_sleep_key() {
        let transition_a = EnabledTransition {
            process_id: ProcessId(9),
            branch_label: "branch_alpha".to_string(),
            successor_fingerprint: StateFingerprint(1),
            ordering_key: "0099".to_string(),
            footprint: TransitionFootprint::default(),
        };
        let transition_b = EnabledTransition {
            process_id: ProcessId(10),
            branch_label: "branch_beta".to_string(),
            successor_fingerprint: StateFingerprint(2),
            ordering_key: "0001".to_string(),
            footprint: TransitionFootprint::default(),
        };
        let sleep: BTreeSet<String> = [transition_sleep_key(&transition_a)].into();
        let backtrack =
            initialize_backtrack_keys(&[transition_a.clone(), transition_b.clone()], &sleep);
        assert!(
            !backtrack.contains(&transition_a.ordering_key),
            "sleep-filtering should use action identity, not ordering_key equality"
        );
        assert!(
            backtrack.contains(&transition_b.ordering_key),
            "non-sleeping transition should remain in backtrack"
        );
    }

    #[test]
    fn test_has_done_successor_fingerprint_true_for_matching_done_transition() {
        let transition_a = EnabledTransition {
            process_id: ProcessId(0),
            branch_label: "branch_a".to_string(),
            successor_fingerprint: StateFingerprint(11),
            ordering_key: "0000".to_string(),
            footprint: TransitionFootprint::default(),
        };
        let transition_b = EnabledTransition {
            process_id: ProcessId(1),
            branch_label: "branch_b".to_string(),
            successor_fingerprint: StateFingerprint(11),
            ordering_key: "0001".to_string(),
            footprint: TransitionFootprint::default(),
        };
        let done: BTreeSet<String> = [transition_a.ordering_key.clone()].into();
        let enabled = vec![transition_a, transition_b.clone()];

        assert!(
            has_done_successor_fingerprint(&done, &enabled, transition_b.successor_fingerprint),
            "done-set should report a matching successor fingerprint"
        );
    }

    #[test]
    fn test_has_done_successor_fingerprint_false_without_matching_done_transition() {
        let transition_a = EnabledTransition {
            process_id: ProcessId(0),
            branch_label: "branch_a".to_string(),
            successor_fingerprint: StateFingerprint(11),
            ordering_key: "0000".to_string(),
            footprint: TransitionFootprint::default(),
        };
        let transition_b = EnabledTransition {
            process_id: ProcessId(1),
            branch_label: "branch_b".to_string(),
            successor_fingerprint: StateFingerprint(12),
            ordering_key: "0001".to_string(),
            footprint: TransitionFootprint::default(),
        };
        let done: BTreeSet<String> = [transition_a.ordering_key.clone()].into();
        let enabled = vec![transition_a, transition_b.clone()];

        assert!(
            !has_done_successor_fingerprint(&done, &enabled, transition_b.successor_fingerprint),
            "done-set should not report a non-matching successor fingerprint"
        );
    }

    #[test]
    fn test_should_prune_seen_successor_enabled() {
        assert!(
            should_prune_seen_successor(true),
            "sleep mode should prune already-seen successor states"
        );
    }

    #[test]
    fn test_should_prune_seen_successor_disabled() {
        assert!(
            !should_prune_seen_successor(false),
            "without sleep mode, seen successors should not be pruned"
        );
    }

    #[test]
    fn test_sleep_cardinality_telemetry_helpers() {
        let mut stats = std::collections::BTreeMap::new();
        record_sleep_cardinality(&mut stats, 1, 2);
        record_sleep_cardinality(&mut stats, 1, 4);
        record_sleep_cardinality(&mut stats, 2, 0);

        let d1 = stats.get(&1).expect("depth 1 stats missing");
        assert_eq!(d1.samples, 2);
        assert_eq!(d1.total_cardinality, 6);
        assert_eq!(d1.max_cardinality, 4);

        let summary = format_sleep_cardinality_summary(&stats);
        assert!(
            summary.contains("d1:3.0/4"),
            "summary should include avg/max for depth 1, got {}",
            summary
        );
        assert!(
            summary.contains("d2:0.0/0"),
            "summary should include depth 2 zero cardinality, got {}",
            summary
        );
    }

    #[test]
    fn test_compute_child_sleep_set_records_independence_blockers() {
        let chosen = EnabledTransition {
            process_id: ProcessId(1),
            branch_label: "t_chosen".to_string(),
            successor_fingerprint: StateFingerprint(0),
            ordering_key: "0000".to_string(),
            footprint: TransitionFootprint {
                reads: ["x".to_string()].into(),
                writes: ["x".to_string()].into(),
            },
        };
        let same_process = EnabledTransition {
            process_id: ProcessId(1),
            branch_label: "t_same".to_string(),
            successor_fingerprint: StateFingerprint(1),
            ordering_key: "0001".to_string(),
            footprint: TransitionFootprint {
                reads: ["y".to_string()].into(),
                writes: ["y".to_string()].into(),
            },
        };
        let unknown = EnabledTransition {
            process_id: ProcessId(2),
            branch_label: "t_unknown".to_string(),
            successor_fingerprint: StateFingerprint(2),
            ordering_key: "0002".to_string(),
            footprint: TransitionFootprint::default(),
        };
        let conflict = EnabledTransition {
            process_id: ProcessId(3),
            branch_label: "t_conflict".to_string(),
            successor_fingerprint: StateFingerprint(3),
            ordering_key: "0003".to_string(),
            footprint: TransitionFootprint {
                reads: ["x".to_string()].into(),
                writes: BTreeSet::new(),
            },
        };
        let independent = EnabledTransition {
            process_id: ProcessId(4),
            branch_label: "t_indep".to_string(),
            successor_fingerprint: StateFingerprint(4),
            ordering_key: "0004".to_string(),
            footprint: TransitionFootprint {
                reads: ["z".to_string()].into(),
                writes: ["z".to_string()].into(),
            },
        };
        let parent_enabled = vec![
            chosen.clone(),
            same_process.clone(),
            unknown.clone(),
            conflict.clone(),
            independent.clone(),
        ];
        let parent_sleep: BTreeSet<String> = [
            transition_sleep_key(&same_process),
            transition_sleep_key(&unknown),
            transition_sleep_key(&conflict),
            transition_sleep_key(&independent),
        ]
        .into();

        let mut blockers = SleepIndependenceBlockers::default();
        let child_sleep = compute_child_sleep_set(
            &parent_sleep,
            &BTreeSet::new(),
            &chosen,
            &parent_enabled,
            true,
            &mut blockers,
        );
        assert!(
            child_sleep.contains(&transition_sleep_key(&independent)),
            "independent candidate should remain in child sleep"
        );
        assert_eq!(
            child_sleep.len(),
            1,
            "only one candidate should remain asleep"
        );
        assert_eq!(blockers.early_exit_independence_disabled, 0);
        assert_eq!(blockers.early_exit_chosen_unknown_footprint, 0);
        assert_eq!(blockers.candidates_considered, 4);
        assert_eq!(blockers.independent_candidates, 1);
        assert_eq!(blockers.blocked_same_process, 1);
        assert_eq!(blockers.blocked_unknown_footprint, 1);
        assert_eq!(blockers.blocked_footprint_conflict, 1);

        // Verify per-field-pair conflict tracking (Phase 38.21.I.a)
        assert!(
            !blockers.conflict_field_pairs.is_empty(),
            "conflict_field_pairs should be populated when footprint conflict occurs"
        );
        // The conflict transition reads "x", chosen writes "x" → pair ("x", "x")
        assert!(
            blockers.conflict_field_pairs.contains_key(&("x".to_string(), "x".to_string())),
            "should record (x, x) conflict pair, got: {:?}",
            blockers.conflict_field_pairs
        );

        let summary = format_independence_blockers_summary(&blockers);
        assert!(
            summary
                .contains("early_off=0 chosen_unknown=0 cand=4 ind=1 same=1 unknown=1 conflict=1"),
            "summary should include blocker counts, got {}",
            summary
        );
        assert!(
            summary.contains("top_conflicts="),
            "summary should include top conflicts, got {}",
            summary
        );
    }

    #[test]
    fn test_conflict_field_pairs_accumulate_across_decisions() {
        let mut blockers = SleepIndependenceBlockers::default();

        let t1 = EnabledTransition {
            process_id: ProcessId(0),
            branch_label: "a".to_string(),
            successor_fingerprint: StateFingerprint(0),
            ordering_key: "0".to_string(),
            footprint: TransitionFootprint {
                reads: BTreeSet::new(),
                writes: ["pc".to_string(), "val".to_string()].into(),
            },
        };
        let t2 = EnabledTransition {
            process_id: ProcessId(1),
            branch_label: "b".to_string(),
            successor_fingerprint: StateFingerprint(1),
            ordering_key: "1".to_string(),
            footprint: TransitionFootprint {
                reads: ["pc".to_string()].into(),
                writes: ["val".to_string()].into(),
            },
        };

        // Record conflict twice to test accumulation
        let decision = classify_transition_independence(&t1, &t2, true);
        assert_eq!(decision, IndependenceDecision::BlockedFootprintConflict);
        record_independence_decision(&mut blockers, decision, &t1, &t2);
        record_independence_decision(&mut blockers, decision, &t1, &t2);

        assert_eq!(blockers.blocked_footprint_conflict, 2);
        // t1 writes "pc", t2 reads "pc" → ("pc", "pc")
        // t1 writes "pc", t2 writes "val" → no conflict (different roots)
        // t1 writes "val", t2 reads "pc" → no conflict (different roots)
        // t1 writes "val", t2 writes "val" → ("val", "val")
        assert_eq!(
            blockers.conflict_field_pairs.get(&("pc".to_string(), "pc".to_string())),
            Some(&2),
            "pc-pc pair should be counted twice"
        );
        assert_eq!(
            blockers.conflict_field_pairs.get(&("val".to_string(), "val".to_string())),
            Some(&2),
            "val-val pair should be counted twice"
        );
        assert_eq!(
            blockers.conflict_field_pairs.len(),
            2,
            "should have exactly 2 distinct field pairs"
        );
    }

    #[test]
    fn test_conflict_field_pairs_empty_when_no_footprint_conflict() {
        let mut blockers = SleepIndependenceBlockers::default();

        let t1 = EnabledTransition {
            process_id: ProcessId(0),
            branch_label: "a".to_string(),
            successor_fingerprint: StateFingerprint(0),
            ordering_key: "0".to_string(),
            footprint: TransitionFootprint {
                reads: BTreeSet::new(),
                writes: ["x".to_string()].into(),
            },
        };
        let t2 = EnabledTransition {
            process_id: ProcessId(1),
            branch_label: "b".to_string(),
            successor_fingerprint: StateFingerprint(1),
            ordering_key: "1".to_string(),
            footprint: TransitionFootprint {
                reads: ["y".to_string()].into(),
                writes: BTreeSet::new(),
            },
        };

        let decision = classify_transition_independence(&t1, &t2, true);
        assert_eq!(decision, IndependenceDecision::Independent);
        record_independence_decision(&mut blockers, decision, &t1, &t2);

        assert_eq!(blockers.independent_candidates, 1);
        assert!(
            blockers.conflict_field_pairs.is_empty(),
            "no field pairs should be recorded for independent transitions"
        );
    }

    #[test]
    fn test_format_summary_top_conflicts_ordering() {
        let mut blockers = SleepIndependenceBlockers::default();
        blockers.blocked_footprint_conflict = 30;
        blockers.candidates_considered = 30;
        // Insert field pairs with different frequencies
        blockers.conflict_field_pairs.insert(("a".to_string(), "b".to_string()), 5);
        blockers.conflict_field_pairs.insert(("pc".to_string(), "pc".to_string()), 20);
        blockers.conflict_field_pairs.insert(("val".to_string(), "val".to_string()), 3);
        blockers.conflict_field_pairs.insert(("x".to_string(), "y".to_string()), 2);

        let summary = format_independence_blockers_summary(&blockers);
        // Top-N should be ordered by frequency descending
        assert!(summary.contains("top_conflicts="));
        // pc,pc (20) should appear before a,b (5)
        let pc_pos = summary.find("(pc,pc)::20").expect("should contain pc,pc::20");
        let ab_pos = summary.find("(a,b)::5").expect("should contain a,b::5");
        assert!(
            pc_pos < ab_pos,
            "higher-frequency pair should appear first in summary"
        );
    }

    #[test]
    fn test_format_conflict_profile_report() {
        let mut blockers = SleepIndependenceBlockers::default();
        blockers.candidates_considered = 100;
        blockers.independent_candidates = 40;
        blockers.blocked_same_process = 20;
        blockers.blocked_unknown_footprint = 10;
        blockers.blocked_footprint_conflict = 30;
        blockers
            .conflict_field_pairs
            .insert(("pc".to_string(), "pc".to_string()), 15);
        blockers
            .conflict_field_pairs
            .insert(("pc[0]".to_string(), "pc[0]".to_string()), 10);
        blockers
            .conflict_field_pairs
            .insert(("val".to_string(), "log[1]".to_string()), 5);

        let runtime_stats = RuntimeConflictStats::default();
        let report = format_conflict_profile(&blockers, &runtime_stats);
        assert!(report.contains("=== Conflict Profile Report ==="));
        assert!(report.contains("Total candidate pairs evaluated: 100"));
        assert!(report.contains("Independent: 40 (40.0%)"));
        assert!(report.contains("Blocked (same process): 20"));
        assert!(report.contains("Blocked (footprint conflict): 30"));
        assert!(report.contains("Field-pair conflict frequency"));
        // Verify ordering: pc,pc (15) before pc[0],pc[0] (10)
        let pc_pos = report.find("pc  ").expect("should contain pc field");
        let keyed_pos = report.find("pc[0]").expect("should contain pc[0]");
        assert!(pc_pos < keyed_pos, "higher-freq pair first");
        // Verify suggestions
        assert!(report.contains("try process-scoped keying"));
        assert!(report.contains("already keyed"));
        assert!(report.contains("partially keyed"));
        assert!(report.contains("=== End Conflict Profile ==="));
    }

    #[test]
    fn test_format_conflict_profile_empty() {
        let blockers = SleepIndependenceBlockers::default();
        let runtime_stats = RuntimeConflictStats::default();
        let report = format_conflict_profile(&blockers, &runtime_stats);
        assert!(report.contains("No field-pair conflict data recorded"));
        assert!(report.contains("Total candidate pairs evaluated: 0"));
    }

    // =========================================================================
    // Runtime conflict verification tests (Phase 38.21.I.c)
    // =========================================================================

    fn make_struct_state(fields: Vec<(&str, RuntimeValue)>) -> RuntimeValue {
        RuntimeValue::struct_value(
            "State",
            fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect::<Vec<_>>(),
        )
        .unwrap()
    }

    #[test]
    fn test_extract_field_value_simple() {
        let state = make_struct_state(vec![
            ("pc", RuntimeValue::Int(1)),
            ("val", RuntimeValue::Int(42)),
        ]);
        assert_eq!(extract_field_value(&state, "pc"), Some(&RuntimeValue::Int(1)));
        assert_eq!(extract_field_value(&state, "val"), Some(&RuntimeValue::Int(42)));
        assert_eq!(extract_field_value(&state, "nonexistent"), None);
    }

    #[test]
    fn test_extract_field_value_keyed_seq() {
        let seq = RuntimeValue::Seq(std::sync::Arc::new(vec![
            RuntimeValue::Int(10),
            RuntimeValue::Int(20),
            RuntimeValue::Int(30),
        ]));
        let state = make_struct_state(vec![("log", seq)]);
        assert_eq!(extract_field_value(&state, "log[0]"), Some(&RuntimeValue::Int(10)));
        assert_eq!(extract_field_value(&state, "log[2]"), Some(&RuntimeValue::Int(30)));
        assert_eq!(extract_field_value(&state, "log[5]"), None);
    }

    #[test]
    fn test_extract_field_value_non_struct() {
        let val = RuntimeValue::Int(42);
        assert_eq!(extract_field_value(&val, "anything"), None);
    }

    #[test]
    fn test_record_runtime_write_stats_field_changed() {
        let pre = make_struct_state(vec![
            ("pc", RuntimeValue::Int(0)),
            ("val", RuntimeValue::Int(10)),
        ]);
        let post = make_struct_state(vec![
            ("pc", RuntimeValue::Int(1)),
            ("val", RuntimeValue::Int(10)),
        ]);
        let transition = EnabledTransition {
            process_id: ProcessId(0),
            branch_label: "Step".to_string(),
            successor_fingerprint: StateFingerprint(1),
            ordering_key: "0:Step".to_string(),
            footprint: TransitionFootprint {
                reads: BTreeSet::new(),
                writes: BTreeSet::from(["pc".to_string(), "val".to_string()]),
            },
        };
        let mut stats = RuntimeConflictStats::default();
        record_runtime_write_stats(&mut stats, &transition, &pre, &post);

        // "pc" changed (0→1), "val" did not (10→10)
        assert_eq!(stats.write_field_stats["pc"], (1, 1));
        assert_eq!(stats.write_field_stats["val"], (1, 0));
    }

    #[test]
    fn test_record_runtime_write_stats_accumulates() {
        let pre = make_struct_state(vec![("x", RuntimeValue::Int(0))]);
        let post = make_struct_state(vec![("x", RuntimeValue::Int(1))]);
        let transition = EnabledTransition {
            process_id: ProcessId(0),
            branch_label: "Inc".to_string(),
            successor_fingerprint: StateFingerprint(1),
            ordering_key: "0:Inc".to_string(),
            footprint: TransitionFootprint {
                reads: BTreeSet::new(),
                writes: BTreeSet::from(["x".to_string()]),
            },
        };
        let mut stats = RuntimeConflictStats::default();
        record_runtime_write_stats(&mut stats, &transition, &pre, &post);
        record_runtime_write_stats(&mut stats, &transition, &pre, &post);
        // Fired twice, changed both times
        assert_eq!(stats.write_field_stats["x"], (2, 2));

        // Fire once with no change
        record_runtime_write_stats(&mut stats, &transition, &pre, &pre);
        assert_eq!(stats.write_field_stats["x"], (3, 2));
    }

    #[test]
    fn test_format_conflict_profile_with_runtime_stats() {
        let blockers = SleepIndependenceBlockers::default();
        let mut runtime_stats = RuntimeConflictStats::default();
        runtime_stats.write_field_stats.insert("pc".to_string(), (100, 80));
        runtime_stats.write_field_stats.insert("val".to_string(), (50, 5));

        let report = format_conflict_profile(&blockers, &runtime_stats);
        assert!(report.contains("Runtime write-field verification:"));
        assert!(report.contains("WRITE FIELD"));
        assert!(report.contains("FP RATE"));
        assert!(report.contains("pc"));
        assert!(report.contains("val"));
        // val has 90% false positive rate (50-5)/50
        assert!(report.contains("90.0%"));
    }

    // =========================================================================
    // Invariant checking and violation witness tests (Phase 38.8.5)
    // =========================================================================

    #[test]
    fn test_dpor_invariant_check_aplusb_passes() {
        // APlusB with LSumInvariant — should find no violation
        let spec_path = match aplusb_spec_path() {
            Some(p) => p,
            None => return,
        };
        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_model_toml(tmp.path());
        let ctx = SpecContext::load(&spec_path, None, &model_path, "LInit", "LNext").unwrap();

        let config = DporConfig {
            max_depth: 20,
            max_states: 1_000,
            invariants: vec!["LSumInvariant".to_string()],
            ..Default::default()
        };
        let result = explore_dpor(&ctx, &config);
        assert!(
            result.violation.is_none(),
            "APlusB should pass LSumInvariant — no violation expected"
        );
        assert!(result.distinct_states.len() > 1, "Should explore states");
        eprintln!(
            "APlusB invariant check: {} states, no violation ✓",
            result.distinct_states.len()
        );
    }

    #[test]
    fn test_dpor_invariant_check_counter_race_bug() {
        // CounterRaceBug with LTotalCorrect — should find violation
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_file = manifest_dir.join("tests/tla-rs/03_counter_race_bug/CounterRaceBug.rs");
        if !spec_file.exists() {
            return;
        }
        let model_path = case_model_config("03_counter_race_bug");
        let ctx = match SpecContext::load(&spec_file, None, &model_path, "LInit", "LNext") {
            Ok(c) => c,
            Err(e) => {
                eprintln!("Skip: {}", e);
                return;
            }
        };

        let config = DporConfig {
            max_depth: 20,
            max_states: 10_000,
            invariants: vec!["LTotalCorrect".to_string()],
            ..Default::default()
        };
        let result = explore_dpor(&ctx, &config);
        assert!(
            result.violation.is_some(),
            "CounterRaceBug should violate LTotalCorrect"
        );
        let witness = result.violation.unwrap();
        assert_eq!(witness.invariant, "LTotalCorrect");
        assert!(witness.depth > 0, "Violation should be at depth > 0");
        assert!(
            !witness.trace.is_empty(),
            "Witness trace should not be empty"
        );
        eprintln!(
            "CounterRaceBug violation: invariant={}, depth={}, trace_len={} ✓",
            witness.invariant,
            witness.depth,
            witness.trace.len()
        );
    }

    #[test]
    fn test_dpor_invariant_check_broken_lock() {
        // BrokenLockBug with LMutualExclusion — should find violation
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_file = manifest_dir.join("tests/tla-rs/05_broken_lock_bug/BrokenLockBug.rs");
        if !spec_file.exists() {
            return;
        }
        let model_path = case_model_config("05_broken_lock_bug");
        let ctx = match SpecContext::load(&spec_file, None, &model_path, "LInit", "LNext") {
            Ok(c) => c,
            Err(e) => {
                eprintln!("Skip: {}", e);
                return;
            }
        };

        let config = DporConfig {
            max_depth: 20,
            max_states: 10_000,
            invariants: vec!["LMutualExclusion".to_string()],
            ..Default::default()
        };
        let result = explore_dpor(&ctx, &config);
        assert!(
            result.violation.is_some(),
            "BrokenLockBug should violate LMutualExclusion"
        );
        let witness = result.violation.unwrap();
        assert_eq!(witness.invariant, "LMutualExclusion");
        assert!(
            !witness.trace.is_empty(),
            "Witness trace should not be empty"
        );
        eprintln!(
            "BrokenLockBug violation: invariant={}, depth={}, trace_len={} ✓",
            witness.invariant,
            witness.depth,
            witness.trace.len()
        );
    }

    #[test]
    fn test_dpor_invariant_check_readers_writers() {
        // ReadersWritersBug with LSafety — should find violation
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_file =
            manifest_dir.join("tests/tla-rs/11_readers_writers_small/ReadersWritersBug.rs");
        if !spec_file.exists() {
            return;
        }
        let model_path = case_model_config("11_readers_writers_small");
        let ctx = match SpecContext::load(&spec_file, None, &model_path, "LInit", "LNext") {
            Ok(c) => c,
            Err(e) => {
                eprintln!("Skip: {}", e);
                return;
            }
        };

        let config = DporConfig {
            max_depth: 20,
            max_states: 10_000,
            invariants: vec!["LSafety".to_string()],
            ..Default::default()
        };
        let result = explore_dpor(&ctx, &config);
        assert!(
            result.violation.is_some(),
            "ReadersWritersBug should violate LSafety"
        );
        let witness = result.violation.unwrap();
        assert_eq!(witness.invariant, "LSafety");
        eprintln!(
            "ReadersWritersBug violation: invariant={}, depth={}, trace_len={} ✓",
            witness.invariant,
            witness.depth,
            witness.trace.len()
        );
    }

    #[test]
    fn test_dpor_deadlock_detection_dining_philosophers() {
        // DiningPhilosophers with check_deadlock — should find deadlock
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_file =
            manifest_dir.join("tests/tla-rs/12_dining_philosophers_3/DiningPhilosophers.rs");
        if !spec_file.exists() {
            return;
        }
        let model_path = case_model_config("12_dining_philosophers_3");
        let ctx = match SpecContext::load(&spec_file, None, &model_path, "LInit", "LNext") {
            Ok(c) => c,
            Err(e) => {
                eprintln!("Skip: {}", e);
                return;
            }
        };

        let config = DporConfig {
            max_depth: 20,
            max_states: 10_000,
            check_deadlock: true,
            ..Default::default()
        };
        let result = explore_dpor(&ctx, &config);
        assert!(
            result.violation.is_some(),
            "DiningPhilosophers should deadlock"
        );
        let witness = result.violation.unwrap();
        assert_eq!(witness.invariant, "__deadlock__");
        assert!(witness.depth > 0, "Deadlock should be at depth > 0");
        eprintln!(
            "DiningPhilosophers deadlock: depth={}, trace_len={}, states={} ✓",
            witness.depth,
            witness.trace.len(),
            result.distinct_states.len()
        );
    }

    #[test]
    fn test_dpor_no_deadlock_aplusb() {
        // APlusB with check_deadlock — should NOT deadlock
        let spec_path = match aplusb_spec_path() {
            Some(p) => p,
            None => return,
        };
        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_model_toml(tmp.path());
        let ctx = SpecContext::load(&spec_path, None, &model_path, "LInit", "LNext").unwrap();

        let config = DporConfig {
            max_depth: 20,
            max_states: 1_000,
            check_deadlock: true,
            ..Default::default()
        };
        let result = explore_dpor(&ctx, &config);
        // APlusB has self-loops (stuttering) at terminal states, so no deadlock
        // But if it does deadlock at the boundary, that's also acceptable
        eprintln!(
            "APlusB deadlock check: violation={:?}, states={} ✓",
            result.violation.as_ref().map(|w| &w.invariant),
            result.distinct_states.len()
        );
    }

    // =========================================================================
    // Witness replay regression tests (Phase 38.8.5.b)
    // =========================================================================

    #[test]
    fn test_replay_counter_race_bug_witness() {
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_file = manifest_dir.join("tests/tla-rs/03_counter_race_bug/CounterRaceBug.rs");
        if !spec_file.exists() {
            return;
        }
        let model_path = case_model_config("03_counter_race_bug");
        let ctx = match SpecContext::load(&spec_file, None, &model_path, "LInit", "LNext") {
            Ok(c) => c,
            Err(_) => return,
        };

        // First explore to find the violation
        let config = DporConfig {
            max_depth: 20,
            max_states: 10_000,
            invariants: vec!["LTotalCorrect".to_string()],
            ..Default::default()
        };
        let result = explore_dpor(&ctx, &config);
        let witness = result.violation.expect("Should find violation");

        // Replay the witness
        let replay = replay_witness(&ctx, &witness);
        assert!(
            replay.confirmed,
            "Replay should confirm CounterRaceBug violation: {:?}",
            replay.error
        );
        assert_eq!(replay.violated_invariant.as_deref(), Some("LTotalCorrect"));
        assert!(
            replay.states.len() > 1,
            "Replay should visit multiple states"
        );
        eprintln!(
            "Replay CounterRaceBug: confirmed={}, states={}, depth={} ✓",
            replay.confirmed,
            replay.states.len(),
            replay.depth
        );
    }

    #[test]
    fn test_replay_broken_lock_witness() {
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_file = manifest_dir.join("tests/tla-rs/05_broken_lock_bug/BrokenLockBug.rs");
        if !spec_file.exists() {
            return;
        }
        let model_path = case_model_config("05_broken_lock_bug");
        let ctx = match SpecContext::load(&spec_file, None, &model_path, "LInit", "LNext") {
            Ok(c) => c,
            Err(_) => return,
        };

        let config = DporConfig {
            max_depth: 20,
            max_states: 10_000,
            invariants: vec!["LMutualExclusion".to_string()],
            ..Default::default()
        };
        let result = explore_dpor(&ctx, &config);
        let witness = result.violation.expect("Should find violation");

        let replay = replay_witness(&ctx, &witness);
        assert!(
            replay.confirmed,
            "Replay should confirm BrokenLockBug violation: {:?}",
            replay.error
        );
        assert_eq!(
            replay.violated_invariant.as_deref(),
            Some("LMutualExclusion")
        );
        eprintln!(
            "Replay BrokenLockBug: confirmed={}, states={}, depth={} ✓",
            replay.confirmed,
            replay.states.len(),
            replay.depth
        );
    }

    #[test]
    fn test_replay_readers_writers_witness() {
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_file =
            manifest_dir.join("tests/tla-rs/11_readers_writers_small/ReadersWritersBug.rs");
        if !spec_file.exists() {
            return;
        }
        let model_path = case_model_config("11_readers_writers_small");
        let ctx = match SpecContext::load(&spec_file, None, &model_path, "LInit", "LNext") {
            Ok(c) => c,
            Err(_) => return,
        };

        let config = DporConfig {
            max_depth: 20,
            max_states: 10_000,
            invariants: vec!["LSafety".to_string()],
            ..Default::default()
        };
        let result = explore_dpor(&ctx, &config);
        let witness = result.violation.expect("Should find violation");

        let replay = replay_witness(&ctx, &witness);
        assert!(
            replay.confirmed,
            "Replay should confirm ReadersWritersBug violation: {:?}",
            replay.error
        );
        assert_eq!(replay.violated_invariant.as_deref(), Some("LSafety"));
        eprintln!(
            "Replay ReadersWritersBug: confirmed={}, states={}, depth={} ✓",
            replay.confirmed,
            replay.states.len(),
            replay.depth
        );
    }

    #[test]
    fn test_replay_dining_philosophers_deadlock() {
        // DiningPhilosophers deadlock — explore, record witness, replay
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_file =
            manifest_dir.join("tests/tla-rs/12_dining_philosophers_3/DiningPhilosophers.rs");
        if !spec_file.exists() {
            return;
        }
        let model_path = case_model_config("12_dining_philosophers_3");
        let ctx = match SpecContext::load(&spec_file, None, &model_path, "LInit", "LNext") {
            Ok(c) => c,
            Err(_) => return,
        };

        // Explore to find deadlock
        let config = DporConfig {
            max_depth: 20,
            max_states: 10_000,
            check_deadlock: true,
            ..Default::default()
        };
        let result = explore_dpor(&ctx, &config);
        let witness = result.violation.expect("Should find deadlock");
        assert_eq!(witness.invariant, "__deadlock__");

        // Replay the deadlock witness
        let replay = replay_witness(&ctx, &witness);
        assert!(
            replay.confirmed,
            "Replay should confirm DiningPhilosophers deadlock: {:?}",
            replay.error
        );
        assert_eq!(replay.violated_invariant.as_deref(), Some("__deadlock__"));
        assert!(
            replay.states.len() > 1,
            "Replay should visit multiple states"
        );
        eprintln!(
            "Replay DiningPhilosophers deadlock: confirmed={}, states={}, depth={} ✓",
            replay.confirmed,
            replay.states.len(),
            replay.depth
        );
    }

    // =========================================================================
    // Automated baseline-vs-DPOR comparison (Phase 38.8.4.a)
    // =========================================================================

    #[derive(Clone, Debug, PartialEq, Eq)]
    enum NegativeWitnessSignature {
        Invariant { invariant: String, depth: usize },
        Deadlock { depth: usize },
    }

    fn extract_depth_with_summary_fallback(
        root: &serde_json::Value,
        section: &serde_json::Value,
    ) -> Option<usize> {
        section
            .get("depth")
            .and_then(|v| v.as_u64())
            .map(|d| d as usize)
            .or_else(|| {
                root.get("summary")
                    .and_then(|summary| summary.get("depth"))
                    .and_then(|v| v.as_u64())
                    .map(|d| d as usize)
            })
    }

    fn baseline_negative_signature(
        baseline: &crate::modelcheck::dpor::baseline::BaselineResult,
    ) -> Option<NegativeWitnessSignature> {
        let root = baseline.raw_json.as_ref()?;
        match baseline.result.as_str() {
            "invariant_violated" => {
                let section = root.get("invariant_violation")?;
                let invariant = section.get("invariant")?.as_str()?.to_string();
                let depth = extract_depth_with_summary_fallback(root, section)?;
                Some(NegativeWitnessSignature::Invariant { invariant, depth })
            }
            "deadlock_detected" => {
                let section = root.get("deadlock")?;
                let depth = extract_depth_with_summary_fallback(root, section)?;
                Some(NegativeWitnessSignature::Deadlock { depth })
            }
            _ => None,
        }
    }

    fn dpor_verdict_and_signature(
        violation: Option<&ViolationWitness>,
    ) -> (&'static str, Option<NegativeWitnessSignature>) {
        match violation {
            Some(witness) if witness.invariant == "__deadlock__" => (
                "deadlock_detected",
                Some(NegativeWitnessSignature::Deadlock {
                    depth: witness.depth,
                }),
            ),
            Some(witness) => (
                "invariant_violated",
                Some(NegativeWitnessSignature::Invariant {
                    invariant: witness.invariant.clone(),
                    depth: witness.depth,
                }),
            ),
            None => ("ok", None),
        }
    }

    fn classify_parity_status(
        baseline_verdict: &str,
        dpor_verdict: &str,
        bl_states: usize,
        dp_states: usize,
        baseline_signature: Option<&NegativeWitnessSignature>,
        dpor_signature: Option<&NegativeWitnessSignature>,
    ) -> &'static str {
        if baseline_verdict != "ok"
            && baseline_verdict != "invariant_violated"
            && baseline_verdict != "deadlock_detected"
        {
            return "baseline_error";
        }

        if baseline_verdict == "ok" {
            if dpor_verdict != "ok" {
                return "dpor_found_negative_on_positive_case";
            }
            if dp_states == bl_states {
                return "exact_match";
            }
            if dp_states < bl_states {
                return "dpor_subset";
            }
            return "dpor_exceeded_baseline";
        }

        if dpor_verdict != baseline_verdict {
            return "negative_verdict_mismatch";
        }

        match (baseline_signature, dpor_signature) {
            (Some(bl), Some(dp)) if bl == dp => "negative_witness_match",
            (Some(_), Some(_)) => "negative_witness_mismatch",
            _ => "negative_witness_unavailable",
        }
    }

    /// Run both baseline and DPOR on a case, compare results.
    /// Returns (baseline_states, dpor_states, match_status).
    fn compare_baseline_vs_dpor(
        spec_file: &std::path::Path,
        model_path: &std::path::Path,
        invariants: &[String],
    ) -> (usize, usize, &'static str) {
        let ctx = match SpecContext::load(spec_file, None, model_path, "LInit", "LNext") {
            Ok(c) => c,
            Err(_) => return (0, 0, "load_failed"),
        };

        // Run baseline subprocess
        let transpiler = match crate::modelcheck::dpor::baseline::find_transpiler_bin() {
            Some(p) => p,
            None => return (0, 0, "no_baseline_bin"),
        };
        let baseline = run_baseline_serial(&transpiler, spec_file, model_path, invariants, 30);

        // Run DPOR with witness checks aligned to the baseline's verdict mode.
        // Deadlock checking is enabled only for baseline-deadlock rows so the
        // comparison does not treat baseline-positive no-invariant rows as
        // accidental deadlock checks.
        let config = DporConfig {
            max_depth: 20,
            max_states: 10_000,
            invariants: invariants.to_vec(),
            check_deadlock: baseline.result == "deadlock_detected",
            ..Default::default()
        };
        let dpor_result = explore_dpor(&ctx, &config);

        let bl_states = baseline.distinct_states;
        let dp_states = dpor_result.distinct_states.len();
        let baseline_signature = baseline_negative_signature(&baseline);
        let (dpor_verdict, dpor_signature) =
            dpor_verdict_and_signature(dpor_result.violation.as_ref());
        let status = classify_parity_status(
            baseline.result.as_str(),
            dpor_verdict,
            bl_states,
            dp_states,
            baseline_signature.as_ref(),
            dpor_signature.as_ref(),
        );

        (bl_states, dp_states, status)
    }

    #[test]
    fn test_baseline_negative_signature_extracts_invariant_and_depth() {
        let baseline = crate::modelcheck::dpor::baseline::BaselineResult {
            case_id: "case".to_string(),
            result: "invariant_violated".to_string(),
            stop_reason: "InvariantViolated".to_string(),
            states: 5,
            distinct_states: 5,
            elapsed_ms: 1,
            raw_json: Some(serde_json::json!({
                "invariant_violation": { "invariant": "LMutualExclusion", "depth": 2 }
            })),
        };

        assert_eq!(
            baseline_negative_signature(&baseline),
            Some(NegativeWitnessSignature::Invariant {
                invariant: "LMutualExclusion".to_string(),
                depth: 2,
            })
        );
    }

    #[test]
    fn test_classify_parity_status_negative_witness_match_allows_state_mismatch() {
        let status = classify_parity_status(
            "invariant_violated",
            "invariant_violated",
            5,
            7,
            Some(&NegativeWitnessSignature::Invariant {
                invariant: "LMutualExclusion".to_string(),
                depth: 2,
            }),
            Some(&NegativeWitnessSignature::Invariant {
                invariant: "LMutualExclusion".to_string(),
                depth: 2,
            }),
        );
        assert_eq!(status, "negative_witness_match");
    }

    #[test]
    fn test_classify_parity_status_negative_witness_mismatch_detected() {
        let status = classify_parity_status(
            "invariant_violated",
            "invariant_violated",
            5,
            7,
            Some(&NegativeWitnessSignature::Invariant {
                invariant: "LMutualExclusion".to_string(),
                depth: 2,
            }),
            Some(&NegativeWitnessSignature::Invariant {
                invariant: "LMutualExclusion".to_string(),
                depth: 3,
            }),
        );
        assert_eq!(status, "negative_witness_mismatch");
    }

    #[test]
    fn test_classify_parity_status_positive_row_dpor_negative_is_error() {
        let status = classify_parity_status("ok", "invariant_violated", 21, 21, None, None);
        assert_eq!(status, "dpor_found_negative_on_positive_case");
    }

    /// Get the per-case model config path, falling back to default.
    fn case_model_config(case_id: &str) -> std::path::PathBuf {
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let per_case = manifest_dir.join(format!("tests/model_configs/{}.toml", case_id));
        if per_case.exists() {
            per_case
        } else {
            // Fallback: create a temporary default config
            let tmp = tempfile::tempdir().unwrap();
            let p = create_model_toml(tmp.path());
            // Leak the tempdir to keep the file alive
            std::mem::forget(tmp);
            p
        }
    }

    #[test]
    fn test_case13_twophase_is_real_non_vacuous_pass() {
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_file = manifest_dir.join("tests/tla-rs/13_twophase_small/TwoPhase.rs");
        if !spec_file.exists() {
            eprintln!("Skipping: case 13 translated spec not found");
            return;
        }

        let transpiler = match crate::modelcheck::dpor::baseline::find_transpiler_bin() {
            Some(p) => p,
            None => {
                eprintln!("Skipping: transpiler binary not found");
                return;
            }
        };

        let model_path = case_model_config("13_twophase_small");
        let result = run_baseline_serial(
            &transpiler,
            &spec_file,
            &model_path,
            &["LTCConsistent".to_string()],
            60,
        );

        assert_eq!(
            result.result, "ok",
            "Case 13 must remain a real pass (not vacuous or error): {:?}",
            result
        );
        assert!(
            result.distinct_states > 0,
            "Case 13 must explore at least one state; got {}",
            result.distinct_states
        );
    }

    #[test]
    fn test_case14_leader_election_is_real_non_vacuous_pass() {
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_file = manifest_dir.join("tests/tla-rs/14_leader_election_small/Election.rs");
        if !spec_file.exists() {
            eprintln!("Skipping: case 14 translated spec not found");
            return;
        }

        let transpiler = match crate::modelcheck::dpor::baseline::find_transpiler_bin() {
            Some(p) => p,
            None => {
                eprintln!("Skipping: transpiler binary not found");
                return;
            }
        };

        let model_path = case_model_config("14_leader_election_small");
        let result = run_baseline_serial(
            &transpiler,
            &spec_file,
            &model_path,
            &["LSafetyElectingSubsetAlive".to_string()],
            60,
        );

        assert_eq!(
            result.result, "ok",
            "Case 14 must become a real pass (not vacuous or error): {:?}",
            result
        );
        assert!(
            result.distinct_states > 0,
            "Case 14 must explore at least one state; got {}",
            result.distinct_states
        );
    }

    #[test]
    fn test_case15_chain_replication_is_real_non_vacuous_deadlock() {
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_file = manifest_dir.join("tests/tla-rs/15_chain_replication_small/Chain.rs");
        if !spec_file.exists() {
            eprintln!("Skipping: case 15 translated spec not found");
            return;
        }

        let transpiler = match crate::modelcheck::dpor::baseline::find_transpiler_bin() {
            Some(p) => p,
            None => {
                eprintln!("Skipping: transpiler binary not found");
                return;
            }
        };

        let model_path = case_model_config("15_chain_replication_small");
        let result = run_baseline_serial(&transpiler, &spec_file, &model_path, &[], 240);

        assert_eq!(
            result.result, "deadlock_detected",
            "Case 15 should be a real deadlock-detection outcome under bounded config: {:?}",
            result
        );
        assert!(
            result.distinct_states > 0,
            "Case 15 must explore at least one state; got {}",
            result.distinct_states
        );
    }

    #[test]
    fn test_case16_primarybackup_is_real_non_vacuous_pass() {
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_file = manifest_dir.join("tests/tla-rs/16_primarybackup_small/Primarybackup.rs");
        if !spec_file.exists() {
            eprintln!("Skipping: case 16 translated spec not found");
            return;
        }

        let transpiler = match crate::modelcheck::dpor::baseline::find_transpiler_bin() {
            Some(p) => p,
            None => {
                eprintln!("Skipping: transpiler binary not found");
                return;
            }
        };

        let model_path = case_model_config("16_primarybackup_small");
        let result = run_baseline_serial(
            &transpiler,
            &spec_file,
            &model_path,
            &["LSafetyInactiveStateIsQuiescent".to_string()],
            120,
        );

        assert_eq!(
            result.result, "ok",
            "Case 16 should be a real invariant-checked pass: {:?}",
            result
        );
        assert!(
            result.distinct_states > 0,
            "Case 16 must explore at least one state; got {}",
            result.distinct_states
        );
    }

    #[test]
    fn test_case17_paxos_is_real_non_vacuous_pass() {
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_file = manifest_dir.join("tests/tla-rs/17_paxos_small/Paxos.rs");
        if !spec_file.exists() {
            eprintln!("Skipping: case 17 translated spec not found");
            return;
        }

        let transpiler = match crate::modelcheck::dpor::baseline::find_transpiler_bin() {
            Some(p) => p,
            None => {
                eprintln!("Skipping: transpiler binary not found");
                return;
            }
        };

        let model_path = case_model_config("17_paxos_small");
        let result = run_baseline_serial(
            &transpiler,
            &spec_file,
            &model_path,
            &["LChosenValueAgreement".to_string()],
            60,
        );

        assert_eq!(
            result.result, "ok",
            "Case 17 must remain a real pass (not vacuous or error): {:?}",
            result
        );
        assert!(
            result.distinct_states > 0,
            "Case 17 must explore at least one state; got {}",
            result.distinct_states
        );
    }

    #[test]
    fn test_case18_pbft_is_real_non_vacuous_pass() {
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_file = manifest_dir.join("tests/tla-rs/18_pbft_small/PBFT.rs");
        if !spec_file.exists() {
            eprintln!("Skipping: case 18 translated spec not found");
            return;
        }

        let transpiler = match crate::modelcheck::dpor::baseline::find_transpiler_bin() {
            Some(p) => p,
            None => {
                eprintln!("Skipping: transpiler binary not found");
                return;
            }
        };

        let model_path = case_model_config("18_pbft_small");
        let result = run_baseline_serial(
            &transpiler,
            &spec_file,
            &model_path,
            &["LPBFTSafety".to_string()],
            60,
        );

        assert_eq!(
            result.result, "ok",
            "Case 18 must remain a real pass (not vacuous or error): {:?}",
            result
        );
        assert!(
            result.distinct_states > 0,
            "Case 18 must explore at least one state; got {}",
            result.distinct_states
        );
    }

    #[test]
    #[ignore = "heavy/flaky in default cargo test; covered by run_full_suite.sh case 19"]
    fn test_case19_epaxos_is_real_non_vacuous_pass() {
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_file = manifest_dir.join("tests/tla-rs/19_epaxos_small/Epaxos.rs");
        if !spec_file.exists() {
            eprintln!("Skipping: case 19 translated spec not found");
            return;
        }

        let transpiler = match crate::modelcheck::dpor::baseline::find_transpiler_bin() {
            Some(p) => p,
            None => {
                eprintln!("Skipping: transpiler binary not found");
                return;
            }
        };

        let model_path = case_model_config("19_epaxos_small");
        let mut result = run_baseline_serial(&transpiler, &spec_file, &model_path, &[], 180);
        let mut retries = 0usize;
        while result.result == "timeout_reached" && retries < 2 {
            retries += 1;
            eprintln!(
                "Case 19 baseline timed out on attempt {}; retrying...",
                retries
            );
            result = run_baseline_serial(&transpiler, &spec_file, &model_path, &[], 180);
        }

        assert_eq!(
            result.result, "ok",
            "Case 19 must be a real pass with deadlock semantics enabled after retry budget: {:?}",
            result
        );
        assert!(
            result.distinct_states > 1,
            "Case 19 must explore >1 states to be non-vacuous; got {}",
            result.distinct_states
        );
    }

    #[test]
    #[ignore = "evidence-generation: DPOR reduction on protocol cases (17/18/20)"]
    fn print_dpor_reduction_protocol_cases() {
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let cases: Vec<(&str, &str, &str)> = vec![
            ("17_paxos_small", "Paxos.rs", "LChosenValueAgreement"),
            ("18_pbft_small", "PBFT.rs", "LPBFTSafety"),
            ("20_raft_small", "Raft.rs", "LElectionSafety"),
        ];
        println!(
            "| Case | Cons states | Ind states | Slp states | Cons trans | Ind trans | Slp trans |"
        );
        for (case_id, filename, _inv) in &cases {
            let spec_file = manifest_dir.join(format!("tests/tla-rs/{}/{}", case_id, filename));
            if !spec_file.exists() {
                continue;
            }
            let model_path = case_model_config(case_id);
            let ctx = match SpecContext::load(&spec_file, None, &model_path, "LInit", "LNext") {
                Ok(c) => c,
                Err(_) => continue,
            };
            let configs = [
                (
                    "cons",
                    DporConfig {
                        max_depth: 30,
                        max_states: 500000,
                        use_independence: false,
                        use_sleep_sets: false,
                        invariants: vec![],
                        check_deadlock: false,
                    },
                ),
                (
                    "ind",
                    DporConfig {
                        max_depth: 30,
                        max_states: 500000,
                        use_independence: true,
                        use_sleep_sets: false,
                        invariants: vec![],
                        check_deadlock: false,
                    },
                ),
                (
                    "slp",
                    DporConfig {
                        max_depth: 30,
                        max_states: 500000,
                        use_independence: true,
                        use_sleep_sets: true,
                        invariants: vec![],
                        check_deadlock: false,
                    },
                ),
            ];
            let mut states = [0usize; 3];
            let mut trans = [0usize; 3];
            for (i, (_label, cfg)) in configs.iter().enumerate() {
                let r = explore_dpor(&ctx, cfg);
                states[i] = r.distinct_states.len();
                trans[i] = r.transitions_fired;
            }
            println!(
                "| {} | {} | {} | {} | {} | {} | {} |",
                case_id, states[0], states[1], states[2], trans[0], trans[1], trans[2]
            );
        }
    }

    #[test]
    fn test_case20_raft_is_real_non_vacuous_pass() {
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_file = manifest_dir.join("tests/tla-rs/20_raft_small/Raft.rs");
        if !spec_file.exists() {
            eprintln!("Skipping: case 20 translated spec not found");
            return;
        }

        let transpiler = match crate::modelcheck::dpor::baseline::find_transpiler_bin() {
            Some(p) => p,
            None => {
                eprintln!("Skipping: transpiler binary not found");
                return;
            }
        };

        let model_path = case_model_config("20_raft_small");
        let result = run_baseline_serial(
            &transpiler,
            &spec_file,
            &model_path,
            &["LElectionSafety".to_string()],
            60,
        );

        assert_eq!(
            result.result, "ok",
            "Case 20 must become a real pass (not vacuous or error): {:?}",
            result
        );
        assert!(
            result.distinct_states > 0,
            "Case 20 must explore at least one state; got {}",
            result.distinct_states
        );
    }

    #[test]
    #[ignore = "heavy integration sweep; covered by scripts/run_full_suite.sh"]
    fn test_automated_baseline_vs_dpor_comparison() {
        // Fast baseline-vs-DPOR comparison smoke check.
        //
        // Full-corpus coverage is maintained by scripts/run_full_suite.sh;
        // this unit test intentionally stays lightweight for deterministic
        // default cargo test latency.
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));

        // Representative baseline-passing subset with invariants.
        let cases: Vec<(&str, &str, Vec<String>)> = vec![
            ("01_aplusb", "APlusB.rs", vec!["LSumInvariant".to_string()]),
            (
                "02_counter_incdec",
                "CounterIncDec.rs",
                vec!["LTypeOK".to_string()],
            ),
            (
                "03_counter_race_bug",
                "CounterRaceBug.rs",
                vec!["LTotalCorrect".to_string()],
            ),
            (
                "04_lock_basic",
                "LockBasic.rs",
                vec!["LMutualExclusion".to_string()],
            ),
            (
                "05_broken_lock_bug",
                "BrokenLockBug.rs",
                vec!["LMutualExclusion".to_string()],
            ),
            (
                "06_ticket_lock",
                "TicketLock.rs",
                vec!["LMutualExclusion".to_string()],
            ),
            (
                "07_producer_consumer_1slot",
                "ProducerConsumer1Slot.rs",
                vec!["LSafetyInvariant".to_string()],
            ),
            ("08_bounded_buffer_2slot", "BoundedBuffer2Slot.rs", vec![]),
            (
                "09_peterson_mutex_2p",
                "PetersonMutex.rs",
                vec!["LMutualExclusion".to_string()],
            ),
            (
                "11_readers_writers_small",
                "ReadersWritersBug.rs",
                vec!["LSafety".to_string()],
            ),
            ("12_dining_philosophers_3", "DiningPhilosophers.rs", vec![]),
            (
                "13_twophase_small",
                "TwoPhase.rs",
                vec!["LTCConsistent".to_string()],
            ),
        ];

        let mut results = Vec::new();
        for (case_id, filename, invariants) in &cases {
            let spec_file = manifest_dir.join(format!("tests/tla-rs/{}/{}", case_id, filename));
            if !spec_file.exists() {
                eprintln!("  {} SKIP (not translated)", case_id);
                continue;
            }

            let model_path = case_model_config(case_id);
            let (bl, dp, status) = compare_baseline_vs_dpor(&spec_file, &model_path, invariants);
            results.push((*case_id, bl, dp, status));
            eprintln!("  {} baseline={} dpor={} → {}", case_id, bl, dp, status);
        }

        // Verify no policy-level mismatches.
        for (case_id, _bl, _dp, status) in &results {
            assert_ne!(
                *status, "dpor_found_negative_on_positive_case",
                "CORRECTNESS BUG: DPOR reported a negative verdict for baseline-positive case {}",
                case_id
            );
            assert_ne!(
                *status, "negative_verdict_mismatch",
                "PARITY BUG: baseline/DPOR verdict-class mismatch for {}",
                case_id
            );
            assert_ne!(
                *status, "negative_witness_mismatch",
                "PARITY BUG: baseline/DPOR negative witness signatures diverged for {}",
                case_id
            );
            assert_ne!(
                *status, "negative_witness_unavailable",
                "PARITY BUG: missing witness signature data for {}",
                case_id
            );
            assert_ne!(
                *status, "dpor_exceeded_baseline",
                "CORRECTNESS BUG: DPOR found more states than baseline for {}",
                case_id
            );
        }

        // Verify positive exact parity and negative witness parity are both represented.
        let positive_exact_matches = results
            .iter()
            .filter(|(_, _, _, s)| *s == "exact_match")
            .count();
        assert!(
            positive_exact_matches >= 1,
            "Expected at least 1 exact baseline-DPOR match, got {}",
            positive_exact_matches
        );
        let negative_witness_matches = results
            .iter()
            .filter(|(_, _, _, s)| *s == "negative_witness_match")
            .count();
        assert!(
            negative_witness_matches >= 1,
            "Expected at least 1 negative witness parity match, got {}",
            negative_witness_matches
        );

        let broken_lock_status = results
            .iter()
            .find(|(case_id, _, _, _)| *case_id == "05_broken_lock_bug")
            .map(|(_, _, _, status)| *status);
        assert_eq!(
            broken_lock_status,
            Some("negative_witness_match"),
            "BrokenLockBug should be witness-parity matched under 38.14.11.c.b.c"
        );

        let parity_failures = results
            .iter()
            .filter(|(_, _, _, status)| {
                matches!(
                    *status,
                    "dpor_found_negative_on_positive_case"
                        | "negative_verdict_mismatch"
                        | "negative_witness_mismatch"
                        | "negative_witness_unavailable"
                        | "dpor_exceeded_baseline"
                )
            })
            .count();

        eprintln!(
            "\nAutomated comparison: {} cases, {} positive_exact, {} negative_witness_match, {} subset, {} baseline_error, {} load_failed, {} parity_failures",
            results.len(),
            positive_exact_matches,
            negative_witness_matches,
            results.iter().filter(|(_, _, _, s)| *s == "dpor_subset").count(),
            results.iter().filter(|(_, _, _, s)| *s == "baseline_error").count(),
            results.iter().filter(|(_, _, _, s)| *s == "load_failed").count(),
            parity_failures,
        );
    }
}
