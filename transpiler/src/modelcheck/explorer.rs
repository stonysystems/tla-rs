use crate::error::{TranspileError, TranspileResult};
use crate::modelcheck::config::{SearchLimits, StateDedupMode};
use crate::modelcheck::value::RuntimeValue;
use std::collections::{BTreeSet, VecDeque};
use std::hash::{Hash, Hasher};

/// Traversal strategy for state-space exploration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SearchMode {
    /// Breadth-first search.
    #[default]
    Bfs,
    /// Depth-first search.
    Dfs,
}

/// Limits used while exploring the state space.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExplorationLimits {
    pub max_depth: usize,
    pub max_states: usize,
}

impl From<&SearchLimits> for ExplorationLimits {
    fn from(value: &SearchLimits) -> Self {
        Self {
            max_depth: value.max_depth,
            max_states: value.max_states,
        }
    }
}

/// One visited state and its search depth.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExploredState {
    pub state: RuntimeValue,
    pub depth: usize,
}

/// Why the exploration loop terminated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExplorationStopReason {
    /// Frontier exhausted naturally under the configured bounds.
    FrontierExhausted,
    /// State bound reached before the frontier is fully explored.
    MaxStatesReached,
    /// A user-selected invariant evaluated to false on a reached state.
    InvariantViolated,
    /// Deadlock detected: a reached state (below depth bound) has no successors.
    DeadlockDetected,
}

/// Invariant failure metadata captured at exploration stop.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InvariantViolation {
    pub invariant: String,
    pub state: RuntimeValue,
    pub depth: usize,
}

/// Deadlock metadata captured at exploration stop.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeadlockDetection {
    pub state: RuntimeValue,
    pub depth: usize,
}

/// One state-change summary entry for a transition in a counterexample trace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StateDiffSummary {
    pub path: String,
    pub before: String,
    pub after: String,
}

/// One action-labeled transition in a counterexample trace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CounterexampleStep {
    pub action_branch: String,
    pub state: RuntimeValue,
    pub diffs: Vec<StateDiffSummary>,
}

/// Counterexample trace from one initial state to a failing state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CounterexampleTrace {
    pub initial_state: RuntimeValue,
    pub steps: Vec<CounterexampleStep>,
}

/// Successor annotated with action branch metadata for trace emission.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TracedSuccessor {
    pub action_branch: String,
    pub state: RuntimeValue,
}

/// Summary statistics collected while exploring the state space.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct ExplorationStats {
    /// Number of unique initial states seeded into the frontier.
    pub initial_states: usize,
    /// Number of states popped/explored from the frontier.
    pub explored_states: usize,
    /// Number of unique states ever recorded in the visited set.
    pub visited_states: usize,
    /// Maximum number of states present in the frontier at any point.
    pub max_frontier_size: usize,
    /// Frontier size at the moment exploration stopped.
    pub frontier_size_at_stop: usize,
    /// Number of successor candidates returned by `successor_fn`.
    pub successors_considered: usize,
    /// Number of unique successors enqueued into the frontier.
    pub successors_enqueued: usize,
    /// Number of successor candidates dropped due to deduplication.
    pub duplicate_successors: usize,
    /// Number of distinct states merged due to hash-compaction key collisions.
    ///
    /// Non-zero only when `state_dedup = "hash_compaction64"`.
    pub hash_compaction_collisions: usize,
    /// Number of distinct raw states merged by symmetry normalization.
    ///
    /// Non-zero only when symmetry fields are configured.
    pub symmetry_collapses: usize,
}

/// Result of running a bounded BFS/DFS exploration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExplorationResult {
    pub explored: Vec<ExploredState>,
    pub stop_reason: ExplorationStopReason,
    pub stats: ExplorationStats,
    pub invariant_violation: Option<InvariantViolation>,
    pub deadlock: Option<DeadlockDetection>,
    pub counterexample: Option<CounterexampleTrace>,
}

#[derive(Debug, Clone)]
struct FrontierItem {
    key: String,
    state: RuntimeValue,
    depth: usize,
}

#[derive(Debug, Clone)]
struct TraceParent {
    parent_key: String,
    action_branch: String,
}

/// Explore the state space with either BFS or DFS.
///
/// - `initial_states` are deduplicated by canonical key in input order.
/// - `successor_fn` must return concrete successor states in deterministic order.
/// - Deduplication is global: a state is visited at most once.
pub fn explore_state_space<F>(
    initial_states: &[RuntimeValue],
    mode: SearchMode,
    limits: ExplorationLimits,
    successor_fn: F,
) -> TranspileResult<ExplorationResult>
where
    F: FnMut(&RuntimeValue) -> TranspileResult<Vec<RuntimeValue>>,
{
    explore_state_space_internal(
        initial_states,
        mode,
        limits,
        successor_fn,
        |_, _| Ok(None),
        false,
    )
}

/// Explore the state space while checking user-selected invariants on every reached state.
///
/// The invariant checker is invoked once per state popped from the frontier. Returning
/// `Some(invariant_name)` stops exploration immediately with `InvariantViolated`.
pub fn explore_state_space_with_invariants<F, I>(
    initial_states: &[RuntimeValue],
    mode: SearchMode,
    limits: ExplorationLimits,
    successor_fn: F,
    invariant_checker: I,
) -> TranspileResult<ExplorationResult>
where
    F: FnMut(&RuntimeValue) -> TranspileResult<Vec<RuntimeValue>>,
    I: FnMut(&RuntimeValue, usize) -> TranspileResult<Option<String>>,
{
    explore_state_space_internal(
        initial_states,
        mode,
        limits,
        successor_fn,
        invariant_checker,
        false,
    )
}

/// Explore the state space while checking invariants and deadlocks.
///
/// When `check_deadlock` is true, exploration stops on the first reached state
/// (below `max_depth`) whose successor set is empty.
pub fn explore_state_space_with_checks<F, I>(
    initial_states: &[RuntimeValue],
    mode: SearchMode,
    limits: ExplorationLimits,
    check_deadlock: bool,
    successor_fn: F,
    invariant_checker: I,
) -> TranspileResult<ExplorationResult>
where
    F: FnMut(&RuntimeValue) -> TranspileResult<Vec<RuntimeValue>>,
    I: FnMut(&RuntimeValue, usize) -> TranspileResult<Option<String>>,
{
    explore_state_space_internal(
        initial_states,
        mode,
        limits,
        successor_fn,
        invariant_checker,
        check_deadlock,
    )
}

/// Explore the state space while emitting counterexample traces with action branches
/// and per-transition state-diff summaries.
///
/// On invariant violation or deadlock, `ExplorationResult.counterexample` contains
/// a trace from the chosen initial state to the failing state.
pub fn explore_state_space_with_traces<F, I>(
    initial_states: &[RuntimeValue],
    mode: SearchMode,
    limits: ExplorationLimits,
    check_deadlock: bool,
    successor_fn: F,
    invariant_checker: I,
) -> TranspileResult<ExplorationResult>
where
    F: FnMut(&RuntimeValue) -> TranspileResult<Vec<TracedSuccessor>>,
    I: FnMut(&RuntimeValue, usize) -> TranspileResult<Option<String>>,
{
    explore_state_space_with_traces_and_dedup(
        initial_states,
        mode,
        limits,
        StateDedupMode::Canonical,
        &[],
        check_deadlock,
        successor_fn,
        invariant_checker,
    )
}

/// Same as `explore_state_space_with_traces`, but with explicit state-dedup mode.
pub fn explore_state_space_with_traces_and_dedup<F, I>(
    initial_states: &[RuntimeValue],
    mode: SearchMode,
    limits: ExplorationLimits,
    state_dedup: StateDedupMode,
    symmetry_fields: &[String],
    check_deadlock: bool,
    mut successor_fn: F,
    mut invariant_checker: I,
) -> TranspileResult<ExplorationResult>
where
    F: FnMut(&RuntimeValue) -> TranspileResult<Vec<TracedSuccessor>>,
    I: FnMut(&RuntimeValue, usize) -> TranspileResult<Option<String>>,
{
    validate_limits(limits)?;

    let symmetry_field_set: BTreeSet<&str> = symmetry_fields.iter().map(String::as_str).collect();
    let mut visited = BTreeSet::new();
    let mut hash_representatives = std::collections::BTreeMap::<String, String>::new();
    let mut symmetry_representatives =
        std::collections::BTreeMap::<String, BTreeSet<String>>::new();
    let mut frontier = VecDeque::new();
    let mut states_by_key = std::collections::BTreeMap::new();
    let mut stats = ExplorationStats::default();
    for state in initial_states {
        let dedup_canonical = canonical_dedup_key(state, &symmetry_field_set);
        if !symmetry_field_set.is_empty()
            && record_symmetry_collapse(
                &mut symmetry_representatives,
                &dedup_canonical,
                &state.canonical_key(),
            )
        {
            stats.symmetry_collapses += 1;
        }
        let key = dedup_key_from_canonical(&dedup_canonical, state_dedup);
        if visited.insert(key.clone()) {
            if matches!(state_dedup, StateDedupMode::HashCompaction64) {
                hash_representatives.insert(key.clone(), dedup_canonical);
            }
            states_by_key.insert(key.clone(), state.clone());
            frontier.push_back(FrontierItem {
                key,
                state: state.clone(),
                depth: 0,
            });
        }
    }

    stats.initial_states = frontier.len();
    stats.max_frontier_size = frontier.len();
    let mut explored = Vec::new();
    let mut parents = std::collections::BTreeMap::<String, TraceParent>::new();
    while let Some(item) = pop_frontier(&mut frontier, mode) {
        explored.push(ExploredState {
            state: item.state.clone(),
            depth: item.depth,
        });

        if let Some(invariant_name) = invariant_checker(&item.state, item.depth)? {
            let counterexample = build_counterexample_trace(&item.key, &states_by_key, &parents);
            return Ok(finalize_result(
                explored,
                ExplorationStopReason::InvariantViolated,
                visited.len(),
                frontier.len(),
                stats,
                Some(InvariantViolation {
                    invariant: invariant_name,
                    state: item.state.clone(),
                    depth: item.depth,
                }),
                None,
                counterexample,
            ));
        }

        if item.depth >= limits.max_depth {
            continue;
        }

        let successors = successor_fn(&item.state)?;
        if check_deadlock && successors.is_empty() {
            let counterexample = build_counterexample_trace(&item.key, &states_by_key, &parents);
            return Ok(finalize_result(
                explored,
                ExplorationStopReason::DeadlockDetected,
                visited.len(),
                frontier.len(),
                stats,
                None,
                Some(DeadlockDetection {
                    state: item.state.clone(),
                    depth: item.depth,
                }),
                counterexample,
            ));
        }

        let mut to_enqueue = Vec::new();
        for successor in successors {
            stats.successors_considered += 1;
            if visited.len() >= limits.max_states {
                return Ok(finalize_result(
                    explored,
                    ExplorationStopReason::MaxStatesReached,
                    visited.len(),
                    frontier.len(),
                    stats,
                    None,
                    None,
                    None,
                ));
            }

            let dedup_canonical = canonical_dedup_key(&successor.state, &symmetry_field_set);
            if !symmetry_field_set.is_empty()
                && record_symmetry_collapse(
                    &mut symmetry_representatives,
                    &dedup_canonical,
                    &successor.state.canonical_key(),
                )
            {
                stats.symmetry_collapses += 1;
            }
            let key = dedup_key_from_canonical(&dedup_canonical, state_dedup);
            if visited.insert(key.clone()) {
                if matches!(state_dedup, StateDedupMode::HashCompaction64) {
                    hash_representatives.insert(key.clone(), dedup_canonical);
                }
                states_by_key.insert(key.clone(), successor.state.clone());
                parents.insert(
                    key.clone(),
                    TraceParent {
                        parent_key: item.key.clone(),
                        action_branch: successor.action_branch,
                    },
                );
                to_enqueue.push(FrontierItem {
                    key,
                    state: successor.state,
                    depth: item.depth + 1,
                });
                stats.successors_enqueued += 1;
            } else {
                if is_hash_collision(&hash_representatives, &key, &dedup_canonical) {
                    stats.hash_compaction_collisions += 1;
                }
                stats.duplicate_successors += 1;
            }
        }
        push_successors(&mut frontier, mode, to_enqueue);
        stats.max_frontier_size = stats.max_frontier_size.max(frontier.len());
    }

    Ok(finalize_result(
        explored,
        ExplorationStopReason::FrontierExhausted,
        visited.len(),
        frontier.len(),
        stats,
        None,
        None,
        None,
    ))
}

fn explore_state_space_internal<F, I>(
    initial_states: &[RuntimeValue],
    mode: SearchMode,
    limits: ExplorationLimits,
    mut successor_fn: F,
    mut invariant_checker: I,
    check_deadlock: bool,
) -> TranspileResult<ExplorationResult>
where
    F: FnMut(&RuntimeValue) -> TranspileResult<Vec<RuntimeValue>>,
    I: FnMut(&RuntimeValue, usize) -> TranspileResult<Option<String>>,
{
    validate_limits(limits)?;

    let mut visited = BTreeSet::new();
    let mut frontier = VecDeque::new();
    for state in initial_states {
        let key = state.canonical_key();
        if visited.insert(key.clone()) {
            frontier.push_back(FrontierItem {
                key,
                state: state.clone(),
                depth: 0,
            });
        }
    }

    let mut stats = ExplorationStats {
        initial_states: frontier.len(),
        max_frontier_size: frontier.len(),
        ..ExplorationStats::default()
    };
    let mut explored = Vec::new();
    while let Some(item) = pop_frontier(&mut frontier, mode) {
        explored.push(ExploredState {
            state: item.state.clone(),
            depth: item.depth,
        });

        if let Some(invariant_name) = invariant_checker(&item.state, item.depth)? {
            return Ok(finalize_result(
                explored,
                ExplorationStopReason::InvariantViolated,
                visited.len(),
                frontier.len(),
                stats,
                Some(InvariantViolation {
                    invariant: invariant_name,
                    state: item.state.clone(),
                    depth: item.depth,
                }),
                None,
                None,
            ));
        }

        if item.depth >= limits.max_depth {
            continue;
        }

        let successors = successor_fn(&item.state)?;
        if check_deadlock && successors.is_empty() {
            return Ok(finalize_result(
                explored,
                ExplorationStopReason::DeadlockDetected,
                visited.len(),
                frontier.len(),
                stats,
                None,
                Some(DeadlockDetection {
                    state: item.state.clone(),
                    depth: item.depth,
                }),
                None,
            ));
        }
        let mut to_enqueue = Vec::new();
        for successor in successors {
            stats.successors_considered += 1;
            if visited.len() >= limits.max_states {
                return Ok(finalize_result(
                    explored,
                    ExplorationStopReason::MaxStatesReached,
                    visited.len(),
                    frontier.len(),
                    stats,
                    None,
                    None,
                    None,
                ));
            }

            let key = successor.canonical_key();
            if visited.insert(key.clone()) {
                to_enqueue.push(FrontierItem {
                    key,
                    state: successor,
                    depth: item.depth + 1,
                });
                stats.successors_enqueued += 1;
            } else {
                stats.duplicate_successors += 1;
            }
        }
        push_successors(&mut frontier, mode, to_enqueue);
        stats.max_frontier_size = stats.max_frontier_size.max(frontier.len());
    }

    Ok(finalize_result(
        explored,
        ExplorationStopReason::FrontierExhausted,
        visited.len(),
        frontier.len(),
        stats,
        None,
        None,
        None,
    ))
}

fn dedup_key_from_canonical(canonical: &str, mode: StateDedupMode) -> String {
    match mode {
        StateDedupMode::Canonical => canonical.to_string(),
        StateDedupMode::HashCompaction64 => {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            canonical.hash(&mut hasher);
            format!("h{:016x}", hasher.finish())
        }
    }
}

fn is_hash_collision(
    representatives: &std::collections::BTreeMap<String, String>,
    key: &str,
    canonical: &str,
) -> bool {
    representatives
        .get(key)
        .map(|existing| existing != canonical)
        .unwrap_or(false)
}

fn record_symmetry_collapse(
    representatives: &mut std::collections::BTreeMap<String, BTreeSet<String>>,
    symmetry_key: &str,
    raw_key: &str,
) -> bool {
    let raw_keys = representatives.entry(symmetry_key.to_string()).or_default();
    let inserted = raw_keys.insert(raw_key.to_string());
    inserted && raw_keys.len() > 1
}

fn canonical_dedup_key(state: &RuntimeValue, symmetry_fields: &BTreeSet<&str>) -> String {
    if symmetry_fields.is_empty() {
        return state.canonical_key();
    }

    match state {
        RuntimeValue::Struct { ty, fields } => {
            let mut parts = Vec::new();
            for (name, value) in fields {
                let field_key = if symmetry_fields.contains(name.as_str()) {
                    symmetry_normalized_key(value)
                } else {
                    value.canonical_key()
                };
                parts.push(format!("{name}:{field_key}"));
            }
            format!("struct:{ty}{{{}}}", parts.join(","))
        }
        _ => state.canonical_key(),
    }
}

fn symmetry_normalized_key(value: &RuntimeValue) -> String {
    let mut atoms = std::collections::BTreeMap::<String, usize>::new();
    symmetry_normalized_key_with_atoms(value, &mut atoms)
}

fn symmetry_normalized_key_with_atoms(
    value: &RuntimeValue,
    atoms: &mut std::collections::BTreeMap<String, usize>,
) -> String {
    match value {
        RuntimeValue::Unit => "unit".to_string(),
        RuntimeValue::Bool(v) => format!("bool:{v}"),
        RuntimeValue::Int(v) => symmetry_atom_key(format!("int:{v}"), atoms),
        RuntimeValue::Nat(v) => symmetry_atom_key(format!("nat:{v}"), atoms),
        RuntimeValue::String(v) => symmetry_atom_key(format!("string:{v}"), atoms),
        RuntimeValue::Enum {
            ty,
            variant,
            fields,
        } if fields.is_empty() => symmetry_atom_key(format!("enum:{ty}::{variant}"), atoms),
        RuntimeValue::Enum {
            ty,
            variant,
            fields,
        } => {
            let field_parts = fields
                .iter()
                .map(|(k, v)| format!("{k}:{}", symmetry_normalized_key_with_atoms(v, atoms)))
                .collect::<Vec<_>>()
                .join(",");
            format!("enum:{ty}::{variant}{{{field_parts}}}")
        }
        RuntimeValue::Struct { ty, fields } => {
            let field_parts = fields
                .iter()
                .map(|(k, v)| format!("{k}:{}", symmetry_normalized_key_with_atoms(v, atoms)))
                .collect::<Vec<_>>()
                .join(",");
            format!("struct:{ty}{{{field_parts}}}")
        }
        RuntimeValue::Tuple(values) => {
            let parts = values
                .iter()
                .map(|v| symmetry_normalized_key_with_atoms(v, atoms))
                .collect::<Vec<_>>()
                .join(",");
            format!("tuple:[{parts}]")
        }
        RuntimeValue::Seq(values) => {
            let parts = values
                .iter()
                .map(|v| symmetry_normalized_key_with_atoms(v, atoms))
                .collect::<Vec<_>>()
                .join(",");
            format!("seq:[{parts}]")
        }
        RuntimeValue::Set(items) => {
            let mut parts = items
                .iter()
                .map(|v| symmetry_normalized_key_with_atoms(v, atoms))
                .collect::<Vec<_>>();
            parts.sort();
            format!("set:[{}]", parts.join(","))
        }
        RuntimeValue::Map(entries) => {
            let mut parts = entries
                .iter()
                .map(|(k, v)| {
                    format!(
                        "{}=>{}",
                        symmetry_normalized_key_with_atoms(k, atoms),
                        symmetry_normalized_key_with_atoms(v, atoms)
                    )
                })
                .collect::<Vec<_>>();
            parts.sort();
            format!("map:[{}]", parts.join(","))
        }
    }
}

fn symmetry_atom_key(raw: String, atoms: &mut std::collections::BTreeMap<String, usize>) -> String {
    let next = atoms.len();
    let id = *atoms.entry(raw).or_insert(next);
    format!("a{id}")
}

fn finalize_result(
    explored: Vec<ExploredState>,
    stop_reason: ExplorationStopReason,
    visited_len: usize,
    frontier_len: usize,
    mut stats: ExplorationStats,
    invariant_violation: Option<InvariantViolation>,
    deadlock: Option<DeadlockDetection>,
    counterexample: Option<CounterexampleTrace>,
) -> ExplorationResult {
    stats.explored_states = explored.len();
    stats.visited_states = visited_len;
    stats.frontier_size_at_stop = frontier_len;
    ExplorationResult {
        explored,
        stop_reason,
        stats,
        invariant_violation,
        deadlock,
        counterexample,
    }
}

fn build_counterexample_trace(
    failure_key: &str,
    states_by_key: &std::collections::BTreeMap<String, RuntimeValue>,
    parents: &std::collections::BTreeMap<String, TraceParent>,
) -> Option<CounterexampleTrace> {
    let mut path = Vec::new();
    let mut cursor = failure_key.to_string();
    path.push(cursor.clone());
    while let Some(parent) = parents.get(&cursor) {
        cursor = parent.parent_key.clone();
        path.push(cursor.clone());
    }
    path.reverse();

    let initial_key = path.first()?;
    let initial_state = states_by_key.get(initial_key)?.clone();
    let mut steps = Vec::new();
    for window in path.windows(2) {
        let from_key = &window[0];
        let to_key = &window[1];
        let edge = parents.get(to_key)?;
        let from_state = states_by_key.get(from_key)?;
        let to_state = states_by_key.get(to_key)?;
        steps.push(CounterexampleStep {
            action_branch: edge.action_branch.clone(),
            state: to_state.clone(),
            diffs: summarize_state_diff(from_state, to_state),
        });
    }

    Some(CounterexampleTrace {
        initial_state,
        steps,
    })
}

fn summarize_state_diff(before: &RuntimeValue, after: &RuntimeValue) -> Vec<StateDiffSummary> {
    let mut diffs = Vec::new();
    collect_state_diffs("s", before, after, &mut diffs);
    diffs
}

fn collect_state_diffs(
    path: &str,
    before: &RuntimeValue,
    after: &RuntimeValue,
    diffs: &mut Vec<StateDiffSummary>,
) {
    if before == after {
        return;
    }

    match (before, after) {
        (
            RuntimeValue::Struct {
                ty: b_ty,
                fields: b_fields,
            },
            RuntimeValue::Struct {
                ty: a_ty,
                fields: a_fields,
            },
        ) if b_ty == a_ty => collect_named_field_diffs(path, b_fields, a_fields, diffs),
        (
            RuntimeValue::Enum {
                ty: b_ty,
                variant: b_variant,
                fields: b_fields,
            },
            RuntimeValue::Enum {
                ty: a_ty,
                variant: a_variant,
                fields: a_fields,
            },
        ) if b_ty == a_ty && b_variant == a_variant => {
            collect_named_field_diffs(path, b_fields, a_fields, diffs)
        }
        (RuntimeValue::Tuple(b_values), RuntimeValue::Tuple(a_values))
        | (RuntimeValue::Seq(b_values), RuntimeValue::Seq(a_values)) => {
            let max_len = b_values.len().max(a_values.len());
            for idx in 0..max_len {
                let sub_path = format!("{path}[{idx}]");
                match (b_values.get(idx), a_values.get(idx)) {
                    (Some(b), Some(a)) => collect_state_diffs(&sub_path, b, a, diffs),
                    (Some(b), None) => diffs.push(StateDiffSummary {
                        path: sub_path,
                        before: b.canonical_key(),
                        after: "<missing>".to_string(),
                    }),
                    (None, Some(a)) => diffs.push(StateDiffSummary {
                        path: sub_path,
                        before: "<missing>".to_string(),
                        after: a.canonical_key(),
                    }),
                    (None, None) => {}
                }
            }
        }
        _ => diffs.push(StateDiffSummary {
            path: path.to_string(),
            before: before.canonical_key(),
            after: after.canonical_key(),
        }),
    }
}

fn collect_named_field_diffs(
    path: &str,
    before: &std::collections::BTreeMap<String, RuntimeValue>,
    after: &std::collections::BTreeMap<String, RuntimeValue>,
    diffs: &mut Vec<StateDiffSummary>,
) {
    let mut keys: BTreeSet<String> = BTreeSet::new();
    keys.extend(before.keys().cloned());
    keys.extend(after.keys().cloned());
    for key in keys {
        let sub_path = format!("{path}.{key}");
        match (before.get(&key), after.get(&key)) {
            (Some(b), Some(a)) => collect_state_diffs(&sub_path, b, a, diffs),
            (Some(b), None) => diffs.push(StateDiffSummary {
                path: sub_path,
                before: b.canonical_key(),
                after: "<missing>".to_string(),
            }),
            (None, Some(a)) => diffs.push(StateDiffSummary {
                path: sub_path,
                before: "<missing>".to_string(),
                after: a.canonical_key(),
            }),
            (None, None) => {}
        }
    }
}

fn validate_limits(limits: ExplorationLimits) -> TranspileResult<()> {
    if limits.max_states == 0 {
        return Err(TranspileError::Config {
            message: "Invalid model-check exploration limits: `max_states` must be > 0."
                .to_string(),
        });
    }
    Ok(())
}

fn pop_frontier(frontier: &mut VecDeque<FrontierItem>, mode: SearchMode) -> Option<FrontierItem> {
    match mode {
        SearchMode::Bfs => frontier.pop_front(),
        SearchMode::Dfs => frontier.pop_back(),
    }
}

fn push_successors(
    frontier: &mut VecDeque<FrontierItem>,
    mode: SearchMode,
    mut successors: Vec<FrontierItem>,
) {
    match mode {
        SearchMode::Bfs => {
            for successor in successors {
                frontier.push_back(successor);
            }
        }
        SearchMode::Dfs => {
            successors.reverse();
            for successor in successors {
                frontier.push_back(successor);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    fn state(id: i128) -> RuntimeValue {
        RuntimeValue::struct_value("LState", vec![("id".to_string(), RuntimeValue::Int(id))])
            .unwrap()
    }

    fn state_id(state: &RuntimeValue) -> i128 {
        match state {
            RuntimeValue::Struct { fields, .. } => match fields.get("id") {
                Some(RuntimeValue::Int(v)) => *v,
                other => panic!("invalid id field: {other:?}"),
            },
            other => panic!("expected struct state, got {other:?}"),
        }
    }

    fn ids(result: &ExplorationResult) -> Vec<i128> {
        result.explored.iter().map(|s| state_id(&s.state)).collect()
    }

    #[test]
    fn test_explore_state_space_bfs_order() {
        let graph = BTreeMap::from([
            (0, vec![1, 2]),
            (1, vec![3]),
            (2, vec![4]),
            (3, vec![]),
            (4, vec![]),
        ]);
        let result = explore_state_space(
            &[state(0)],
            SearchMode::Bfs,
            ExplorationLimits {
                max_depth: 10,
                max_states: 20,
            },
            |s| {
                let next = graph
                    .get(&state_id(s))
                    .unwrap()
                    .iter()
                    .map(|i| state(*i))
                    .collect();
                Ok(next)
            },
        )
        .unwrap();
        assert_eq!(ids(&result), vec![0, 1, 2, 3, 4]);
        assert_eq!(result.stop_reason, ExplorationStopReason::FrontierExhausted);
    }

    #[test]
    fn test_explore_state_space_dfs_order() {
        let graph = BTreeMap::from([
            (0, vec![1, 2]),
            (1, vec![3]),
            (2, vec![4]),
            (3, vec![]),
            (4, vec![]),
        ]);
        let result = explore_state_space(
            &[state(0)],
            SearchMode::Dfs,
            ExplorationLimits {
                max_depth: 10,
                max_states: 20,
            },
            |s| {
                let next = graph
                    .get(&state_id(s))
                    .unwrap()
                    .iter()
                    .map(|i| state(*i))
                    .collect();
                Ok(next)
            },
        )
        .unwrap();
        assert_eq!(ids(&result), vec![0, 1, 3, 2, 4]);
        assert_eq!(result.stop_reason, ExplorationStopReason::FrontierExhausted);
    }

    #[test]
    fn test_explore_state_space_deduplicates_cycles() {
        let graph = BTreeMap::from([(0, vec![1]), (1, vec![0, 2]), (2, vec![])]);
        let result = explore_state_space(
            &[state(0)],
            SearchMode::Bfs,
            ExplorationLimits {
                max_depth: 10,
                max_states: 20,
            },
            |s| {
                let next = graph
                    .get(&state_id(s))
                    .unwrap()
                    .iter()
                    .map(|i| state(*i))
                    .collect();
                Ok(next)
            },
        )
        .unwrap();
        assert_eq!(ids(&result), vec![0, 1, 2]);
    }

    #[test]
    fn test_explore_state_space_respects_depth_bound() {
        let graph = BTreeMap::from([(0, vec![1]), (1, vec![2]), (2, vec![3]), (3, vec![])]);
        let result = explore_state_space(
            &[state(0)],
            SearchMode::Bfs,
            ExplorationLimits {
                max_depth: 1,
                max_states: 20,
            },
            |s| {
                let next = graph
                    .get(&state_id(s))
                    .unwrap()
                    .iter()
                    .map(|i| state(*i))
                    .collect();
                Ok(next)
            },
        )
        .unwrap();
        assert_eq!(ids(&result), vec![0, 1]);
    }

    #[test]
    fn test_explore_state_space_stops_on_max_states() {
        let graph = BTreeMap::from([(0, vec![1, 2, 3]), (1, vec![]), (2, vec![]), (3, vec![])]);
        let result = explore_state_space(
            &[state(0)],
            SearchMode::Bfs,
            ExplorationLimits {
                max_depth: 10,
                max_states: 2,
            },
            |s| {
                let next = graph
                    .get(&state_id(s))
                    .unwrap()
                    .iter()
                    .map(|i| state(*i))
                    .collect();
                Ok(next)
            },
        )
        .unwrap();

        assert_eq!(result.stop_reason, ExplorationStopReason::MaxStatesReached);
        assert_eq!(ids(&result), vec![0]);
    }

    #[test]
    fn test_explore_state_space_rejects_zero_max_states() {
        let err = explore_state_space(
            &[state(0)],
            SearchMode::Bfs,
            ExplorationLimits {
                max_depth: 10,
                max_states: 0,
            },
            |_| Ok(vec![]),
        )
        .unwrap_err();
        assert!(err.to_string().contains("max_states"));
    }

    #[test]
    fn test_explore_state_space_reports_statistics() {
        let graph = BTreeMap::from([(0, vec![1, 2]), (1, vec![2]), (2, vec![])]);
        let result = explore_state_space(
            &[state(0)],
            SearchMode::Bfs,
            ExplorationLimits {
                max_depth: 10,
                max_states: 20,
            },
            |s| {
                let next = graph
                    .get(&state_id(s))
                    .unwrap()
                    .iter()
                    .map(|i| state(*i))
                    .collect();
                Ok(next)
            },
        )
        .unwrap();

        assert_eq!(result.stop_reason, ExplorationStopReason::FrontierExhausted);
        assert_eq!(result.stats.initial_states, 1);
        assert_eq!(result.stats.explored_states, 3);
        assert_eq!(result.stats.visited_states, 3);
        assert_eq!(result.stats.max_frontier_size, 2);
        assert_eq!(result.stats.frontier_size_at_stop, 0);
        assert_eq!(result.stats.successors_considered, 3);
        assert_eq!(result.stats.successors_enqueued, 2);
        assert_eq!(result.stats.duplicate_successors, 1);
    }

    #[test]
    fn test_explore_state_space_reports_statistics_on_max_states_stop() {
        let graph = BTreeMap::from([(0, vec![1, 2, 3]), (1, vec![]), (2, vec![]), (3, vec![])]);
        let result = explore_state_space(
            &[state(0)],
            SearchMode::Bfs,
            ExplorationLimits {
                max_depth: 10,
                max_states: 2,
            },
            |s| {
                let next = graph
                    .get(&state_id(s))
                    .unwrap()
                    .iter()
                    .map(|i| state(*i))
                    .collect();
                Ok(next)
            },
        )
        .unwrap();

        assert_eq!(result.stop_reason, ExplorationStopReason::MaxStatesReached);
        assert_eq!(result.stats.initial_states, 1);
        assert_eq!(result.stats.explored_states, 1);
        assert_eq!(result.stats.visited_states, 2);
        assert_eq!(result.stats.max_frontier_size, 1);
        assert_eq!(result.stats.frontier_size_at_stop, 0);
        assert_eq!(result.stats.successors_considered, 2);
        assert_eq!(result.stats.successors_enqueued, 1);
        assert_eq!(result.stats.duplicate_successors, 0);
    }

    #[test]
    fn test_explore_state_space_with_invariants_stops_on_violation() {
        let graph = BTreeMap::from([(0, vec![1]), (1, vec![2]), (2, vec![])]);
        let result = explore_state_space_with_invariants(
            &[state(0)],
            SearchMode::Bfs,
            ExplorationLimits {
                max_depth: 10,
                max_states: 20,
            },
            |s| {
                let next = graph
                    .get(&state_id(s))
                    .unwrap()
                    .iter()
                    .map(|i| state(*i))
                    .collect();
                Ok(next)
            },
            |s, _depth| {
                if state_id(s) == 1 {
                    Ok(Some("LSafety".to_string()))
                } else {
                    Ok(None)
                }
            },
        )
        .unwrap();

        assert_eq!(result.stop_reason, ExplorationStopReason::InvariantViolated);
        assert_eq!(ids(&result), vec![0, 1]);
        assert_eq!(
            result.invariant_violation,
            Some(InvariantViolation {
                invariant: "LSafety".to_string(),
                state: state(1),
                depth: 1,
            })
        );
        assert_eq!(result.stats.successors_considered, 1);
        assert_eq!(result.stats.successors_enqueued, 1);
    }

    #[test]
    fn test_explore_state_space_with_invariants_checks_initial_states() {
        let mut successor_calls = 0usize;
        let result = explore_state_space_with_invariants(
            &[state(0)],
            SearchMode::Bfs,
            ExplorationLimits {
                max_depth: 10,
                max_states: 20,
            },
            |_| {
                successor_calls += 1;
                Ok(vec![state(1)])
            },
            |_s, depth| {
                if depth == 0 {
                    Ok(Some("LTypeOK".to_string()))
                } else {
                    Ok(None)
                }
            },
        )
        .unwrap();

        assert_eq!(result.stop_reason, ExplorationStopReason::InvariantViolated);
        assert_eq!(ids(&result), vec![0]);
        assert_eq!(successor_calls, 0);
    }

    #[test]
    fn test_explore_state_space_with_invariants_has_no_violation_when_all_hold() {
        let graph = BTreeMap::from([(0, vec![1]), (1, vec![])]);
        let result = explore_state_space_with_invariants(
            &[state(0)],
            SearchMode::Bfs,
            ExplorationLimits {
                max_depth: 10,
                max_states: 20,
            },
            |s| {
                let next = graph
                    .get(&state_id(s))
                    .unwrap()
                    .iter()
                    .map(|i| state(*i))
                    .collect();
                Ok(next)
            },
            |_s, _depth| Ok(None),
        )
        .unwrap();

        assert_eq!(result.stop_reason, ExplorationStopReason::FrontierExhausted);
        assert_eq!(ids(&result), vec![0, 1]);
        assert_eq!(result.invariant_violation, None);
    }

    #[test]
    fn test_explore_state_space_with_checks_detects_deadlock_when_enabled() {
        let graph = BTreeMap::from([(0, vec![1]), (1, vec![])]);
        let result = explore_state_space_with_checks(
            &[state(0)],
            SearchMode::Bfs,
            ExplorationLimits {
                max_depth: 10,
                max_states: 20,
            },
            true,
            |s| {
                let next = graph
                    .get(&state_id(s))
                    .unwrap()
                    .iter()
                    .map(|i| state(*i))
                    .collect();
                Ok(next)
            },
            |_s, _depth| Ok(None),
        )
        .unwrap();

        assert_eq!(result.stop_reason, ExplorationStopReason::DeadlockDetected);
        assert_eq!(ids(&result), vec![0, 1]);
        assert_eq!(
            result.deadlock,
            Some(DeadlockDetection {
                state: state(1),
                depth: 1,
            })
        );
        assert_eq!(result.invariant_violation, None);
    }

    #[test]
    fn test_explore_state_space_with_checks_ignores_deadlock_when_disabled() {
        let graph = BTreeMap::from([(0, vec![1]), (1, vec![])]);
        let result = explore_state_space_with_checks(
            &[state(0)],
            SearchMode::Bfs,
            ExplorationLimits {
                max_depth: 10,
                max_states: 20,
            },
            false,
            |s| {
                let next = graph
                    .get(&state_id(s))
                    .unwrap()
                    .iter()
                    .map(|i| state(*i))
                    .collect();
                Ok(next)
            },
            |_s, _depth| Ok(None),
        )
        .unwrap();

        assert_eq!(result.stop_reason, ExplorationStopReason::FrontierExhausted);
        assert_eq!(ids(&result), vec![0, 1]);
        assert_eq!(result.deadlock, None);
    }

    #[test]
    fn test_explore_state_space_with_checks_does_not_treat_depth_bound_as_deadlock() {
        let graph = BTreeMap::from([(0, vec![1]), (1, vec![])]);
        let result = explore_state_space_with_checks(
            &[state(0)],
            SearchMode::Bfs,
            ExplorationLimits {
                max_depth: 1,
                max_states: 20,
            },
            true,
            |s| {
                let next = graph
                    .get(&state_id(s))
                    .unwrap()
                    .iter()
                    .map(|i| state(*i))
                    .collect();
                Ok(next)
            },
            |_s, _depth| Ok(None),
        )
        .unwrap();

        assert_eq!(result.stop_reason, ExplorationStopReason::FrontierExhausted);
        assert_eq!(ids(&result), vec![0, 1]);
        assert_eq!(result.deadlock, None);
    }

    #[test]
    fn test_explore_state_space_with_traces_emits_invariant_counterexample() {
        let graph = BTreeMap::from([
            (0, vec![(1, "LStep")]),
            (1, vec![(2, "LCommit")]),
            (2, vec![]),
        ]);
        let result = explore_state_space_with_traces(
            &[state(0)],
            SearchMode::Bfs,
            ExplorationLimits {
                max_depth: 10,
                max_states: 20,
            },
            false,
            |s| {
                let next = graph
                    .get(&state_id(s))
                    .unwrap()
                    .iter()
                    .map(|(id, action)| TracedSuccessor {
                        action_branch: (*action).to_string(),
                        state: state(*id),
                    })
                    .collect();
                Ok(next)
            },
            |s, _| {
                if state_id(s) == 2 {
                    Ok(Some("LSafety".to_string()))
                } else {
                    Ok(None)
                }
            },
        )
        .unwrap();

        assert_eq!(result.stop_reason, ExplorationStopReason::InvariantViolated);
        let trace = result.counterexample.expect("expected counterexample");
        assert_eq!(state_id(&trace.initial_state), 0);
        assert_eq!(trace.steps.len(), 2);
        assert_eq!(trace.steps[0].action_branch, "LStep");
        assert_eq!(state_id(&trace.steps[0].state), 1);
        assert_eq!(trace.steps[1].action_branch, "LCommit");
        assert_eq!(state_id(&trace.steps[1].state), 2);
        assert_eq!(trace.steps[1].diffs[0].path, "s.id");
        assert!(trace.steps[1].diffs[0].before.contains("int:1"));
        assert!(trace.steps[1].diffs[0].after.contains("int:2"));
    }

    #[test]
    fn test_explore_state_space_with_traces_emits_deadlock_counterexample() {
        let graph = BTreeMap::from([(0, vec![(1, "LAdvance")]), (1, vec![])]);
        let result = explore_state_space_with_traces(
            &[state(0)],
            SearchMode::Bfs,
            ExplorationLimits {
                max_depth: 10,
                max_states: 20,
            },
            true,
            |s| {
                let next = graph
                    .get(&state_id(s))
                    .unwrap()
                    .iter()
                    .map(|(id, action)| TracedSuccessor {
                        action_branch: (*action).to_string(),
                        state: state(*id),
                    })
                    .collect();
                Ok(next)
            },
            |_s, _| Ok(None),
        )
        .unwrap();

        assert_eq!(result.stop_reason, ExplorationStopReason::DeadlockDetected);
        let trace = result.counterexample.expect("expected counterexample");
        assert_eq!(state_id(&trace.initial_state), 0);
        assert_eq!(trace.steps.len(), 1);
        assert_eq!(trace.steps[0].action_branch, "LAdvance");
        assert_eq!(state_id(&trace.steps[0].state), 1);
    }

    #[test]
    fn test_dedup_key_from_canonical_hash_compaction64_is_stable() {
        let canonical = "struct:LState{id=int:42}";
        let key_a = dedup_key_from_canonical(canonical, StateDedupMode::HashCompaction64);
        let key_b = dedup_key_from_canonical(canonical, StateDedupMode::HashCompaction64);
        let exact = dedup_key_from_canonical(canonical, StateDedupMode::Canonical);

        assert_eq!(key_a, key_b);
        assert_ne!(key_a, exact);
        assert!(key_a.starts_with('h'));
        assert_eq!(key_a.len(), 17);
    }

    #[test]
    fn test_is_hash_collision_detects_distinct_canonical_representatives() {
        let mut reps = BTreeMap::new();
        reps.insert(
            "h00000000000000aa".to_string(),
            "struct:LState{id=int:1}".to_string(),
        );

        assert!(!is_hash_collision(
            &reps,
            "h00000000000000aa",
            "struct:LState{id=int:1}"
        ));
        assert!(is_hash_collision(
            &reps,
            "h00000000000000aa",
            "struct:LState{id=int:2}"
        ));
        assert!(!is_hash_collision(
            &reps,
            "h00000000000000bb",
            "struct:LState{id=int:2}"
        ));
    }

    #[test]
    fn test_explore_state_space_with_traces_hash_compaction_reports_collision_stats() {
        let graph = BTreeMap::from([(0, vec![(1, "LStep")]), (1, vec![(0, "LBack")])]);
        let result = explore_state_space_with_traces_and_dedup(
            &[state(0)],
            SearchMode::Bfs,
            ExplorationLimits {
                max_depth: 5,
                max_states: 20,
            },
            StateDedupMode::HashCompaction64,
            &[],
            false,
            |s| {
                let next = graph
                    .get(&state_id(s))
                    .unwrap()
                    .iter()
                    .map(|(id, action)| TracedSuccessor {
                        action_branch: (*action).to_string(),
                        state: state(*id),
                    })
                    .collect();
                Ok(next)
            },
            |_s, _| Ok(None),
        )
        .unwrap();

        assert_eq!(result.stop_reason, ExplorationStopReason::FrontierExhausted);
        assert_eq!(ids(&result), vec![0, 1]);
        assert_eq!(result.stats.duplicate_successors, 1);
        assert_eq!(result.stats.hash_compaction_collisions, 0);
        assert_eq!(result.stats.symmetry_collapses, 0);
    }

    #[test]
    fn test_explore_state_space_with_traces_symmetry_fields_deduplicate_initial_states() {
        let result = explore_state_space_with_traces_and_dedup(
            &[state(1), state(2)],
            SearchMode::Bfs,
            ExplorationLimits {
                max_depth: 3,
                max_states: 20,
            },
            StateDedupMode::Canonical,
            &["id".to_string()],
            false,
            |_s| Ok(vec![]),
            |_s, _| Ok(None),
        )
        .unwrap();

        assert_eq!(result.stop_reason, ExplorationStopReason::FrontierExhausted);
        assert_eq!(result.stats.initial_states, 1);
        assert_eq!(result.stats.visited_states, 1);
        assert_eq!(result.stats.symmetry_collapses, 1);
        assert_eq!(ids(&result), vec![1]);
    }

    #[test]
    fn test_explore_state_space_with_traces_symmetry_fields_ignore_unknown_field() {
        let result = explore_state_space_with_traces_and_dedup(
            &[state(1), state(2)],
            SearchMode::Bfs,
            ExplorationLimits {
                max_depth: 3,
                max_states: 20,
            },
            StateDedupMode::Canonical,
            &["unknown_field".to_string()],
            false,
            |_s| Ok(vec![]),
            |_s, _| Ok(None),
        )
        .unwrap();

        assert_eq!(result.stop_reason, ExplorationStopReason::FrontierExhausted);
        assert_eq!(result.stats.initial_states, 2);
        assert_eq!(result.stats.visited_states, 2);
        assert_eq!(result.stats.symmetry_collapses, 0);
        assert_eq!(ids(&result), vec![1, 2]);
    }
}
