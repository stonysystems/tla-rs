use crate::error::{TranspileError, TranspileResult};
use crate::modelcheck::config::SearchLimits;
use crate::modelcheck::value::RuntimeValue;
use std::collections::{BTreeSet, VecDeque};

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
}

/// Result of running a bounded BFS/DFS exploration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExplorationResult {
    pub explored: Vec<ExploredState>,
    pub stop_reason: ExplorationStopReason,
    pub stats: ExplorationStats,
}

#[derive(Debug, Clone)]
struct FrontierItem {
    state: RuntimeValue,
    depth: usize,
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
    mut successor_fn: F,
) -> TranspileResult<ExplorationResult>
where
    F: FnMut(&RuntimeValue) -> TranspileResult<Vec<RuntimeValue>>,
{
    validate_limits(limits)?;

    let mut visited = BTreeSet::new();
    let mut frontier = VecDeque::new();
    for state in initial_states {
        let key = state.canonical_key();
        if visited.insert(key) {
            frontier.push_back(FrontierItem {
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

        if item.depth >= limits.max_depth {
            continue;
        }

        let successors = successor_fn(&item.state)?;
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
                ));
            }

            let key = successor.canonical_key();
            if visited.insert(key) {
                to_enqueue.push(FrontierItem {
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
    ))
}

fn finalize_result(
    explored: Vec<ExploredState>,
    stop_reason: ExplorationStopReason,
    visited_len: usize,
    frontier_len: usize,
    mut stats: ExplorationStats,
) -> ExplorationResult {
    stats.explored_states = explored.len();
    stats.visited_states = visited_len;
    stats.frontier_size_at_stop = frontier_len;
    ExplorationResult {
        explored,
        stop_reason,
        stats,
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
}
