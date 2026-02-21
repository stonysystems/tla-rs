use crate::error::TranspileResult;
use crate::modelcheck::explorer::{ExploredState, TracedSuccessor};
use crate::modelcheck::value::RuntimeValue;
use std::collections::{BTreeMap, BTreeSet};

/// Per-state metadata stored in the explored graph index.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GraphNodeMetadata {
    pub state: RuntimeValue,
    pub depth: usize,
}

/// Directed edge key for branch-label metadata.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct GraphEdgeKey {
    pub from_key: String,
    pub to_key: String,
}

/// Build-time summary for explored-graph indexing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct GraphIndexStats {
    /// Number of successor edges returned by `successor_fn` across indexed nodes.
    pub edges_considered: usize,
    /// Number of edges whose destination is also in the explored-node set.
    pub edges_within_explored: usize,
    /// Number of edges dropped because destination is outside explored-node set.
    pub edges_to_unexplored: usize,
}

/// Adjacency index over already-explored states.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExploredGraphIndex {
    /// Node metadata keyed by canonical runtime state key.
    pub nodes: BTreeMap<String, GraphNodeMetadata>,
    /// Outgoing adjacency keyed by source node key.
    pub successors: BTreeMap<String, BTreeSet<String>>,
    /// Incoming adjacency keyed by destination node key.
    pub predecessors: BTreeMap<String, BTreeSet<String>>,
    /// Action-branch labels seen on each directed edge.
    pub edge_branches: BTreeMap<GraphEdgeKey, BTreeSet<String>>,
    pub stats: GraphIndexStats,
}

impl ExploredGraphIndex {
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    pub fn edge_count(&self) -> usize {
        self.edge_branches.len()
    }
}

/// Build a reusable adjacency index from explored states and traced successors.
///
/// Only transitions that stay within the explored-node set are indexed. Edges to
/// unexplored destinations are counted in stats and skipped from adjacency maps.
pub fn build_explored_graph_index<F>(
    explored: &[ExploredState],
    mut successor_fn: F,
) -> TranspileResult<ExploredGraphIndex>
where
    F: FnMut(&RuntimeValue) -> TranspileResult<Vec<TracedSuccessor>>,
{
    let mut nodes = BTreeMap::<String, GraphNodeMetadata>::new();
    for explored_state in explored {
        let key = explored_state.state.canonical_key();
        match nodes.get_mut(&key) {
            Some(existing) => {
                // Keep the shallowest depth when duplicate keys are present.
                if explored_state.depth < existing.depth {
                    existing.depth = explored_state.depth;
                    existing.state = explored_state.state.clone();
                }
            }
            None => {
                nodes.insert(
                    key,
                    GraphNodeMetadata {
                        state: explored_state.state.clone(),
                        depth: explored_state.depth,
                    },
                );
            }
        }
    }

    let mut successors = BTreeMap::<String, BTreeSet<String>>::new();
    let mut predecessors = BTreeMap::<String, BTreeSet<String>>::new();
    for key in nodes.keys() {
        successors.insert(key.clone(), BTreeSet::new());
        predecessors.insert(key.clone(), BTreeSet::new());
    }

    let mut edge_branches = BTreeMap::<GraphEdgeKey, BTreeSet<String>>::new();
    let mut stats = GraphIndexStats::default();
    let node_entries: Vec<(String, RuntimeValue)> = nodes
        .iter()
        .map(|(key, meta)| (key.clone(), meta.state.clone()))
        .collect();

    for (from_key, from_state) in node_entries {
        let traced_successors = successor_fn(&from_state)?;
        for successor in traced_successors {
            stats.edges_considered += 1;
            let to_key = successor.state.canonical_key();
            if !nodes.contains_key(&to_key) {
                stats.edges_to_unexplored += 1;
                continue;
            }

            stats.edges_within_explored += 1;
            if let Some(outgoing) = successors.get_mut(&from_key) {
                outgoing.insert(to_key.clone());
            }
            if let Some(incoming) = predecessors.get_mut(&to_key) {
                incoming.insert(from_key.clone());
            }
            edge_branches
                .entry(GraphEdgeKey {
                    from_key: from_key.clone(),
                    to_key,
                })
                .or_default()
                .insert(successor.action_branch);
        }
    }

    Ok(ExploredGraphIndex {
        nodes,
        successors,
        predecessors,
        edge_branches,
        stats,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int_state(value: i128) -> RuntimeValue {
        RuntimeValue::Int(value)
    }

    fn edge_key(from: i128, to: i128) -> GraphEdgeKey {
        GraphEdgeKey {
            from_key: int_state(from).canonical_key(),
            to_key: int_state(to).canonical_key(),
        }
    }

    #[test]
    fn test_build_explored_graph_index_builds_successor_and_predecessor_adjacency() {
        let explored = vec![
            ExploredState {
                state: int_state(0),
                depth: 0,
            },
            ExploredState {
                state: int_state(1),
                depth: 1,
            },
            ExploredState {
                state: int_state(2),
                depth: 2,
            },
        ];

        let index = build_explored_graph_index(&explored, |state| {
            let successors = match state {
                RuntimeValue::Int(0) => vec![TracedSuccessor {
                    action_branch: "branch_0".to_string(),
                    state: int_state(1),
                }],
                RuntimeValue::Int(1) => vec![TracedSuccessor {
                    action_branch: "branch_1".to_string(),
                    state: int_state(2),
                }],
                RuntimeValue::Int(2) => vec![TracedSuccessor {
                    action_branch: "branch_2".to_string(),
                    state: int_state(1),
                }],
                _ => Vec::new(),
            };
            Ok(successors)
        })
        .unwrap();

        let k0 = int_state(0).canonical_key();
        let k1 = int_state(1).canonical_key();
        let k2 = int_state(2).canonical_key();

        assert_eq!(index.node_count(), 3);
        assert_eq!(index.edge_count(), 3);
        assert_eq!(
            index.successors.get(&k0).unwrap(),
            &BTreeSet::from([k1.clone()])
        );
        assert_eq!(
            index.predecessors.get(&k1).unwrap(),
            &BTreeSet::from([k0.clone(), k2.clone()])
        );
        assert_eq!(
            index.successors.get(&k1).unwrap(),
            &BTreeSet::from([k2.clone()])
        );
        assert_eq!(
            index.predecessors.get(&k2).unwrap(),
            &BTreeSet::from([k1.clone()])
        );
        assert_eq!(
            index.edge_branches.get(&edge_key(2, 1)).unwrap(),
            &BTreeSet::from(["branch_2".to_string()])
        );
        assert_eq!(index.stats.edges_considered, 3);
        assert_eq!(index.stats.edges_within_explored, 3);
        assert_eq!(index.stats.edges_to_unexplored, 0);
    }

    #[test]
    fn test_build_explored_graph_index_drops_edges_to_unexplored_states() {
        let explored = vec![ExploredState {
            state: int_state(0),
            depth: 0,
        }];

        let index = build_explored_graph_index(&explored, |_| {
            Ok(vec![TracedSuccessor {
                action_branch: "branch_outside".to_string(),
                state: int_state(1),
            }])
        })
        .unwrap();

        let k0 = int_state(0).canonical_key();
        assert_eq!(index.node_count(), 1);
        assert_eq!(index.edge_count(), 0);
        assert!(index.successors.get(&k0).unwrap().is_empty());
        assert!(index.predecessors.get(&k0).unwrap().is_empty());
        assert_eq!(index.stats.edges_considered, 1);
        assert_eq!(index.stats.edges_within_explored, 0);
        assert_eq!(index.stats.edges_to_unexplored, 1);
    }

    #[test]
    fn test_build_explored_graph_index_merges_branch_labels_for_same_edge() {
        let explored = vec![
            ExploredState {
                state: int_state(0),
                depth: 0,
            },
            ExploredState {
                state: int_state(1),
                depth: 1,
            },
        ];

        let index = build_explored_graph_index(&explored, |state| {
            let successors = match state {
                RuntimeValue::Int(0) => vec![
                    TracedSuccessor {
                        action_branch: "branch_alpha".to_string(),
                        state: int_state(1),
                    },
                    TracedSuccessor {
                        action_branch: "branch_beta".to_string(),
                        state: int_state(1),
                    },
                ],
                _ => Vec::new(),
            };
            Ok(successors)
        })
        .unwrap();

        assert_eq!(
            index.edge_branches.get(&edge_key(0, 1)).unwrap(),
            &BTreeSet::from(["branch_alpha".to_string(), "branch_beta".to_string()])
        );
    }

    #[test]
    fn test_build_explored_graph_index_keeps_shallowest_depth_on_duplicate_node_keys() {
        let explored = vec![
            ExploredState {
                state: int_state(1),
                depth: 4,
            },
            ExploredState {
                state: int_state(1),
                depth: 2,
            },
        ];

        let index = build_explored_graph_index(&explored, |_| Ok(Vec::new())).unwrap();
        let k1 = int_state(1).canonical_key();
        assert_eq!(index.nodes.get(&k1).unwrap().depth, 2);
    }
}
