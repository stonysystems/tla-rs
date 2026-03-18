//! Parity export for cross-engine state-set comparison.
//!
//! Exports the explored state graph as sorted JSON Lines (`.jsonl`)
//! following the canonical normalization schema defined in
//! `docs/cross-engine-state-normalization.md`.

use crate::modelcheck::graph::ExploredGraphIndex;
use crate::modelcheck::value::RuntimeValue;
use std::collections::BTreeSet;
use std::io::Write;

/// One line in the parity JSONL export.
fn state_to_jsonl_line(
    canonical_key: &str,
    state: &RuntimeValue,
    is_initial: bool,
    depth: usize,
) -> String {
    let obj = serde_json::json!({
        "id": canonical_key,
        "state": state.to_canonical_json(),
        "initial": is_initial,
        "depth": depth,
    });
    serde_json::to_string(&obj).expect("JSON serialization should not fail")
}

/// One line in the edge JSONL export.
fn edge_to_jsonl_line(src_key: &str, dst_key: &str, action: &str) -> String {
    let obj = serde_json::json!({
        "src": src_key,
        "dst": dst_key,
        "action": action,
    });
    serde_json::to_string(&obj).expect("JSON serialization should not fail")
}

/// Export the explored state graph as two JSONL files: states and edges.
///
/// - `states_writer`: receives one JSON object per line (sorted by canonical key)
/// - `edges_writer`: receives one JSON object per line (sorted by src, dst, action)
/// - `initial_state_keys`: set of canonical keys that are initial states
pub fn export_parity_jsonl<W1: Write, W2: Write>(
    graph: &ExploredGraphIndex,
    initial_state_keys: &BTreeSet<String>,
    states_writer: &mut W1,
    edges_writer: &mut W2,
) -> std::io::Result<()> {
    // States: sorted by canonical key (BTreeMap iteration order)
    for (key, meta) in &graph.nodes {
        let line = state_to_jsonl_line(
            key,
            &meta.state,
            initial_state_keys.contains(key),
            meta.depth,
        );
        writeln!(states_writer, "{line}")?;
    }

    // Edges: sorted by (src, dst, action) — BTreeMap iteration + BTreeSet iteration
    for (edge_key, branches) in &graph.edge_branches {
        for action in branches {
            let line = edge_to_jsonl_line(&edge_key.from_key, &edge_key.to_key, action);
            writeln!(edges_writer, "{line}")?;
        }
    }

    Ok(())
}

/// Collect canonical keys for initial states from the initial-state slice.
pub fn collect_initial_state_keys(initial_states: &[RuntimeValue]) -> BTreeSet<String> {
    initial_states.iter().map(|s| s.canonical_key()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::modelcheck::graph::{GraphEdgeKey, GraphIndexStats, GraphNodeMetadata};
    use std::collections::BTreeMap;

    fn make_state(fields: Vec<(&str, i128)>) -> RuntimeValue {
        RuntimeValue::Struct {
            ty: "LState".to_string(),
            fields: fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), RuntimeValue::Int(v)))
                .collect(),
        }
    }

    #[test]
    fn test_canonical_json_roundtrip() {
        let state = make_state(vec![("x", 1), ("y", 2)]);
        let json = state.to_canonical_json();
        assert_eq!(json, serde_json::json!({"x": 1, "y": 2}));
    }

    #[test]
    fn test_canonical_json_enum() {
        let state = RuntimeValue::Enum {
            ty: "TMState".to_string(),
            variant: "Init".to_string(),
            fields: BTreeMap::new(),
        };
        let json = state.to_canonical_json();
        assert_eq!(json, serde_json::json!({"_variant": "Init"}));
    }

    #[test]
    fn test_canonical_json_set_sorted() {
        let set = RuntimeValue::Set(
            vec![
                RuntimeValue::Int(3),
                RuntimeValue::Int(1),
                RuntimeValue::Int(2),
            ]
            .into_iter()
            .collect(),
        );
        let json = set.to_canonical_json();
        assert_eq!(json, serde_json::json!([1, 2, 3]));
    }

    #[test]
    fn test_canonical_json_map() {
        let map = RuntimeValue::Map(
            vec![
                (RuntimeValue::Int(2), RuntimeValue::Bool(false)),
                (RuntimeValue::Int(1), RuntimeValue::Bool(true)),
            ]
            .into_iter()
            .collect(),
        );
        let json = map.to_canonical_json();
        assert_eq!(json, serde_json::json!([[1, true], [2, false]]));
    }

    #[test]
    fn test_export_parity_jsonl_basic() {
        let s1 = make_state(vec![("x", 0)]);
        let s2 = make_state(vec![("x", 1)]);
        let k1 = s1.canonical_key();
        let k2 = s2.canonical_key();

        let mut nodes = BTreeMap::new();
        nodes.insert(
            k1.clone(),
            GraphNodeMetadata {
                state: s1.clone(),
                depth: 0,
            },
        );
        nodes.insert(
            k2.clone(),
            GraphNodeMetadata {
                state: s2.clone(),
                depth: 1,
            },
        );

        let mut successors = BTreeMap::new();
        let mut s1_succs = BTreeSet::new();
        s1_succs.insert(k2.clone());
        successors.insert(k1.clone(), s1_succs);
        successors.insert(k2.clone(), BTreeSet::new());

        let mut predecessors = BTreeMap::new();
        predecessors.insert(k1.clone(), BTreeSet::new());
        let mut k2_preds = BTreeSet::new();
        k2_preds.insert(k1.clone());
        predecessors.insert(k2.clone(), k2_preds);

        let mut edge_branches = BTreeMap::new();
        let mut branches = BTreeSet::new();
        branches.insert("Step".to_string());
        edge_branches.insert(
            GraphEdgeKey {
                from_key: k1.clone(),
                to_key: k2.clone(),
            },
            branches,
        );

        let graph = ExploredGraphIndex {
            nodes,
            successors,
            predecessors,
            edge_branches,
            stats: GraphIndexStats::default(),
        };

        let mut initial_keys = BTreeSet::new();
        initial_keys.insert(k1.clone());

        let mut states_buf = Vec::new();
        let mut edges_buf = Vec::new();
        export_parity_jsonl(&graph, &initial_keys, &mut states_buf, &mut edges_buf).unwrap();

        let states_str = String::from_utf8(states_buf).unwrap();
        let edges_str = String::from_utf8(edges_buf).unwrap();

        let state_lines: Vec<&str> = states_str.trim().split('\n').collect();
        assert_eq!(state_lines.len(), 2);

        // Verify first state line parses and has correct structure
        let first: serde_json::Value = serde_json::from_str(state_lines[0]).unwrap();
        assert!(first["id"].is_string());
        assert!(first["state"].is_object());
        assert!(first["depth"].is_number());

        let edge_lines: Vec<&str> = edges_str.trim().split('\n').collect();
        assert_eq!(edge_lines.len(), 1);
        let edge: serde_json::Value = serde_json::from_str(edge_lines[0]).unwrap();
        assert_eq!(edge["action"], "Step");
    }
}
