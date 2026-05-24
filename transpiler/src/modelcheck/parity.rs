//! Parity export for cross-engine state-set comparison.
//!
//! Exports the explored state graph as sorted JSON Lines (`.jsonl`)
//! following the canonical normalization schema defined in
//! `docs/cross-engine-state-normalization.md`.

use crate::modelcheck::graph::ExploredGraphIndex;
use crate::modelcheck::value::RuntimeValue;
use std::collections::BTreeSet;
use std::io::{BufWriter, Write};
use std::path::Path;

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

/// Streaming debug exporter that writes JSONL lines during exploration.
///
/// Produces three files:
/// - `generated_states.jsonl`: every candidate state before dedup (initial + successors)
/// - `distinct_states.jsonl`: every first-seen accepted state
/// - `edges.jsonl`: predecessor→successor edges with branch labels
///
/// This is designed for focused parity fixtures (small state spaces) to enable
/// first-divergence debugging without requiring a second full in-memory graph copy.
pub struct ParityDebugExporter {
    generated_writer: BufWriter<std::fs::File>,
    distinct_writer: BufWriter<std::fs::File>,
    edges_writer: BufWriter<std::fs::File>,
}

impl ParityDebugExporter {
    /// Create a new exporter writing to the given directory.
    /// Creates the directory and the three output files.
    pub fn new(dir: &Path) -> std::io::Result<Self> {
        std::fs::create_dir_all(dir)?;
        Ok(Self {
            generated_writer: BufWriter::new(std::fs::File::create(
                dir.join("generated_states.jsonl"),
            )?),
            distinct_writer: BufWriter::new(std::fs::File::create(
                dir.join("distinct_states.jsonl"),
            )?),
            edges_writer: BufWriter::new(std::fs::File::create(dir.join("edges.jsonl"))?),
        })
    }

    /// Record a generated state (before dedup decision).
    #[allow(clippy::too_many_arguments)]
    pub fn record_generated(
        &mut self,
        state_id: &str,
        state: &RuntimeValue,
        depth: usize,
        is_initial: bool,
        predecessor_id: Option<&str>,
        branch_label: Option<&str>,
        classification: &str,
    ) -> std::io::Result<()> {
        let obj = serde_json::json!({
            "state_id": state_id,
            "state": state.to_canonical_json(),
            "depth": depth,
            "initial": is_initial,
            "branch_label": branch_label,
            "predecessor_state_id": predecessor_id,
            "classification": classification,
        });
        writeln!(
            self.generated_writer,
            "{}",
            serde_json::to_string(&obj).expect("JSON serialization should not fail")
        )
    }

    /// Record a distinct (first-seen accepted) state.
    pub fn record_distinct(
        &mut self,
        state_id: &str,
        state: &RuntimeValue,
        depth: usize,
        is_initial: bool,
        predecessor_id: Option<&str>,
        branch_label: Option<&str>,
    ) -> std::io::Result<()> {
        let obj = serde_json::json!({
            "state_id": state_id,
            "state": state.to_canonical_json(),
            "depth": depth,
            "initial": is_initial,
            "branch_label": branch_label,
            "predecessor_state_id": predecessor_id,
        });
        writeln!(
            self.distinct_writer,
            "{}",
            serde_json::to_string(&obj).expect("JSON serialization should not fail")
        )
    }

    /// Record an edge (predecessor→successor with branch label).
    pub fn record_edge(
        &mut self,
        predecessor_id: &str,
        successor_id: &str,
        branch_label: &str,
        depth: usize,
    ) -> std::io::Result<()> {
        let obj = serde_json::json!({
            "src": predecessor_id,
            "dst": successor_id,
            "branch_label": branch_label,
            "depth": depth,
        });
        writeln!(
            self.edges_writer,
            "{}",
            serde_json::to_string(&obj).expect("JSON serialization should not fail")
        )
    }

    /// Flush all writers.
    pub fn flush(&mut self) -> std::io::Result<()> {
        self.generated_writer.flush()?;
        self.distinct_writer.flush()?;
        self.edges_writer.flush()?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::modelcheck::graph::{GraphEdgeKey, GraphIndexStats, GraphNodeMetadata};
    use std::collections::BTreeMap;

    fn make_state(fields: Vec<(&str, i128)>) -> RuntimeValue {
        RuntimeValue::struct_value_sym(
            "LState",
            fields
                .into_iter()
                .map(|(k, v)| (crate::modelcheck::symbol::Symbol::intern(k), RuntimeValue::Int(v))),
        )
    }

    #[test]
    fn test_canonical_json_roundtrip() {
        let state = make_state(vec![("x", 1), ("y", 2)]);
        let json = state.to_canonical_json();
        assert_eq!(json, serde_json::json!({"x": 1, "y": 2}));
    }

    #[test]
    fn test_canonical_json_enum() {
        let state = RuntimeValue::enum_value_sym(
            "TMState",
            "Init",
            std::iter::empty::<(crate::modelcheck::symbol::Symbol, RuntimeValue)>(),
        );
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

    #[test]
    fn test_parity_debug_exporter_writes_three_files() {
        let dir = tempfile::tempdir().unwrap();
        let s1 = make_state(vec![("x", 0)]);
        let s2 = make_state(vec![("x", 1)]);
        let k1 = s1.canonical_key();
        let k2 = s2.canonical_key();

        {
            let mut exporter = ParityDebugExporter::new(dir.path()).unwrap();

            // Initial state: generated + distinct
            exporter
                .record_generated(&k1, &s1, 0, true, None, None, "accepted_distinct")
                .unwrap();
            exporter
                .record_distinct(&k1, &s1, 0, true, None, None)
                .unwrap();

            // Successor: generated + distinct + edge
            exporter
                .record_generated(
                    &k2,
                    &s2,
                    1,
                    false,
                    Some(&k1),
                    Some("LStep"),
                    "accepted_distinct",
                )
                .unwrap();
            exporter
                .record_distinct(&k2, &s2, 1, false, Some(&k1), Some("LStep"))
                .unwrap();
            exporter.record_edge(&k1, &k2, "LStep", 1).unwrap();

            // Duplicate: generated only
            exporter
                .record_generated(&k1, &s1, 1, false, Some(&k2), Some("LStep"), "duplicate")
                .unwrap();

            exporter.flush().unwrap();
        }

        // Verify generated_states.jsonl
        let gen_content =
            std::fs::read_to_string(dir.path().join("generated_states.jsonl")).unwrap();
        let gen_lines: Vec<&str> = gen_content.trim().split('\n').collect();
        assert_eq!(
            gen_lines.len(),
            3,
            "3 generated records (1 init + 1 succ + 1 dup)"
        );

        let first: serde_json::Value = serde_json::from_str(gen_lines[0]).unwrap();
        assert_eq!(first["classification"], "accepted_distinct");
        assert_eq!(first["initial"], true);
        assert!(first["predecessor_state_id"].is_null());

        let dup: serde_json::Value = serde_json::from_str(gen_lines[2]).unwrap();
        assert_eq!(dup["classification"], "duplicate");
        assert!(!dup["predecessor_state_id"].is_null());

        // Verify distinct_states.jsonl
        let dist_content =
            std::fs::read_to_string(dir.path().join("distinct_states.jsonl")).unwrap();
        let dist_lines: Vec<&str> = dist_content.trim().split('\n').collect();
        assert_eq!(dist_lines.len(), 2, "2 distinct states");

        let second: serde_json::Value = serde_json::from_str(dist_lines[1]).unwrap();
        assert_eq!(second["initial"], false);
        assert_eq!(second["branch_label"], "LStep");

        // Verify edges.jsonl
        let edges_content = std::fs::read_to_string(dir.path().join("edges.jsonl")).unwrap();
        let edge_lines: Vec<&str> = edges_content.trim().split('\n').collect();
        assert_eq!(edge_lines.len(), 1, "1 edge");

        let edge: serde_json::Value = serde_json::from_str(edge_lines[0]).unwrap();
        assert_eq!(edge["branch_label"], "LStep");
        assert_eq!(edge["depth"], 1);
        assert_eq!(edge["src"], k1);
        assert_eq!(edge["dst"], k2);
    }
}
