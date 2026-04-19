//! DPOR explorer — builds execution traces from baseline export and
//! identifies backtrack points for future DPOR-guided exploration.
//!
//! This module uses the existing model checker's `--export-parity-debug`
//! output (generated_states.jsonl, distinct_states.jsonl, edges.jsonl)
//! to reconstruct the execution graph and compute backtrack sets.
//!
//! Architecture: Phase 38.8.1.c showed that key model-checker functions
//! (expand_type_domain_candidates, eval_spec_function_call_recursive) are
//! private to main.rs. Rather than a premature extraction, we leverage
//! the export infrastructure from Phase 36.1.7.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::process::Command;

use crate::modelcheck::dpor::types::*;

/// A loaded execution graph from the baseline's debug export.
#[derive(Debug)]
pub struct ExportedGraph {
    /// All distinct states (state_id → depth, initial flag)
    pub states: BTreeMap<String, StateInfo>,
    /// Edges: (src_id, dst_id) → branch_label
    pub edges: Vec<EdgeInfo>,
    /// Initial state IDs
    pub initial_states: Vec<String>,
}

/// Info about a distinct state from the export.
#[derive(Debug, Clone)]
pub struct StateInfo {
    pub state_id: String,
    pub depth: usize,
    pub initial: bool,
}

/// An edge in the exported graph.
#[derive(Debug, Clone)]
pub struct EdgeInfo {
    pub src: String,
    pub dst: String,
    pub branch_label: String,
    pub depth: usize,
}

/// Backtrack analysis result for one execution trace.
#[derive(Debug)]
pub struct BacktrackAnalysis {
    /// The trace (sequence of edges from initial state)
    pub trace: Vec<EdgeInfo>,
    /// At each trace index, the set of alternative successors that were available
    /// but not taken (backtrack candidates)
    pub backtrack_sets: Vec<BacktrackInfo>,
    /// Total number of backtrack points (positions with non-empty backtrack sets)
    pub total_backtrack_points: usize,
}

/// Run the baseline model checker with `--export-parity-debug` and parse the output.
pub fn run_baseline_with_export(
    transpiler_bin: &Path,
    spec_file: &Path,
    model_toml: &Path,
    invariants: &[String],
    export_dir: &Path,
) -> Result<ExportedGraph, String> {
    std::fs::create_dir_all(export_dir)
        .map_err(|e| format!("Failed to create export dir: {}", e))?;

    let mut cmd = Command::new(transpiler_bin);
    cmd.arg("model-check")
        .arg("--input")
        .arg(spec_file)
        .arg("--init")
        .arg("LInit")
        .arg("--next")
        .arg("LNext")
        .arg("--model")
        .arg(model_toml)
        .arg("--export-parity-debug")
        .arg(export_dir)
        .arg("--json-report");

    for inv in invariants {
        cmd.arg("--invariant").arg(inv);
    }

    let output = cmd
        .output()
        .map_err(|e| format!("Failed to run transpiler: {}", e))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        return Err(format!(
            "Baseline checker failed: {}{}",
            stdout.chars().take(200).collect::<String>(),
            stderr.chars().take(200).collect::<String>()
        ));
    }

    // Parse exported files
    parse_exported_graph(export_dir)
}

/// Parse the exported JSONL files into an ExportedGraph.
fn parse_exported_graph(export_dir: &Path) -> Result<ExportedGraph, String> {
    let distinct_path = export_dir.join("distinct_states.jsonl");
    let edges_path = export_dir.join("edges.jsonl");

    let mut states = BTreeMap::new();
    let mut initial_states = Vec::new();

    // Parse distinct states
    let content = std::fs::read_to_string(&distinct_path)
        .map_err(|e| format!("Failed to read distinct_states.jsonl: {}", e))?;
    for line in content.lines() {
        if line.trim().is_empty() {
            continue;
        }
        let entry: serde_json::Value =
            serde_json::from_str(line).map_err(|e| format!("JSON parse error: {}", e))?;

        let state_id = entry["state_id"].as_str().unwrap_or_default().to_string();
        let depth = entry["depth"].as_u64().unwrap_or(0) as usize;
        let initial = entry["initial"].as_bool().unwrap_or(false);

        if initial {
            initial_states.push(state_id.clone());
        }

        states.insert(
            state_id.clone(),
            StateInfo {
                state_id,
                depth,
                initial,
            },
        );
    }

    // Parse edges
    let mut edges = Vec::new();
    let edges_content = std::fs::read_to_string(&edges_path)
        .map_err(|e| format!("Failed to read edges.jsonl: {}", e))?;
    for line in edges_content.lines() {
        if line.trim().is_empty() {
            continue;
        }
        let entry: serde_json::Value =
            serde_json::from_str(line).map_err(|e| format!("JSON parse error: {}", e))?;

        edges.push(EdgeInfo {
            src: entry["src"].as_str().unwrap_or_default().to_string(),
            dst: entry["dst"].as_str().unwrap_or_default().to_string(),
            branch_label: entry["branch_label"]
                .as_str()
                .unwrap_or_default()
                .to_string(),
            depth: entry["depth"].as_u64().unwrap_or(0) as usize,
        });
    }

    Ok(ExportedGraph {
        states,
        edges,
        initial_states,
    })
}

/// Build an adjacency map from the exported graph.
/// Returns: state_id → Vec<(branch_label, dst_state_id)>
pub fn build_adjacency(graph: &ExportedGraph) -> BTreeMap<String, Vec<(String, String)>> {
    let mut adj: BTreeMap<String, Vec<(String, String)>> = BTreeMap::new();
    for edge in &graph.edges {
        adj.entry(edge.src.clone())
            .or_default()
            .push((edge.branch_label.clone(), edge.dst.clone()));
    }
    adj
}

/// Compute conservative backtrack sets for a single DFS trace through the graph.
///
/// This walks one path from the initial state and at each step records
/// which alternative successors were available but not taken.
/// v1: all alternatives are backtrack candidates (no independence filtering).
pub fn compute_backtrack_sets(graph: &ExportedGraph) -> BacktrackAnalysis {
    let adj = build_adjacency(graph);

    // Find a DFS path from the first initial state
    let initial = match graph.initial_states.first() {
        Some(s) => s.clone(),
        None => {
            return BacktrackAnalysis {
                trace: vec![],
                backtrack_sets: vec![],
                total_backtrack_points: 0,
            };
        }
    };

    let mut trace = Vec::new();
    let mut backtrack_sets = Vec::new();
    let mut visited = BTreeSet::new();
    visited.insert(initial.clone());

    let mut current = initial;
    loop {
        let successors = adj.get(&current).cloned().unwrap_or_default();
        if successors.is_empty() {
            break;
        }

        // Pick the first unvisited successor (deterministic DFS)
        let mut chosen = None;
        let mut alternatives = BTreeSet::new();

        for (branch, dst) in &successors {
            if !visited.contains(dst) {
                if chosen.is_none() {
                    chosen = Some((branch.clone(), dst.clone()));
                } else {
                    // This is an alternative we're not taking
                    alternatives.insert(ProcessId(0)); // v1: all alternatives as ProcessId(0)
                }
            }
        }

        match chosen {
            Some((branch, dst)) => {
                trace.push(EdgeInfo {
                    src: current.clone(),
                    dst: dst.clone(),
                    branch_label: branch,
                    depth: trace.len() + 1,
                });

                backtrack_sets.push(BacktrackInfo {
                    backtrack: alternatives,
                    done: {
                        let mut done = BTreeSet::new();
                        done.insert(ProcessId(0)); // The chosen process
                        done
                    },
                });

                visited.insert(dst.clone());
                current = dst;
            }
            None => break, // All successors already visited
        }
    }

    let total_backtrack_points = backtrack_sets
        .iter()
        .filter(|bs| !bs.backtrack.is_empty())
        .count();

    BacktrackAnalysis {
        trace,
        backtrack_sets,
        total_backtrack_points,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_exported_graph_empty() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("distinct_states.jsonl"), "").unwrap();
        std::fs::write(dir.path().join("edges.jsonl"), "").unwrap();

        let graph = parse_exported_graph(dir.path()).unwrap();
        assert!(graph.states.is_empty());
        assert!(graph.edges.is_empty());
        assert!(graph.initial_states.is_empty());
    }

    #[test]
    fn test_parse_exported_graph_simple() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(
            dir.path().join("distinct_states.jsonl"),
            r#"{"state_id":"s0","state":{},"depth":0,"initial":true}
{"state_id":"s1","state":{},"depth":1,"initial":false}
"#,
        )
        .unwrap();
        std::fs::write(
            dir.path().join("edges.jsonl"),
            r#"{"src":"s0","dst":"s1","branch_label":"LAdd","depth":1}
"#,
        )
        .unwrap();

        let graph = parse_exported_graph(dir.path()).unwrap();
        assert_eq!(graph.states.len(), 2);
        assert_eq!(graph.edges.len(), 1);
        assert_eq!(graph.initial_states, vec!["s0"]);
        assert_eq!(graph.edges[0].branch_label, "LAdd");
    }

    #[test]
    fn test_build_adjacency() {
        let graph = ExportedGraph {
            states: BTreeMap::new(),
            edges: vec![
                EdgeInfo {
                    src: "s0".to_string(),
                    dst: "s1".to_string(),
                    branch_label: "A".to_string(),
                    depth: 1,
                },
                EdgeInfo {
                    src: "s0".to_string(),
                    dst: "s2".to_string(),
                    branch_label: "B".to_string(),
                    depth: 1,
                },
                EdgeInfo {
                    src: "s1".to_string(),
                    dst: "s2".to_string(),
                    branch_label: "C".to_string(),
                    depth: 2,
                },
            ],
            initial_states: vec!["s0".to_string()],
        };

        let adj = build_adjacency(&graph);
        assert_eq!(adj.get("s0").unwrap().len(), 2);
        assert_eq!(adj.get("s1").unwrap().len(), 1);
        assert!(adj.get("s2").is_none());
    }

    #[test]
    fn test_backtrack_sets_linear() {
        // Linear graph: s0 → s1 → s2 (no alternatives → no backtrack points)
        let graph = ExportedGraph {
            states: [
                (
                    "s0".to_string(),
                    StateInfo {
                        state_id: "s0".to_string(),
                        depth: 0,
                        initial: true,
                    },
                ),
                (
                    "s1".to_string(),
                    StateInfo {
                        state_id: "s1".to_string(),
                        depth: 1,
                        initial: false,
                    },
                ),
                (
                    "s2".to_string(),
                    StateInfo {
                        state_id: "s2".to_string(),
                        depth: 2,
                        initial: false,
                    },
                ),
            ]
            .into_iter()
            .collect(),
            edges: vec![
                EdgeInfo {
                    src: "s0".to_string(),
                    dst: "s1".to_string(),
                    branch_label: "A".to_string(),
                    depth: 1,
                },
                EdgeInfo {
                    src: "s1".to_string(),
                    dst: "s2".to_string(),
                    branch_label: "A".to_string(),
                    depth: 2,
                },
            ],
            initial_states: vec!["s0".to_string()],
        };

        let analysis = compute_backtrack_sets(&graph);
        assert_eq!(analysis.trace.len(), 2);
        assert_eq!(analysis.total_backtrack_points, 0);
    }

    #[test]
    fn test_backtrack_sets_branching() {
        // Branching: s0 → s1 (via A) and s0 → s2 (via B)
        // At s0, choosing A means B is a backtrack candidate
        let graph = ExportedGraph {
            states: [
                (
                    "s0".to_string(),
                    StateInfo {
                        state_id: "s0".to_string(),
                        depth: 0,
                        initial: true,
                    },
                ),
                (
                    "s1".to_string(),
                    StateInfo {
                        state_id: "s1".to_string(),
                        depth: 1,
                        initial: false,
                    },
                ),
                (
                    "s2".to_string(),
                    StateInfo {
                        state_id: "s2".to_string(),
                        depth: 1,
                        initial: false,
                    },
                ),
            ]
            .into_iter()
            .collect(),
            edges: vec![
                EdgeInfo {
                    src: "s0".to_string(),
                    dst: "s1".to_string(),
                    branch_label: "A".to_string(),
                    depth: 1,
                },
                EdgeInfo {
                    src: "s0".to_string(),
                    dst: "s2".to_string(),
                    branch_label: "B".to_string(),
                    depth: 1,
                },
            ],
            initial_states: vec!["s0".to_string()],
        };

        let analysis = compute_backtrack_sets(&graph);
        assert_eq!(analysis.trace.len(), 1); // Only follows one path
        assert_eq!(analysis.total_backtrack_points, 1); // s0 has an alternative
        assert!(!analysis.backtrack_sets[0].backtrack.is_empty());
    }

    #[test]
    fn test_run_baseline_with_export_aplusb() {
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_file = manifest_dir.join("tests/tla-rs/01_aplusb/APlusB.rs");
        if !spec_file.exists() {
            eprintln!("Skipping: APlusB.rs not found (run regenerate_corpus.sh first)");
            return;
        }

        let transpiler = match crate::modelcheck::dpor::baseline::find_transpiler_bin() {
            Some(p) => p,
            None => {
                eprintln!("Skipping: transpiler binary not found");
                return;
            }
        };

        let tmp = tempfile::tempdir().unwrap();
        let model_path = crate::modelcheck::dpor::baseline::create_default_model_toml(tmp.path());
        let export_dir = tmp.path().join("export");

        let graph = run_baseline_with_export(
            &transpiler,
            &spec_file,
            &model_path,
            &["LSumInvariant".to_string()],
            &export_dir,
        );
        assert!(graph.is_ok(), "Failed: {:?}", graph.err());
        let graph = graph.unwrap();

        // APlusB: {a:0,b:0} → {a:1,b:1} → ... → {a:5,b:5} (bounded by int 0..5)
        assert!(!graph.states.is_empty(), "Should have states");
        assert_eq!(graph.initial_states.len(), 1, "Should have 1 initial state");
        assert!(!graph.edges.is_empty(), "Should have edges");

        // Backtrack analysis on APlusB (linear, 1 process → 0 backtrack points)
        let analysis = compute_backtrack_sets(&graph);
        assert_eq!(
            analysis.total_backtrack_points, 0,
            "APlusB is linear (1 process, 1 action) → 0 backtrack points"
        );
        eprintln!(
            "APlusB: {} states, {} edges, {} trace steps, {} backtrack points",
            graph.states.len(),
            graph.edges.len(),
            analysis.trace.len(),
            analysis.total_backtrack_points
        );
    }
}
