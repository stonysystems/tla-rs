//! Regression tests for cross-engine parity state exports (Phase 36.1.6).
//!
//! These tests validate the checked-in parity JSONL exports under
//! `reports/model_check/parity/` to catch regressions in:
//! - Source-first state count changes
//! - TLC state count changes
//! - Parity overlap changes
//!
//! The expected counts are baseline values from the initial export run.
//! When the model checker is improved, update the expected values here.

use std::collections::BTreeSet;
use std::path::PathBuf;
use std::process::Command;

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..")
}

fn load_state_ids(path: &std::path::Path) -> Vec<String> {
    let content = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", path.display(), e));
    content
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            let entry: serde_json::Value = serde_json::from_str(line)
                .unwrap_or_else(|e| panic!("Failed to parse JSONL line: {}", e));
            // Use canonical state JSON as ID for comparison
            serde_json::to_string(&entry["state"]).unwrap()
        })
        .collect()
}

fn load_initial_state_ids(path: &std::path::Path) -> BTreeSet<String> {
    let content = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", path.display(), e));
    content
        .lines()
        .filter(|line| !line.trim().is_empty())
        .filter_map(|line| {
            let entry: serde_json::Value = serde_json::from_str(line).ok()?;
            if entry["initial"].as_bool().unwrap_or(false) {
                Some(serde_json::to_string(&entry["state"]).unwrap())
            } else {
                None
            }
        })
        .collect()
}

fn count_distinct(ids: &[String]) -> usize {
    ids.iter().collect::<BTreeSet<_>>().len()
}

fn count_shared(left: &[String], right: &[String]) -> usize {
    let left_set: BTreeSet<_> = left.iter().collect();
    let right_set: BTreeSet<_> = right.iter().collect();
    left_set.intersection(&right_set).count()
}

// =========================================================================
// TwoPhase parity regression
// =========================================================================

#[test]
fn test_parity_twophase_source_first_state_count() {
    let path = repo_root().join("reports/model_check/parity/source_first/twophase/states.jsonl");
    let ids = load_state_ids(&path);
    let distinct = count_distinct(&ids);
    // After Phase 36.2.3 fix (PreparedVote added to enum domain): 37 states
    // (up from 8 when PreparedVote was missing). Source-first finds more
    // states than TLC (56) because it doesn't model message channels.
    assert_eq!(
        distinct, 37,
        "TwoPhase source-first distinct state count changed (expected 37, got {})",
        distinct
    );
}

#[test]
fn test_parity_twophase_tlc_state_count() {
    let path = repo_root().join("reports/model_check/parity/tlc/twophase/states.jsonl");
    let ids = load_state_ids(&path);
    let distinct = count_distinct(&ids);
    assert_eq!(
        distinct, 56,
        "TwoPhase TLC projected distinct state count changed (expected 56, got {})",
        distinct
    );
}

#[test]
fn test_parity_twophase_overlap() {
    let sf_path = repo_root().join("reports/model_check/parity/source_first/twophase/states.jsonl");
    let tlc_path = repo_root().join("reports/model_check/parity/tlc/twophase/states.jsonl");
    let sf_ids = load_state_ids(&sf_path);
    let tlc_ids = load_state_ids(&tlc_path);
    let shared = count_shared(&sf_ids, &tlc_ids);
    // After Phase 36.2.3: 23 shared states (up from 8).
    // Source-first has 14 states not in TLC (message-free over-approximation).
    // TLC has 33 states not in source-first (message-channel reachable states).
    // The remaining gap is a modeling difference (message channels), not a bug.
    assert_eq!(
        shared, 23,
        "TwoPhase shared state count changed (expected 23, got {})",
        shared
    );
}

#[test]
fn test_parity_twophase_initial_states_match() {
    let sf_path = repo_root().join("reports/model_check/parity/source_first/twophase/states.jsonl");
    let tlc_path = repo_root().join("reports/model_check/parity/tlc/twophase/states.jsonl");
    let sf_init = load_initial_state_ids(&sf_path);
    let tlc_init = load_initial_state_ids(&tlc_path);
    assert_eq!(sf_init.len(), 1, "Expected 1 source-first initial state");
    assert_eq!(tlc_init.len(), 1, "Expected 1 TLC initial state");
    assert_eq!(
        sf_init, tlc_init,
        "TwoPhase initial states should match between engines"
    );
}

// =========================================================================
// PrimaryBackup parity regression
// =========================================================================

#[test]
fn test_parity_primarybackup_source_first_state_count() {
    let path =
        repo_root().join("reports/model_check/parity/source_first/primarybackup/states.jsonl");
    // Post Phase 36.3.4: PB finds 37,213 states (17MB), too large to check in.
    // Skip if export not present.
    if !path.exists() {
        eprintln!("PB source-first export not present (too large to check in), skipping");
        return;
    }
    let ids = load_state_ids(&path);
    let distinct = count_distinct(&ids);
    assert!(
        distinct >= 37213,
        "PrimaryBackup source-first should find at least 37,213 states (got {})",
        distinct
    );
}

#[test]
fn test_parity_primarybackup_tlc_state_count() {
    let path = repo_root().join("reports/model_check/parity/tlc/primarybackup/states.jsonl");
    let ids = load_state_ids(&path);
    let distinct = count_distinct(&ids);
    // After Phase 36.2.4: 42 projected states (down from 54) after
    // excluding the wrapper-only `phase` field.
    assert_eq!(
        distinct, 42,
        "PrimaryBackup TLC projected distinct state count changed (expected 42, got {})",
        distinct
    );
}

#[test]
fn test_parity_primarybackup_overlap() {
    let sf_path =
        repo_root().join("reports/model_check/parity/source_first/primarybackup/states.jsonl");
    if !sf_path.exists() {
        eprintln!("PB source-first export not present (too large to check in), skipping");
        return;
    }
    let tlc_path = repo_root().join("reports/model_check/parity/tlc/primarybackup/states.jsonl");
    let sf_ids = load_state_ids(&sf_path);
    let tlc_ids = load_state_ids(&tlc_path);
    let shared = count_shared(&sf_ids, &tlc_ids);
    // Post Phase 36.3.4: 27 shared (up from 18). SF over-approximates
    // massively (37K states) without message channels.
    assert!(
        shared >= 27,
        "PrimaryBackup shared count should be at least 27 (got {})",
        shared
    );
}

// =========================================================================
// LeaderElection parity regression (partial — source-first times out)
// =========================================================================

#[test]
fn test_parity_leaderelection_source_first_partial() {
    let path =
        repo_root().join("reports/model_check/parity/source_first/leaderelection/states.jsonl");
    let ids = load_state_ids(&path);
    let distinct = count_distinct(&ids);
    // Post Phase 36.3.4: 31 states (up from 2). All are strict subset of TLC.
    assert!(
        distinct >= 31,
        "LeaderElection source-first should find at least 31 states (got {})",
        distinct
    );
}

#[test]
fn test_parity_leaderelection_tlc_state_count() {
    let path = repo_root().join("reports/model_check/parity/tlc/leaderelection/states.jsonl");
    let ids = load_state_ids(&path);
    let distinct = count_distinct(&ids);
    assert_eq!(
        distinct, 913,
        "LeaderElection TLC projected distinct state count changed (expected 913, got {})",
        distinct
    );
}

#[test]
fn test_parity_leaderelection_overlap() {
    let sf_path =
        repo_root().join("reports/model_check/parity/source_first/leaderelection/states.jsonl");
    let tlc_path = repo_root().join("reports/model_check/parity/tlc/leaderelection/states.jsonl");
    let sf_ids = load_state_ids(&sf_path);
    let tlc_ids = load_state_ids(&tlc_path);
    let shared = count_shared(&sf_ids, &tlc_ids);
    // Post Phase 36.3.4: all 31 SF states are in TLC (strict subset)
    assert!(
        shared >= 31,
        "LeaderElection shared count should be at least 31 (got {})",
        shared
    );
}

// =========================================================================
// Bug repro: TwoPhase LRMReceivePrepare produces 0 successors (Phase 36.2.2)
//
// The source-first solver fails to produce successors for branches with
// enum variants that have fields (e.g., PreparedVote{rm}). This test
// runs the model checker on a minimal 1-RM config and checks the state
// count. When the bug is fixed, state count should be >4.
// =========================================================================

#[test]
fn test_twophase_prepare_branch_produces_successors() {
    let root = repo_root();
    let binary = root.join("transpiler/target/debug/verus-transpile");

    // Build if needed
    let build = Command::new("cargo")
        .args(["build", "--bin", "verus-transpile"])
        .current_dir(root.join("transpiler"))
        .output()
        .expect("Failed to run cargo build");
    assert!(
        build.status.success(),
        "cargo build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );

    let output = Command::new(&binary)
        .args([
            "model-check",
            "--input",
            "src/protocol/TwoPhase/twophase.rs",
            "--types",
            "src/protocol/TwoPhase/types.rs",
            "--model",
            "transpiler/tests/model_check_fixtures/twophase_parity_bug_repro.model.toml",
            "--json-report",
        ])
        .current_dir(&root)
        .output()
        .expect("Failed to run model-check");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let report: serde_json::Value = serde_json::from_str(&stdout)
        .unwrap_or_else(|e| panic!("Failed to parse JSON report: {}. stdout: {}", e, stdout));

    let states = report["summary"]["states"].as_u64().unwrap_or(0);
    let branch_telemetry = report["summary"]["branch_telemetry"].as_array().unwrap();

    // Find LRMReceivePrepare branch (branch_1 — second branch in LNext)
    // It should have successful_successors > 0 when the bug is fixed.
    let branch1_successors: u64 = branch_telemetry
        .get(1)
        .and_then(|b| b["successful_successors"].as_u64())
        .unwrap_or(0);

    // FIX VERIFIED (Phase 36.2.3): PreparedVote was missing from
    // enum_subset in model config. After adding it, branch_1 produces
    // successors and the prepare/commit paths are explored.
    assert!(
        branch1_successors > 0,
        "LRMReceivePrepare should produce successors (got {})",
        branch1_successors
    );
    assert!(
        states > 4,
        "Should find prepare/commit paths with PreparedVote in enum domain (got {})",
        states
    );
}

// =========================================================================
// Paxos parity regression (small 2-node fixture, Phase 36.2.5.c)
// =========================================================================

#[test]
fn test_parity_paxos_small_source_first_state_count() {
    let path = repo_root().join("reports/model_check/parity/source_first/paxos/states.jsonl");
    let ids = load_state_ids(&path);
    let distinct = count_distinct(&ids);
    // Phase 36.2.5.c: 2-node Paxos (quorum=1, int 0..1) exhausts at 570 states.
    assert_eq!(
        distinct, 570,
        "Paxos small source-first distinct state count changed (expected 570, got {})",
        distinct
    );
}

#[test]
fn test_parity_paxos_small_initial_state() {
    let path = repo_root().join("reports/model_check/parity/source_first/paxos/states.jsonl");
    let initial = load_initial_state_ids(&path);
    assert_eq!(
        initial.len(),
        1,
        "Paxos small should have exactly 1 initial state (got {})",
        initial.len()
    );
}

// =========================================================================
// LeaderElection performance reproducer regression (Phase 36.2.5.b)
// =========================================================================

#[test]
fn test_parity_leaderelection_perf_repro_exists() {
    let path = repo_root()
        .join("transpiler/tests/model_check_fixtures/leaderelection_perf_repro.model.toml");
    assert!(
        path.exists(),
        "LeaderElection 2-node performance reproducer fixture should exist"
    );
}
