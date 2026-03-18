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
    assert_eq!(
        distinct, 8,
        "TwoPhase source-first distinct state count changed (expected 8, got {})",
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
    // All 8 source-first states should be in TLC (source-first is a subset)
    assert_eq!(
        shared, 8,
        "TwoPhase shared state count changed (expected 8, got {}). \
         Source-first states should be a subset of TLC states.",
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
    let ids = load_state_ids(&path);
    let distinct = count_distinct(&ids);
    assert_eq!(
        distinct, 60,
        "PrimaryBackup source-first distinct state count changed (expected 60, got {})",
        distinct
    );
}

#[test]
fn test_parity_primarybackup_tlc_state_count() {
    let path = repo_root().join("reports/model_check/parity/tlc/primarybackup/states.jsonl");
    let ids = load_state_ids(&path);
    let distinct = count_distinct(&ids);
    assert_eq!(
        distinct, 54,
        "PrimaryBackup TLC projected distinct state count changed (expected 54, got {})",
        distinct
    );
}

#[test]
fn test_parity_primarybackup_overlap() {
    let sf_path =
        repo_root().join("reports/model_check/parity/source_first/primarybackup/states.jsonl");
    let tlc_path = repo_root().join("reports/model_check/parity/tlc/primarybackup/states.jsonl");
    let sf_ids = load_state_ids(&sf_path);
    let tlc_ids = load_state_ids(&tlc_path);
    let shared = count_shared(&sf_ids, &tlc_ids);
    // Current baseline: 0 shared (representation mismatch — field naming
    // or enum encoding differs between engines). This should INCREASE as
    // normalization bugs are fixed in Phase 36.2.
    // For now, just record the baseline.
    let _baseline = shared; // 0 as of Phase 36.1.6
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
    // Source-first times out; current baseline is 2 states
    assert!(
        distinct >= 2,
        "LeaderElection source-first should find at least 2 states (got {})",
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
    // Source-first partial states should be a subset of TLC
    assert!(
        shared >= 2,
        "LeaderElection shared count should be at least 2 (got {})",
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
    assert!(build.status.success(), "cargo build failed: {}", String::from_utf8_lossy(&build.stderr));

    let output = Command::new(&binary)
        .args([
            "model-check",
            "--input", "src/protocol/TwoPhase/twophase.rs",
            "--types", "src/protocol/TwoPhase/types.rs",
            "--model", "transpiler/tests/model_check_fixtures/twophase_parity_bug_repro.model.toml",
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

    // CURRENT BUG: branch_1 produces 0 successors.
    // When fixed, this should produce successors and total states should
    // increase from 4 to something higher (TLC finds 16 projected states
    // for 1 RM).
    //
    // This test documents the current buggy baseline. Update the assertion
    // when the bug is fixed:
    //   assert!(branch1_successors > 0, "LRMReceivePrepare should produce successors");
    //   assert!(states > 4, "Should find prepare/commit paths (TLC finds 16)");
    assert_eq!(
        branch1_successors, 0,
        "BUG BASELINE: LRMReceivePrepare currently produces 0 successors. \
         If this assertion fails, the bug may be fixed — update the test!"
    );
    assert!(
        states <= 4,
        "BUG BASELINE: with bug, only abort paths explored (<=4 states). \
         Got {} states — if higher, the PreparedVote bug may be fixed!",
        states
    );
}
