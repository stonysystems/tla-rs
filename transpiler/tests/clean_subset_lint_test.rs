//! Phase 52.M0 acceptance test: the clean-subset linter must accept the clean
//! reference fixture and reject the dirty ones with the documented codes.
//!
//! These fixtures double as the reference examples in
//! `docs/clean_tla_subset_spec.md`; keep them in sync with that document.

use std::collections::BTreeSet;
use std::path::PathBuf;

use verus_transpiler::tla::{
    lint_module, lint_module_with_config, parse_module, CleanSubsetConfig,
};

fn fixture(name: &str) -> String {
    let path: PathBuf = [
        env!("CARGO_MANIFEST_DIR"),
        "tests",
        "fixtures",
        "clean_subset",
        name,
    ]
    .iter()
    .collect();
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

fn codes(src: &str) -> BTreeSet<String> {
    let module = parse_module(src).expect("fixture must parse");
    lint_module(&module)
        .violations
        .iter()
        .map(|v| v.code.to_string())
        .collect()
}

#[test]
fn clean_fixture_is_accepted() {
    let src = fixture("CleanVoting.tla");
    let module = parse_module(&src).expect("fixture must parse");
    let report = lint_module(&module);
    assert!(
        report.is_clean(),
        "CleanVoting.tla must be clean:\n{}",
        report.render()
    );
    assert_eq!(report.node_set.as_deref(), Some("Node"));
    assert_eq!(report.network_var.as_deref(), Some("messages"));
    assert_eq!(report.clean_distance(), 0);
    // All five actions are recognised, including the receive-side ones.
    for action in [
        "RequestVote",
        "GrantVote",
        "CountVote",
        "BecomeLeader",
        "DropMessage",
    ] {
        assert!(report.actions.contains(action), "missing action {action}");
    }
}

#[test]
fn dirty_global_raft_fixture_is_rejected_with_expected_codes() {
    let found = codes(&fixture("DirtyGlobalRaft.tla"));
    for expected in [
        "CS001", // global scalar variable
        "CS003", // cross-node read
        "CS005", // history variable
        "CS006", // aggregation over the node set
        "CS009", // non-send network update
        "CS010", // message without src/dst
        "CS012", // Next disjunct with no node parameter
        "CS016", // whole-array write in an action
    ] {
        assert!(found.contains(expected), "expected {expected} in {found:?}");
    }
}

#[test]
fn shared_memory_fixture_is_rejected_for_having_no_network() {
    let found = codes(&fixture("SharedMemoryFlags.tla"));
    assert!(found.contains("CS007"), "{found:?}"); // no network variable
    assert!(found.contains("CS003"), "{found:?}"); // reads the peer's flag
    assert!(found.contains("CS001"), "{found:?}"); // global `turn`
}

#[test]
fn designating_the_network_variable_does_not_rescue_a_dirty_spec() {
    // C4 can be satisfied by fiat (`--network-var`), but C2/C3 cannot: the
    // cross-node reads survive, which is exactly the boundary the linter draws
    // between "translator's job" and "human rewrite".
    let src = fixture("SharedMemoryFlags.tla");
    let module = parse_module(&src).expect("fixture must parse");
    let config = CleanSubsetConfig {
        network_var: Some("turn".to_string()),
        ..CleanSubsetConfig::default()
    };
    let report = lint_module_with_config(&module, &config);
    assert!(!report.is_clean(), "{}", report.render());
    assert!(report.violations.iter().any(|v| v.code == "CS003"));
    assert!(!report.violations.iter().any(|v| v.code == "CS007"));
}

#[test]
fn every_violation_carries_an_actionable_hint() {
    for name in [
        "DirtyGlobalRaft.tla",
        "SharedMemoryFlags.tla",
        "CleanVoting.tla",
    ] {
        let src = fixture(name);
        let module = parse_module(&src).expect("fixture must parse");
        for v in lint_module(&module).violations {
            assert!(!v.message.trim().is_empty(), "{name}: empty message");
            assert!(!v.hint.trim().is_empty(), "{name}: {} has no hint", v.code);
            assert!(v.code.starts_with("CS"), "{name}: bad code {}", v.code);
            assert!(v.rule.starts_with('C'), "{name}: bad rule {}", v.rule);
        }
    }
}
