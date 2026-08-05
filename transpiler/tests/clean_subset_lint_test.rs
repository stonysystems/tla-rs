//! Phase 52.M0 acceptance test: the clean-subset linter must accept the clean
//! reference fixture and reject the dirty ones.
//!
//! **These fixtures and this test came from a parallel, independent
//! implementation of Phase 52.M0** (origin/main commit `b6245c76`), merged in
//! alongside ours. That implementation's linter did not survive the merge --
//! it was API-incompatible with the projection stack built on top of ours, and
//! its frontend could not parse any of the eight `clean.tla` rewrites in
//! `tests/corpus/`. The fixtures and their intent did survive, and they earned
//! their place immediately: `CleanVoting.tla` exposed a real defect in **our**
//! C5, which rejected `\E m \in messages : DropMessage(m)` -- message loss, an
//! environment action our own contract has always permitted. Our corpus has no
//! lossy network, so nothing had ever exercised the shape.
//!
//! Ported to our API. Three assertions from the original could not be carried
//! over, and it is worth saying which rather than quietly dropping them:
//!
//! - **`CS001`-style diagnostic codes.** Ours reports a rule (`C1`..`C5`) and a
//!   prose message; it has no stable per-diagnostic code. The rule-level
//!   assertions below are correspondingly weaker.
//! - **A separate `hint` field.** Ours puts the guidance in the message itself,
//!   so "every violation carries an actionable hint" becomes "every message is
//!   non-empty and long enough to say what the human has to decide".
//! - **`--network-var` designation by fiat.** Ours infers the network and has no
//!   override, so the original's "designating the network does not rescue a
//!   dirty spec" test has nothing to drive. The *claim* it made still holds and
//!   is covered by `shared_memory_fixture_is_rejected`: C2's cross-node reads
//!   survive whatever C4 concludes.

use std::collections::BTreeSet;
use std::path::PathBuf;

use verus_transpiler::tla::{lint_module, parse_module, CleanRule};

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

fn rules(src: &str) -> BTreeSet<CleanRule> {
    let module = parse_module(src).expect("fixture must parse");
    lint_module(&module)
        .findings
        .iter()
        .map(|f| f.rule)
        .collect()
}

#[test]
fn clean_fixture_is_accepted() {
    let src = fixture("CleanVoting.tla");
    let module = parse_module(&src).expect("fixture must parse");
    let report = lint_module(&module);
    assert!(
        report.is_clean(),
        "CleanVoting.tla must be clean, got {:?}",
        report.findings
    );
    assert_eq!(report.node_set.as_deref(), Some("Node"));
    assert_eq!(report.network_variable.as_deref(), Some("messages"));
    assert_eq!(report.violations(), 0);
}

#[test]
fn the_clean_fixture_keeps_its_environment_action() {
    // The reason this fixture is worth keeping. `DropMessage` is performed by
    // the framework, not by a node, and C5 must not demand a node binder for
    // it. Our linter used to, and nothing in our own corpus caught it.
    let src = fixture("CleanVoting.tla");
    assert!(
        src.contains("DropMessage(m)"),
        "the fixture no longer contains the environment action this test is about"
    );
    let module = parse_module(&src).expect("fixture must parse");
    let report = lint_module(&module);
    assert!(
        !report
            .findings
            .iter()
            .any(|f| f.rule == CleanRule::C5 && f.message.contains("DropMessage")),
        "C5 rejected an environment action: {:?}",
        report.findings
    );
}

#[test]
fn dirty_global_raft_fixture_is_rejected() {
    let found = rules(&fixture("DirtyGlobalRaft.tla"));
    for expected in [
        CleanRule::C1, // `elections`, `leaderCount`, `messages` are global
        CleanRule::C2, // AppendEntries reads currentTerm[j]
        CleanRule::C4, // `messages` is a queue array, not a message set
    ] {
        assert!(
            found.contains(&expected),
            "expected {expected:?} in {found:?}"
        );
    }

    // The original asserted C3 here too (its CS005 "history variable" and
    // CS006 "aggregation over the node set"). Ours does not report C3 on this
    // fixture, and after checking the spec that looks like the better verdict
    // rather than a gap:
    //
    // - `AllLogs == { log[i] : i \in Server }` is the aggregation their CS006
    //   fires on, but it is a *definition* that nothing in the module uses. An
    //   unused definition is not state, so it cannot be a history variable; if
    //   an action did use it, that read of every node's `log` is what C2 exists
    //   to catch.
    // - `elections' = elections \cup {[eterm |-> currentTerm[i]]}` appends one
    //   record built from the acting node's own state. That is not an
    //   aggregation over `Server`, which is the signal our C3 looks for -- and
    //   `elections` is rejected anyway, by C1, for the more fundamental reason
    //   that it is global.
    //
    // Recorded rather than "fixed": the two implementations genuinely disagree
    // about whether a syntactic aggregation in dead code is worth a finding.
    assert!(
        !found.contains(&CleanRule::C3),
        "if C3 now fires here, revisit the reasoning above: {found:?}"
    );
}

#[test]
fn shared_memory_fixture_is_rejected() {
    // A spec with no per-node state at all has no projection, and a spec that
    // reads its peer's flag violates C2 whatever is decided about the network.
    let found = rules(&fixture("SharedMemoryFlags.tla"));
    assert!(!found.is_empty(), "SharedMemoryFlags.tla must be rejected");
    assert!(
        found.contains(&CleanRule::C1) || found.contains(&CleanRule::C2),
        "expected a C1 or C2 finding, got {found:?}"
    );
}

#[test]
fn every_finding_says_what_the_human_has_to_decide() {
    for name in [
        "DirtyGlobalRaft.tla",
        "SharedMemoryFlags.tla",
        "CleanVoting.tla",
    ] {
        let src = fixture(name);
        let module = parse_module(&src).expect("fixture must parse");
        for f in lint_module(&module).findings {
            assert!(!f.message.trim().is_empty(), "{name}: empty message");
            // The contract for a finding is that it names the construct and
            // says what to do, not merely that something is unsupported.
            assert!(
                f.message.len() > 40,
                "{name}: {:?} message is too terse to act on: {}",
                f.rule,
                f.message
            );
        }
    }
}
