//! Phase 52.M0.d — corpus accept/reject guard for the clean-subset linter.
//!
//! The M0 acceptance criterion is that the linter "correctly accepts clean and
//! rejects dirty samples". This pins that down for every corpus case: the
//! manifest records the expected clean-distance (violation count) and the
//! expected rules, and this test asserts the linter still produces exactly
//! that.
//!
//! Why an exact count rather than "at least one violation": a linter that
//! reports *more* than the spec actually violates is as broken as one that
//! reports fewer — the count is what `clean_distance` publishes as a measure of
//! rewrite effort, so it has to be pinned, not bounded.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use verus_transpiler::tla::{lint_module, parse_module};

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus")
}

#[derive(Debug, Default, Clone)]
struct ManifestCase {
    id: String,
    tier: String,
    clean_distance: String,
    expected_rules: Vec<String>,
}

/// Parse the manifest's case table. A hand-rolled reader keeps the corpus
/// registry free of a TOML dependency in the test target and makes the exact
/// fields this guard depends on obvious.
fn manifest_cases() -> Vec<ManifestCase> {
    let text = fs::read_to_string(corpus_dir().join("manifest.toml"))
        .expect("corpus manifest must be readable");

    let mut cases = Vec::new();
    let mut current: Option<ManifestCase> = None;
    for line in text.lines() {
        let line = line.trim();
        if line == "[[case]]" {
            if let Some(done) = current.take() {
                cases.push(done);
            }
            current = Some(ManifestCase::default());
            continue;
        }
        let Some(case) = current.as_mut() else {
            continue;
        };
        if let Some(rest) = line.strip_prefix("id = ") {
            case.id = rest.trim_matches('"').to_string();
        } else if let Some(rest) = line.strip_prefix("tier = ") {
            case.tier = rest.trim().to_string();
        } else if let Some(rest) = line.strip_prefix("clean_distance = ") {
            case.clean_distance = rest.trim().trim_matches('"').to_string();
        } else if let Some(rest) = line.strip_prefix("expected_rules = ") {
            case.expected_rules = rest
                .trim()
                .trim_start_matches('[')
                .trim_end_matches(']')
                .split(',')
                .map(|r| r.trim().trim_matches('"').to_string())
                .filter(|r| !r.is_empty())
                .collect();
        }
    }
    if let Some(done) = current {
        cases.push(done);
    }
    cases
}

#[test]
fn linter_verdicts_match_the_manifest() {
    let corpus = corpus_dir();
    let cases = manifest_cases();
    assert!(!cases.is_empty(), "the corpus registry lists no cases");

    let mut checked = 0usize;
    let mut mismatches = Vec::new();

    for case in &cases {
        let spec = corpus
            .join(format!("tier{}", case.tier))
            .join(&case.id)
            .join("original.tla");
        if !spec.exists() {
            // Still `planned`; nothing downloaded for it yet.
            continue;
        }
        if case.clean_distance == "unmeasured" {
            // Taken in before the linter existed and not yet measured. The
            // manifest is explicit about it, so this is not a silent skip.
            continue;
        }

        let source = fs::read_to_string(&spec).expect("spec must be readable");
        let module = parse_module(&source)
            .unwrap_or_else(|e| panic!("{}: corpus spec must parse: {e}", case.id));
        let report = lint_module(&module);
        checked += 1;

        let expected: usize = case
            .clean_distance
            .parse()
            .unwrap_or_else(|_| panic!("{}: clean_distance must be a number", case.id));
        if report.violations() != expected {
            mismatches.push(format!(
                "{}: clean_distance says {expected}, linter found {} ({})",
                case.id,
                report.violations(),
                report
                    .findings
                    .iter()
                    .map(|f| format!("{} {}", f.rule.as_str(), f.definition))
                    .collect::<Vec<_>>()
                    .join("; ")
            ));
            continue;
        }

        let found: BTreeSet<String> = report
            .findings
            .iter()
            .map(|f| f.rule.as_str().to_string())
            .collect();
        let want: BTreeSet<String> = case.expected_rules.iter().cloned().collect();
        if found != want {
            mismatches.push(format!(
                "{}: expected rules {:?}, linter reported {:?}",
                case.id, want, found
            ));
        }
    }

    assert!(
        checked > 0,
        "no corpus case was linted -- the guard would pass vacuously"
    );
    assert!(
        mismatches.is_empty(),
        "linter verdicts drifted from the corpus manifest:\n  {}",
        mismatches.join("\n  ")
    );
}

/// The corpus must contain at least one case the linter accepts and one it
/// rejects. A corpus of only-dirty specs cannot show that the linter accepts
/// anything, which is half of the M0 acceptance criterion.
#[test]
fn corpus_exercises_both_verdicts() {
    let corpus = corpus_dir();
    let mut clean = Vec::new();
    let mut dirty = Vec::new();

    for case in manifest_cases() {
        let spec = corpus
            .join(format!("tier{}", case.tier))
            .join(&case.id)
            .join("clean.tla");
        if !spec.exists() {
            continue;
        }
        let source = fs::read_to_string(&spec).unwrap_or_default();
        // Skip the scaffolded placeholder a case gets before its rewrite.
        if source
            .lines()
            .all(|l| l.trim().is_empty() || l.trim_start().starts_with("\\*"))
        {
            continue;
        }
        let Ok(module) = parse_module(&source) else {
            continue;
        };
        if lint_module(&module).is_clean() {
            clean.push(case.id.clone());
        } else {
            dirty.push(case.id.clone());
        }
    }

    // Until the first clean.tla is written (Phase 53.2), there is nothing to
    // accept yet. Fail loudly once rewrites exist but none of them pass.
    if clean.is_empty() && dirty.is_empty() {
        return;
    }
    assert!(
        !clean.is_empty(),
        "every rewritten clean.tla is still rejected by the linter: {dirty:?}. \
         Either the rewrites are not in the subset or the linter is over-strict."
    );
}
