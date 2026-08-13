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

use verus_transpiler::tla::{lint_module, needs_resolution, parse_module, resolve_module_file};

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus")
}

#[derive(Debug, Default, Clone)]
struct ManifestCase {
    id: String,
    tier: String,
    status: String,
    role: String,
    clean_distance: String,
    expected_rules: Vec<String>,
    rules_skipped: Vec<String>,
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
        } else if let Some(rest) = line.strip_prefix("status = ") {
            case.status = rest.trim().trim_matches('"').to_string();
        } else if let Some(rest) = line.strip_prefix("role = ") {
            case.role = rest.trim().trim_matches('"').to_string();
        } else if let Some(rest) = line.strip_prefix("clean_distance = ") {
            case.clean_distance = rest.trim().trim_matches('"').to_string();
        } else if let Some(rest) = line.strip_prefix("rules_skipped = ") {
            case.rules_skipped = rest
                .trim()
                .trim_start_matches('[')
                .trim_end_matches(']')
                .split(',')
                .map(|r| r.trim().trim_matches('"').to_string())
                .filter(|r| !r.is_empty())
                .collect();
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
        // A composed spec is measured as the module it denotes. Without this the
        // Jetpack composition lints at 2 with three rules silently not running,
        // which is the failure mode this pinning exists to catch.
        let module = if needs_resolution(&module) {
            resolve_module_file(&spec).unwrap_or_else(|e| panic!("{}: {e}", case.id))
        } else {
            module
        };
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

        // A rule that did not run cannot have found anything, so a low
        // clean_distance next to a non-empty skip list is a lower bound rather
        // than a near-clean spec. Pinning it keeps that distinction honest:
        // ReadersWriters reports 1 and Jetpack 2, both with C1/C2/C3 skipped.
        let skipped: BTreeSet<String> = report
            .skipped_rules
            .iter()
            .map(|(r, _)| r.as_str().to_string())
            .collect();
        let expected_skipped: BTreeSet<String> = case.rules_skipped.iter().cloned().collect();
        if skipped != expected_skipped {
            mismatches.push(format!(
                "{}: rules_skipped says {:?}, linter skipped {:?}",
                case.id, expected_skipped, skipped
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

/// A case's `role` says what it is *for*, and the two roles have opposite
/// obligations. Without this guard a `reject-only` case is indistinguishable
/// from a `translate` case somebody forgot to finish, which is exactly the
/// confusion the role was introduced to end.
#[test]
fn roles_match_what_the_cases_actually_contain() {
    let corpus = corpus_dir();
    let mut problems = Vec::new();
    let mut reject_only = 0;

    for case in manifest_cases() {
        let dir = corpus.join(format!("tier{}", case.tier)).join(&case.id);
        let role = if case.role.is_empty() {
            "translate"
        } else {
            &case.role
        };
        match role {
            "reject-only" => {
                reject_only += 1;
                // The point of a reject-only case is that it is never
                // rewritten. A clean.tla would mean somebody rewrote it
                // anyway, and the manifest would be lying about why it exists.
                for artefact in ["clean.tla", "golden.rs", "rewrite.md"] {
                    if dir.join(artefact).exists() {
                        problems.push(format!(
                            "{}: role is reject-only but it has a {artefact}",
                            case.id
                        ));
                    }
                }
                // The decision has to be written down where a reader looks for
                // it. Without this, "reject-only" reads as an excuse.
                if !dir.join("why_reject_only.md").exists() {
                    problems.push(format!(
                        "{}: role is reject-only but nothing says why -- write \
                         why_reject_only.md",
                        case.id
                    ));
                }
                if case.status != "intake" && case.status != "blocked" {
                    problems.push(format!(
                        "{}: role is reject-only, so its status should stay at \
                         intake (or blocked), not `{}`",
                        case.id, case.status
                    ));
                }
                if case.clean_distance == "unmeasured" {
                    problems.push(format!(
                        "{}: a reject-only case exists to be rejected, so its \
                         clean-distance has to be measured",
                        case.id
                    ));
                }
            }
            "translate" => {
                // `green` is the status that a milestone counts, so what it
                // asserts has to be on disk. V1 and V3 are guarded elsewhere
                // (the verus run and corpus_v3_guard); V2's evidence is the
                // case's declared observables, and without them the status is
                // claiming a comparison nobody ran.
                if case.status == "green" && !dir.join("observables.toml").exists() {
                    problems.push(format!(
                        "{}: status is green, but there is no observables.toml \
                         -- V2 cannot have been run",
                        case.id
                    ));
                }
                // A case is usually one `clean.tla`. A *composition* is
                // several modules -- tier4's Jetpack is two libraries and the
                // spec that INSTANCEs them -- and naming one of them
                // `clean.tla` would say the other two are not part of the
                // rewrite. So: at least one `*clean*.tla`, whatever it is
                // called.
                let clean_modules: Vec<String> = std::fs::read_dir(&dir)
                    .into_iter()
                    .flatten()
                    .flatten()
                    .filter_map(|e| {
                        let name = e.file_name().to_string_lossy().to_string();
                        (name.contains("clean") && name.ends_with(".tla")).then_some(name)
                    })
                    .collect();
                if dir.join("golden.rs").exists() && clean_modules.is_empty() {
                    problems.push(format!(
                        "{}: has a golden.rs but no clean-subset module to \
                         generate it from",
                        case.id
                    ));
                }
                if !clean_modules.is_empty() && !dir.join("rewrite.md").exists() {
                    problems.push(format!(
                        "{}: has {} clean-subset module(s) but no rewrite.md \
                         recording what the human decided",
                        case.id,
                        clean_modules.len()
                    ));
                }
            }
            other => problems.push(format!("{}: unknown role `{other}`", case.id)),
        }
    }

    assert!(
        reject_only > 0,
        "no case is reject-only, so this guard is checking nothing -- the \
         corpus is supposed to keep specimens the linter must reject"
    );
    assert!(
        problems.is_empty(),
        "corpus roles do not match the cases on disk:\n  {}",
        problems.join("\n  ")
    );
}
