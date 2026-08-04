//! Phase 52.M1 — the projection pass checked against the corpus goldens.
//!
//! The goldens (`tests/corpus/*/golden.rs`) are the frozen statement of what
//! the translator must emit. This test holds the projection's *type* decisions
//! against them: for every `clean.tla` that has a golden, each projected state
//! field must have the type the golden declares.
//!
//! Reading the golden rather than restating the expected types here is
//! deliberate. A copy would drift, and the golden is the artifact under review.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use verus_transpiler::tla::{parse_module, project_module, ProjectionError};

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus")
}

/// Field name -> declared type, read out of the golden's `pub struct LState`.
fn golden_state_fields(golden: &str) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    let Some(start) = golden.find("pub struct LState {") else {
        return out;
    };
    let body = &golden[start..];
    let Some(end) = body.find("\n    }") else {
        return out;
    };
    for line in body[..end].lines().skip(1) {
        let line = line.trim();
        let Some(rest) = line.strip_prefix("pub ") else {
            continue;
        };
        let Some((name, ty)) = rest.trim_end_matches(',').split_once(':') else {
            continue;
        };
        out.insert(name.trim().to_string(), ty.trim().to_string());
    }
    out
}

#[test]
fn projected_state_types_match_the_goldens() {
    let corpus = corpus_dir();
    let mut checked = 0usize;
    let mut mismatches = Vec::new();

    for tier in ["tier0", "tier1", "tier2", "tier3"] {
        let tier_dir = corpus.join(tier);
        let Ok(entries) = fs::read_dir(&tier_dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let case = entry.path();
            let (clean, golden) = (case.join("clean.tla"), case.join("golden.rs"));
            if !clean.exists() || !golden.exists() {
                continue;
            }

            let case_id = case.file_name().unwrap().to_string_lossy().to_string();
            let source = fs::read_to_string(&clean).expect("clean.tla must be readable");
            let module = parse_module(&source)
                .unwrap_or_else(|e| panic!("{case_id}: clean.tla must parse: {e}"));
            let spec = match project_module(&module) {
                Ok(spec) => spec,
                Err(ProjectionError::NotClean(report)) => panic!(
                    "{case_id}: a case with a golden must be clean, got {:?}",
                    report.findings
                ),
            };

            let expected = golden_state_fields(
                &fs::read_to_string(&golden).expect("golden.rs must be readable"),
            );
            assert!(
                !expected.is_empty(),
                "{case_id}: could not read LState out of the golden"
            );
            checked += 1;

            for field in &spec.state_fields {
                match expected.get(&field.name) {
                    Some(want) if *want == field.ty.render() => {}
                    Some(want) => mismatches.push(format!(
                        "{case_id}.{}: golden says `{want}`, projection says `{}`",
                        field.name,
                        field.ty.render()
                    )),
                    None => mismatches.push(format!(
                        "{case_id}.{}: projected but absent from the golden's LState \
                         (golden has {:?})",
                        field.name,
                        expected.keys().collect::<Vec<_>>()
                    )),
                }
            }
            for name in expected.keys() {
                if !spec.state_fields.iter().any(|f| &f.name == name) {
                    mismatches.push(format!(
                        "{case_id}.{name}: in the golden's LState but not projected"
                    ));
                }
            }
            assert!(
                spec.gaps.is_empty(),
                "{case_id}: projection reported gaps: {:?}",
                spec.gaps
            );
        }
    }

    assert!(
        checked > 0,
        "no case had both a clean.tla and a golden.rs -- the guard would pass vacuously"
    );
    assert!(
        mismatches.is_empty(),
        "projection disagrees with the goldens:\n  {}",
        mismatches.join("\n  ")
    );
}
