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

use verus_transpiler::tla::{parse_module, project, project_module, ProjectionError};

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

/// Field name -> declared type, read out of a named `pub struct` in the golden.
fn golden_struct_fields(golden: &str, struct_name: &str) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    let Some(start) = golden.find(&format!("pub struct {struct_name} {{")) else {
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

/// Variant name -> payload field names, read out of the golden's `LMessage`.
fn golden_message_variants(golden: &str) -> BTreeMap<String, Vec<String>> {
    let mut out = BTreeMap::new();
    let Some(start) = golden.find("pub enum LMessage {") else {
        return out;
    };
    let body = &golden[start..];
    let Some(end) = body.find("\n    }") else {
        return out;
    };
    for line in body[..end].lines().skip(1) {
        let line = line.trim().trim_end_matches(',');
        if line.is_empty() || line.starts_with("//") {
            continue;
        }
        let (name, fields) = match line.split_once('{') {
            Some((name, rest)) => {
                let fields = rest
                    .trim_end_matches('}')
                    .split(',')
                    .filter_map(|f| f.split_once(':').map(|(n, _)| n.trim().to_string()))
                    .filter(|f| !f.is_empty())
                    .collect();
                (name.trim().to_string(), fields)
            }
            None => (line.to_string(), Vec::new()),
        };
        out.insert(name, fields);
    }
    out
}

#[test]
fn projected_constants_and_messages_match_the_goldens() {
    let corpus = corpus_dir();
    let mut checked = 0usize;
    let mut mismatches = Vec::new();

    for tier in ["tier0", "tier1", "tier2", "tier3"] {
        let Ok(entries) = fs::read_dir(corpus.join(tier)) else {
            continue;
        };
        for entry in entries.flatten() {
            let case = entry.path();
            let (clean, golden_path) = (case.join("clean.tla"), case.join("golden.rs"));
            if !clean.exists() || !golden_path.exists() {
                continue;
            }
            let case_id = case.file_name().unwrap().to_string_lossy().to_string();
            let module = parse_module(&fs::read_to_string(&clean).unwrap())
                .unwrap_or_else(|e| panic!("{case_id}: {e}"));
            let spec = match project(&module) {
                Ok(projected) => projected.spec,
                Err(ProjectionError::NotClean(_)) => panic!("{case_id}: must be clean"),
            };
            let golden = fs::read_to_string(&golden_path).unwrap();
            checked += 1;

            // Constants: names and types, which is where a pluralised or
            // otherwise invented name would show up.
            let want = golden_struct_fields(&golden, "LConstants");
            for (name, ty) in &spec.constants {
                match want.get(name) {
                    Some(w) if *w == ty.render() => {}
                    Some(w) => mismatches.push(format!(
                        "{case_id}: constant `{name}` golden `{w}` vs projected `{}`",
                        ty.render()
                    )),
                    None => mismatches.push(format!(
                        "{case_id}: constant `{name}` is projected but absent from the \
                         golden's LConstants ({:?})",
                        want.keys().collect::<Vec<_>>()
                    )),
                }
            }

            // Message variants and their payloads.
            let want_msgs = golden_message_variants(&golden);
            for variant in &spec.messages {
                let names: Vec<String> = variant.fields.iter().map(|(n, _)| n.clone()).collect();
                match want_msgs.get(&variant.name) {
                    Some(w) if *w == names => {}
                    Some(w) => mismatches.push(format!(
                        "{case_id}: message `{}` golden payload {w:?} vs projected {names:?}",
                        variant.name
                    )),
                    None => mismatches.push(format!(
                        "{case_id}: message `{}` is projected but absent from the golden \
                         ({:?})",
                        variant.name,
                        want_msgs.keys().collect::<Vec<_>>()
                    )),
                }
            }
        }
    }

    assert!(
        checked > 0,
        "no case checked -- the guard would pass vacuously"
    );
    assert!(
        mismatches.is_empty(),
        "projection disagrees with the goldens:\n  {}",
        mismatches.join("\n  ")
    );
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
