//! Phase 52.M0.0.d — corpus parse guard.
//!
//! Every `original.tla` and `clean.tla` in `tests/corpus/` must parse with the
//! tla-rs TLA+ frontend. This is the regression guard for the Phase 52.M0.0
//! frontend work: when the corpus was first taken in (Phase 53.2), 0 of 5
//! tier-0 originals parsed, and the linter and projection passes are
//! meaningless until they do.
//!
//! The manifest records the expected status per case. A case whose spec cannot
//! be parsed is marked `parse_status = "unparseable"` there with a reason, and
//! this test asserts the manifest and reality agree in both directions — so a
//! newly-fixed case cannot silently stay marked broken, and a newly-broken case
//! cannot slip through.

use std::fs;
use std::path::{Path, PathBuf};

use verus_transpiler::tla::parse_module;

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus")
}

/// Case id -> `parse_status` from the manifest. Absent means "must parse".
fn manifest_parse_status() -> Vec<(String, String)> {
    let text = fs::read_to_string(corpus_dir().join("manifest.toml"))
        .expect("corpus manifest must be readable");

    let mut out = Vec::new();
    let mut id: Option<String> = None;
    let mut status = String::from("parses");
    for line in text.lines() {
        let line = line.trim();
        if line == "[[case]]" {
            if let Some(prev) = id.take() {
                out.push((prev, std::mem::replace(&mut status, "parses".into())));
            }
        } else if let Some(rest) = line.strip_prefix("id = ") {
            id = Some(rest.trim_matches('"').to_string());
        } else if let Some(rest) = line.strip_prefix("parse_status = ") {
            status = rest.trim_matches('"').to_string();
        }
    }
    if let Some(last) = id {
        out.push((last, status));
    }
    out
}

/// Every spec file a case owns that is expected to be parseable.
fn spec_files(case_dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    for name in ["original.tla", "clean.tla"] {
        let path = case_dir.join(name);
        if !path.exists() {
            continue;
        }
        // A scaffolded-but-unwritten clean.tla is a comment-only placeholder;
        // it carries no spec to parse yet.
        let text = fs::read_to_string(&path).unwrap_or_default();
        if text
            .lines()
            .all(|l| l.trim().is_empty() || l.trim_start().starts_with("\\*"))
        {
            continue;
        }
        files.push(path);
    }
    files
}

#[test]
fn corpus_specs_parse_as_the_manifest_claims() {
    let corpus = corpus_dir();
    if !corpus.exists() {
        panic!("corpus directory missing at {}", corpus.display());
    }

    let expected = manifest_parse_status();
    assert!(
        !expected.is_empty(),
        "the manifest lists no cases; the corpus registry is the source of truth"
    );

    let mut checked = 0usize;
    let mut wrongly_marked_broken = Vec::new();
    let mut newly_broken = Vec::new();

    for (id, status) in &expected {
        let tier = id
            .split('_')
            .next()
            .and_then(|t| t.strip_prefix('t'))
            .unwrap_or("0");
        let case_dir = corpus.join(format!("tier{tier}")).join(id);
        if !case_dir.exists() {
            // Still `planned`: nothing has been downloaded for it yet.
            continue;
        }

        for file in spec_files(&case_dir) {
            let source = fs::read_to_string(&file).expect("spec file must be readable");
            let result = parse_module(&source);
            let rel = file
                .strip_prefix(&corpus)
                .unwrap_or(&file)
                .display()
                .to_string();
            checked += 1;

            match (status.as_str(), result) {
                ("unparseable", Ok(_)) => wrongly_marked_broken.push(rel),
                ("unparseable", Err(_)) => {}
                (_, Err(e)) => newly_broken.push(format!("{rel}: {e}")),
                (_, Ok(_)) => {}
            }
        }
    }

    assert!(
        checked > 0,
        "no corpus spec files were checked -- the guard would pass vacuously"
    );
    assert!(
        newly_broken.is_empty(),
        "corpus specs stopped parsing (TLA+ frontend regression):\n  {}",
        newly_broken.join("\n  ")
    );
    assert!(
        wrongly_marked_broken.is_empty(),
        "these specs parse but the manifest still marks them unparseable -- \
         update parse_status:\n  {}",
        wrongly_marked_broken.join("\n  ")
    );
}
