//! Phase 52 V3 — translator output must match the frozen goldens.
//!
//! For every corpus case with a `clean.tla` and a `golden.rs`, the translator's
//! output is byte-compared against the golden's `verus! { .. }` block.
//!
//! **Why only that block.** A golden's module header is hand-written prose
//! explaining how to read the file beside its source spec; a translator cannot
//! produce it, and it is worth keeping for review. Everything the translator
//! *does* decide — every declaration, signature, conjunct and its order — is
//! inside the block, and is compared exactly. Nothing is normalised away, so a
//! reordered conjunct or a changed frame condition fails here.

use std::fs;
use std::path::{Path, PathBuf};

use verus_transpiler::tla::{emit, parse_module, project, ProjectionError};

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus")
}

/// The `verus! { .. }` block, which is everything the translator decides.
fn verus_block(source: &str) -> Option<&str> {
    let start = source.find("verus! {")?;
    Some(&source[start..])
}

#[test]
fn translator_output_matches_the_goldens() {
    let corpus = corpus_dir();
    let mut checked = 0usize;
    let mut failures = Vec::new();

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

            let source = fs::read_to_string(&clean).expect("clean.tla must be readable");
            let module = parse_module(&source)
                .unwrap_or_else(|e| panic!("{case_id}: clean.tla must parse: {e}"));
            let projected = match project(&module) {
                Ok(projected) => projected,
                Err(ProjectionError::NotClean(report)) => panic!(
                    "{case_id}: a case with a golden must be clean, got {:?}",
                    report.findings
                ),
            };
            let emitted = match emit(&projected) {
                Ok(text) => text,
                Err(gaps) => {
                    failures.push(format!("{case_id}: projection is incomplete: {gaps:?}"));
                    continue;
                }
            };
            checked += 1;

            let golden = fs::read_to_string(&golden_path).expect("golden.rs must be readable");
            let want = verus_block(&golden)
                .unwrap_or_else(|| panic!("{case_id}: golden has no verus! block"));
            let got = verus_block(&emitted)
                .unwrap_or_else(|| panic!("{case_id}: emitter produced no verus! block"));

            if want != got {
                let first_diff = want
                    .lines()
                    .zip(got.lines())
                    .enumerate()
                    .find(|(_, (w, g))| w != g)
                    .map(|(i, (w, g))| {
                        format!("line {}:\n    golden:  {w}\n    emitted: {g}", i + 1)
                    })
                    .unwrap_or_else(|| {
                        format!(
                            "lengths differ: golden {} lines, emitted {} lines",
                            want.lines().count(),
                            got.lines().count()
                        )
                    });
                failures.push(format!("{case_id}: {first_diff}"));
            }
        }
    }

    assert!(
        checked > 0,
        "no case had both a clean.tla and a golden.rs -- the guard would pass vacuously"
    );
    assert!(
        failures.is_empty(),
        "translator output no longer matches the goldens:\n  {}",
        failures.join("\n  ")
    );
}

/// The `pipeline --clean-subset` mode must produce exactly what `clean-tla`
/// produces.
///
/// They are two entry points onto one projection, and the whole value of the
/// pipeline mode is that it is not a second implementation. Without this, the
/// two could drift and the goldens would only pin one of them.
#[test]
fn the_pipeline_mode_agrees_with_clean_tla() {
    use std::process::Command;

    let corpus = corpus_dir();
    // One green case is enough: this pins the *wiring*, not the projection --
    // the projection itself is pinned by every golden.
    let clean = corpus.join("tier0/t0_01_simple/clean.tla");
    let golden = corpus.join("tier0/t0_01_simple/golden.rs");
    assert!(
        clean.exists(),
        "the case this guard is anchored to must exist"
    );

    let out_dir = std::env::temp_dir().join("tla_rs_pipeline_guard");
    let _ = fs::remove_dir_all(&out_dir);
    fs::create_dir_all(&out_dir).expect("temp dir must be creatable");
    let exec_out = out_dir.join("out.rs");

    let status = Command::new(env!("CARGO_BIN_EXE_verus-transpile"))
        .args(["pipeline", "--clean-subset", "--tla-input"])
        .arg(&clean)
        .arg("--exec-output")
        .arg(&exec_out)
        .output()
        .expect("the binary must be runnable");
    assert!(
        status.status.success(),
        "pipeline --clean-subset failed:\n{}",
        String::from_utf8_lossy(&status.stderr)
    );

    let produced = fs::read_to_string(exec_out.with_extension("spec.rs"))
        .expect("the pipeline must have written a spec");
    let golden = fs::read_to_string(&golden).expect("golden must be readable");

    let want = verus_block(&golden).expect("golden has a verus! block");
    let got = verus_block(&produced).expect("pipeline output has a verus! block");
    assert_eq!(
        want, got,
        "`pipeline --clean-subset` and `clean-tla` have drifted apart"
    );
}
