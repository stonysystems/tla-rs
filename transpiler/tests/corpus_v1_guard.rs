//! Phase 52 V1 — every corpus golden must pass `verus`.
//!
//! The manifest claims this for each case at `golden` or `green`, and until now
//! nothing checked it: the runs were done by hand and the result written into
//! `rewrite.md`. A claim nobody re-checks is a claim that decays — a translator
//! change can break a golden's typecheck while V3 (which compares the golden
//! against fresh output) stays happily green, because both sides moved
//! together.
//!
//! **Why the typecheck is worth a guard.** A spec-only file has no proof
//! obligations, so a pass reports `0 verified, 0 errors`, which looks like
//! nothing happened. It is not nothing: on this corpus the typecheck has caught
//! a message variant built without the fields it declares, an unbound
//! identifier where routing should have been, an `int`/`nat` mismatch, a
//! value-returning helper typed `bool`, and a record field emitted with no type
//! at all. Every one of those would have shipped as a plausible-looking spec.
//!
//! Verus is not present on every machine, so this test **skips** when it cannot
//! find one — but it says so loudly, and it never passes silently having
//! checked nothing.
//!
//! ```text
//! VERUS_PATH=/path/to/verus cargo test --test corpus_v1_guard -- --nocapture
//! ```

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus")
}

/// The `verus` binary, from `VERUS_PATH` or a source build beside the repo.
fn resolve_verus() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("VERUS_PATH") {
        let candidate = PathBuf::from(path);
        if candidate.exists() {
            return Some(candidate);
        }
    }
    // A source build is how this repo's Verus is installed: the released binary
    // is linked against a newer glibc than this machine has.
    let home = std::env::var("HOME").ok()?;
    let built = PathBuf::from(home).join("verus-src/source/target-verus/release/verus");
    built.exists().then_some(built)
}

fn goldens() -> Vec<(String, PathBuf)> {
    let mut out = Vec::new();
    let Ok(tiers) = fs::read_dir(corpus_dir()) else {
        return out;
    };
    for tier in tiers.flatten() {
        let Ok(cases) = fs::read_dir(tier.path()) else {
            continue;
        };
        for case in cases.flatten() {
            let golden = case.path().join("golden.rs");
            if golden.exists() {
                let id = case.file_name().to_string_lossy().to_string();
                out.push((id, golden));
            }
        }
    }
    out.sort();
    out
}

#[test]
fn every_golden_passes_verus() {
    let goldens = goldens();
    assert!(
        !goldens.is_empty(),
        "no golden.rs anywhere in the corpus -- this guard would pass vacuously"
    );

    let Some(verus) = resolve_verus() else {
        eprintln!(
            "SKIPPING V1: no verus binary found. Set VERUS_PATH to run it.\n\
             {} golden(s) went unchecked: {}",
            goldens.len(),
            goldens
                .iter()
                .map(|(id, _)| id.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        );
        return;
    };

    // Verus needs a writable directory for its own build products, and it must
    // not be the corpus.
    let work = std::env::temp_dir().join("tla_rs_corpus_v1");
    let _ = fs::remove_dir_all(&work);
    fs::create_dir_all(&work).expect("temp dir must be creatable");

    let mut failures = Vec::new();
    for (id, golden) in &goldens {
        let staged = work.join(format!("{id}.rs"));
        fs::copy(golden, &staged).expect("golden must be readable");

        let output = Command::new(&verus)
            // The corpus is checked against one Verus version; a mismatched
            // solver would report differences that are the toolchain's, not
            // the translator's.
            .args(["-V", "no-solver-version-check"])
            .arg(&staged)
            .arg("--crate-type=lib")
            .current_dir(&work)
            .output()
            .expect("verus must be runnable");

        let combined = format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        // Verus reports success on stdout; a non-zero status or any `error[`
        // means the golden does not typecheck.
        let passed = output.status.success() && !combined.contains("error[");
        if passed {
            eprintln!("V1 ok: {id}");
        } else {
            let first = combined
                .lines()
                .find(|l| l.starts_with("error"))
                .unwrap_or("(no error line)")
                .to_string();
            failures.push(format!("{id}: {first}"));
        }
    }

    assert!(
        failures.is_empty(),
        "golden(s) no longer pass verus:\n  {}",
        failures.join("\n  ")
    );
}
