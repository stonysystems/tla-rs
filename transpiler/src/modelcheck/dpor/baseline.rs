//! Baseline explorer wrapper for the DPOR prototype.
//!
//! Uses the existing model checker (`verus-transpile model-check`) as a
//! subprocess oracle. This matches the isolation principle: the DPOR crate
//! does not reach into the transpiler's private model-checking internals.
//!
//! For DPOR's own exploration loop (Phase 38.8.1.c+), the key functions
//! (expand_type_domain_candidates, eval_spec_function_call_recursive) will
//! need to be extracted from main.rs into the library. Until then, the
//! baseline operates via CLI invocation.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Result of running the baseline model checker on a case.
#[derive(Debug, Clone)]
pub struct BaselineResult {
    pub case_id: String,
    pub result: String,
    pub stop_reason: String,
    pub states: usize,
    pub distinct_states: usize,
    pub elapsed_ms: u64,
    pub raw_json: Option<serde_json::Value>,
}

/// Run the baseline model checker on a translated tla-rs spec.
///
/// This invokes `verus-transpile model-check` as a subprocess.
pub fn run_baseline(
    transpiler_bin: &Path,
    spec_file: &Path,
    model_toml: &Path,
    invariants: &[String],
    _timeout_sec: u64,
) -> BaselineResult {
    let mut cmd = Command::new(transpiler_bin);
    cmd.arg("model-check")
        .arg("--input")
        .arg(spec_file)
        .arg("--init")
        .arg("LInit")
        .arg("--next")
        .arg("LNext")
        .arg("--model")
        .arg(model_toml)
        .arg("--json-report");

    for inv in invariants {
        cmd.arg("--invariant").arg(inv);
    }

    let output = match cmd.output() {
        Ok(o) => o,
        Err(e) => {
            return BaselineResult {
                case_id: spec_file
                    .file_stem()
                    .unwrap_or_default()
                    .to_string_lossy()
                    .to_string(),
                result: "error".to_string(),
                stop_reason: format!("subprocess_error: {}", e),
                states: 0,
                distinct_states: 0,
                elapsed_ms: 0,
                raw_json: None,
            };
        }
    };

    let stdout = String::from_utf8_lossy(&output.stdout);
    let case_id = spec_file
        .file_stem()
        .unwrap_or_default()
        .to_string_lossy()
        .to_string();

    // Try to parse JSON from output
    match serde_json::from_str::<serde_json::Value>(&stdout) {
        Ok(json) => {
            let result = json["result"].as_str().unwrap_or("parse_error").to_string();
            let stop_reason = json["stop_reason"]
                .as_str()
                .unwrap_or("unknown")
                .to_string();
            let summary = &json["summary"];
            let states = summary["states"].as_u64().unwrap_or(0) as usize;
            let distinct_states =
                summary["distinct_states"].as_u64().unwrap_or(states as u64) as usize;
            let elapsed_ms = summary["elapsed_ms"].as_u64().unwrap_or(0);

            BaselineResult {
                case_id,
                result,
                stop_reason,
                states,
                distinct_states,
                elapsed_ms,
                raw_json: Some(json),
            }
        }
        Err(_) => {
            let _stderr = String::from_utf8_lossy(&output.stderr);
            BaselineResult {
                case_id,
                result: "error".to_string(),
                stop_reason: format!(
                    "json_parse_error: {}",
                    stdout.chars().take(100).collect::<String>()
                ),
                states: 0,
                distinct_states: 0,
                elapsed_ms: 0,
                raw_json: None,
            }
        }
    }
}

/// Create a minimal model.toml file for a test case.
pub fn create_default_model_toml(dir: &Path) -> PathBuf {
    let model_path = dir.join("model.toml");
    let mut f = std::fs::File::create(&model_path).expect("Failed to create model.toml");
    write!(
        f,
        r#"[search]
max_depth = 50
max_states = 10000
timeout_ms = 30000

[properties]
invariants = []
check_deadlock = false
successor_semantics = "deadlock"

[quantifiers]
int = {{ min = 0, max = 5 }}
max_set_len = 4
max_seq_len = 4
"#
    )
    .expect("Failed to write model.toml");
    model_path
}

/// Find the transpiler binary (release build preferred).
pub fn find_transpiler_bin() -> Option<PathBuf> {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    // Try one parent (transpiler crate is at <repo>/transpiler/)
    // and two parents (dpor-checker crate is at <repo>/transpiler/DPOR_based_model_tla_rs_checker/)
    for depth in [1, 2] {
        let mut root = manifest_dir.clone();
        for _ in 0..depth {
            root = root.parent()?.to_path_buf();
        }
        let release = root.join("transpiler/target/release/verus-transpile");
        if release.exists() {
            return Some(release);
        }
        let debug = root.join("transpiler/target/debug/verus-transpile");
        if debug.exists() {
            return Some(debug);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_baseline_on_aplusb() {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_file = manifest_dir.join("tests/tla-rs/01_aplusb/APlusB.rs");
        if !spec_file.exists() {
            eprintln!("Skipping: APlusB.rs not found (run regenerate_corpus.sh first)");
            return;
        }

        let transpiler = match find_transpiler_bin() {
            Some(p) => p,
            None => {
                eprintln!("Skipping: transpiler binary not found (run cargo build --release)");
                return;
            }
        };

        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_default_model_toml(tmp.path());

        let result = run_baseline(
            &transpiler,
            &spec_file,
            &model_path,
            &["LSumInvariant".to_string()],
            30,
        );

        assert_eq!(result.result, "ok", "Expected ok, got: {:?}", result);
        assert!(
            result.distinct_states > 0,
            "Expected >0 states, got: {}",
            result.distinct_states
        );
        eprintln!(
            "APlusB baseline: {} states, {}ms",
            result.distinct_states, result.elapsed_ms
        );
    }

    #[test]
    fn test_baseline_on_producer_consumer() {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_file =
            manifest_dir.join("tests/tla-rs/07_producer_consumer_1slot/ProducerConsumer1Slot.rs");
        if !spec_file.exists() {
            eprintln!("Skipping: ProducerConsumer1Slot.rs not found");
            return;
        }

        let transpiler = match find_transpiler_bin() {
            Some(p) => p,
            None => {
                eprintln!("Skipping: transpiler binary not found");
                return;
            }
        };

        let tmp = tempfile::tempdir().unwrap();
        let model_path = create_default_model_toml(tmp.path());

        let result = run_baseline(
            &transpiler,
            &spec_file,
            &model_path,
            &["LSafetyInvariant".to_string()],
            30,
        );

        assert_eq!(result.result, "ok", "Expected ok, got: {:?}", result);
        assert!(result.distinct_states > 0);
        eprintln!(
            "ProducerConsumer baseline: {} states, {}ms",
            result.distinct_states, result.elapsed_ms
        );
    }
}
