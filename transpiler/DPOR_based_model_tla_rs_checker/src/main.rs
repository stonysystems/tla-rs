//! DPOR checker CLI entrypoint.

use std::path::{Path, PathBuf};
use std::time::Instant;

use dpor_checker::baseline::{find_transpiler_bin, run_baseline};
use dpor_checker::dpor::{explore_dpor, DporConfig, DporResult};
use dpor_checker::enabled::SpecContext;
use serde::Serialize;

#[derive(Debug, Clone, PartialEq, Eq)]
struct ShadowCompareArgs {
    spec_file: PathBuf,
    model_file: PathBuf,
    types_file: Option<PathBuf>,
    invariants: Vec<String>,
    check_deadlock: bool,
    /// Phase 38.18.4: when None, use the model.toml's `[search] max_depth`
    /// so DPOR explores the same depth as the baseline. The CLI flag
    /// `--max-depth` overrides.
    max_depth: Option<usize>,
    max_states: usize,
    timeout_sec: u64,
    json_out: Option<PathBuf>,
}

#[derive(Debug, Serialize)]
struct EngineReport {
    verdict: String,
    stop_reason: Option<String>,
    distinct_states: usize,
    transitions_fired: Option<usize>,
    max_depth: Option<usize>,
    elapsed_ms: u64,
    first_violation_depth: Option<usize>,
    first_violation_kind: Option<String>,
}

#[derive(Debug, Serialize)]
struct ShadowCompareReport {
    command: String,
    classification: String,
    verdict_match: bool,
    state_match: Option<bool>,
    witness_depth_match: Option<bool>,
    spec_file: String,
    model_file: String,
    types_file: Option<String>,
    invariants: Vec<String>,
    check_deadlock: bool,
    baseline: EngineReport,
    dpor: EngineReport,
}

fn main() {
    if let Err(err) = run_cli(std::env::args().skip(1).collect()) {
        eprintln!("dpor-checker: {}", err);
        std::process::exit(2);
    }
}

fn run_cli(args: Vec<String>) -> Result<(), String> {
    if args.is_empty() || args[0] == "--help" || args[0] == "-h" {
        print_help();
        return Ok(());
    }

    match args[0].as_str() {
        "shadow-compare" => {
            if args[1..].iter().any(|a| a == "--help" || a == "-h") {
                print_shadow_compare_help();
                return Ok(());
            }
            let parsed = parse_shadow_compare_args(&args[1..])?;
            let report = run_shadow_compare(&parsed)?;
            let json = serde_json::to_string_pretty(&report)
                .map_err(|err| format!("failed to serialize report: {}", err))?;
            println!("{}", json);

            if let Some(path) = &parsed.json_out {
                std::fs::write(path, format!("{}\n", json)).map_err(|err| {
                    format!("failed to write --json-out file {}: {}", path.display(), err)
                })?;
            }
            Ok(())
        }
        cmd => Err(format!(
            "unknown command `{}` (supported: shadow-compare)",
            cmd
        )),
    }
}

fn parse_shadow_compare_args(args: &[String]) -> Result<ShadowCompareArgs, String> {
    let mut spec_file: Option<PathBuf> = None;
    let mut model_file: Option<PathBuf> = None;
    let mut types_file: Option<PathBuf> = None;
    let mut invariants: Vec<String> = Vec::new();
    let mut check_deadlock = false;
    let mut max_depth: Option<usize> = None;
    let mut max_states: usize = 100_000;
    let mut timeout_sec: u64 = 30;
    let mut json_out: Option<PathBuf> = None;

    let mut i = 0usize;
    while i < args.len() {
        match args[i].as_str() {
            "--spec" => {
                i += 1;
                spec_file = Some(PathBuf::from(next_arg(args, i, "--spec")?));
            }
            "--model" => {
                i += 1;
                model_file = Some(PathBuf::from(next_arg(args, i, "--model")?));
            }
            "--types" => {
                i += 1;
                types_file = Some(PathBuf::from(next_arg(args, i, "--types")?));
            }
            "--invariant" => {
                i += 1;
                let raw = next_arg(args, i, "--invariant")?;
                invariants.push(normalize_invariant_name(raw));
            }
            "--check-deadlock" => {
                check_deadlock = true;
            }
            "--max-depth" => {
                i += 1;
                let raw = next_arg(args, i, "--max-depth")?;
                max_depth = Some(
                    raw.parse::<usize>()
                        .map_err(|err| format!("invalid --max-depth `{}`: {}", raw, err))?,
                );
            }
            "--max-states" => {
                i += 1;
                let raw = next_arg(args, i, "--max-states")?;
                max_states = raw
                    .parse::<usize>()
                    .map_err(|err| format!("invalid --max-states `{}`: {}", raw, err))?;
            }
            "--timeout-sec" => {
                i += 1;
                let raw = next_arg(args, i, "--timeout-sec")?;
                timeout_sec = raw
                    .parse::<u64>()
                    .map_err(|err| format!("invalid --timeout-sec `{}`: {}", raw, err))?;
            }
            "--json-out" => {
                i += 1;
                json_out = Some(PathBuf::from(next_arg(args, i, "--json-out")?));
            }
            unknown => {
                return Err(format!("unknown shadow-compare option `{}`", unknown));
            }
        }
        i += 1;
    }

    let Some(spec_file) = spec_file else {
        return Err("missing required option --spec <path>".to_string());
    };
    let Some(model_file) = model_file else {
        return Err("missing required option --model <path>".to_string());
    };

    Ok(ShadowCompareArgs {
        spec_file,
        model_file,
        types_file,
        invariants,
        check_deadlock,
        max_depth,
        max_states,
        timeout_sec,
        json_out,
    })
}

fn next_arg<'a>(args: &'a [String], i: usize, flag: &str) -> Result<&'a str, String> {
    args.get(i)
        .map(|s| s.as_str())
        .ok_or_else(|| format!("{} requires a value", flag))
}

fn normalize_invariant_name(raw: &str) -> String {
    if raw.starts_with('L') {
        raw.to_string()
    } else {
        format!("L{}", raw)
    }
}

fn run_shadow_compare(args: &ShadowCompareArgs) -> Result<ShadowCompareReport, String> {
    let transpiler_bin = find_transpiler_bin().ok_or_else(|| {
        "failed to find verus-transpile binary (expected transpiler/target/{debug,release}/verus-transpile)".to_string()
    })?;

    if !args.spec_file.exists() {
        return Err(format!(
            "--spec path does not exist: {}",
            args.spec_file.display()
        ));
    }
    if !args.model_file.exists() {
        return Err(format!(
            "--model path does not exist: {}",
            args.model_file.display()
        ));
    }
    if let Some(types_file) = &args.types_file {
        if !types_file.exists() {
            return Err(format!(
                "--types path does not exist: {}",
                types_file.display()
            ));
        }
    }

    let baseline = run_baseline(
        &transpiler_bin,
        &args.spec_file,
        &args.model_file,
        &args.invariants,
        args.timeout_sec,
    );

    let ctx = SpecContext::load(
        &args.spec_file,
        args.types_file.as_deref(),
        &args.model_file,
        "LInit",
        "LNext",
    )
    .map_err(|err| format!("failed to load spec context: {}", err))?;

    // Phase 38.18.4: when --max-depth is not given on the CLI, use the
    // model.toml's `[search] max_depth` so DPOR explores the same depth
    // as the baseline. Pre-fix, the CLI defaulted to 100 and ignored
    // the model config, which made DPOR explore further than the
    // baseline on cases like Raft (DPOR 1930 states vs baseline 812).
    let effective_max_depth = args
        .max_depth
        .unwrap_or(ctx.model_config.search.max_depth);
    let dpor_config = DporConfig {
        max_depth: effective_max_depth,
        max_states: args.max_states,
        use_independence: true,
        use_sleep_sets: true,
        invariants: args.invariants.clone(),
        check_deadlock: args.check_deadlock,
        runtime_overrides: None,
    };

    let dpor_start = Instant::now();
    let dpor_result = explore_dpor(&ctx, &dpor_config);
    let dpor_elapsed_ms = dpor_start.elapsed().as_millis() as u64;

    let (dpor_verdict, dpor_violation_kind, dpor_violation_depth) =
        classify_dpor_result(&dpor_result);
    let baseline_violation_depth = baseline_first_violation_depth(baseline.raw_json.as_ref());
    let baseline_violation_kind = baseline_violation_kind(&baseline);

    let verdict_match = baseline.result == dpor_verdict;
    let state_match = if baseline.result == "ok" && dpor_verdict == "ok" {
        Some(baseline.distinct_states == dpor_result.distinct_states.len())
    } else {
        None
    };
    let witness_depth_match = if baseline.result != "ok" && dpor_verdict != "ok" {
        match (baseline_violation_depth, dpor_violation_depth) {
            (Some(b), Some(d)) => Some(b == d),
            _ => None,
        }
    } else {
        None
    };

    let classification = classify_shadow_outcome(
        &baseline.result,
        &dpor_verdict,
        verdict_match,
        state_match,
        witness_depth_match,
        baseline_violation_kind.as_deref(),
        dpor_violation_kind.as_deref(),
    );

    Ok(ShadowCompareReport {
        command: "shadow-compare".to_string(),
        classification: classification.to_string(),
        verdict_match,
        state_match,
        witness_depth_match,
        spec_file: path_as_string(&args.spec_file),
        model_file: path_as_string(&args.model_file),
        types_file: args.types_file.as_ref().map(|path| path_as_string(path)),
        invariants: args.invariants.clone(),
        check_deadlock: args.check_deadlock,
        baseline: EngineReport {
            verdict: baseline.result,
            stop_reason: Some(baseline.stop_reason),
            distinct_states: baseline.distinct_states,
            transitions_fired: None,
            max_depth: None,
            elapsed_ms: baseline.elapsed_ms,
            first_violation_depth: baseline_violation_depth,
            first_violation_kind: baseline_violation_kind,
        },
        dpor: EngineReport {
            verdict: dpor_verdict,
            stop_reason: None,
            distinct_states: dpor_result.distinct_states.len(),
            transitions_fired: Some(dpor_result.transitions_fired),
            max_depth: Some(dpor_result.max_depth),
            elapsed_ms: dpor_elapsed_ms,
            first_violation_depth: dpor_violation_depth,
            first_violation_kind: dpor_violation_kind,
        },
    })
}

fn classify_dpor_result(result: &DporResult) -> (String, Option<String>, Option<usize>) {
    match &result.violation {
        Some(witness) if witness.invariant == "__deadlock__" => (
            "deadlock_detected".to_string(),
            Some("__deadlock__".to_string()),
            Some(witness.depth),
        ),
        Some(witness) => (
            "invariant_violated".to_string(),
            Some(witness.invariant.clone()),
            Some(witness.depth),
        ),
        None => ("ok".to_string(), None, None),
    }
}

fn baseline_first_violation_depth(raw_json: Option<&serde_json::Value>) -> Option<usize> {
    if let Some(depth) = raw_json
        .and_then(|v| v.get("invariant_violation"))
        .and_then(|iv| iv.get("depth"))
        .and_then(|d| d.as_u64())
    {
        return Some(depth as usize);
    }

    if let Some(depth) = raw_json
        .and_then(|v| v.get("deadlock"))
        .and_then(|dl| dl.get("depth"))
        .and_then(|d| d.as_u64())
    {
        return Some(depth as usize);
    }

    raw_json
        .and_then(|v| v.get("summary"))
        .and_then(|s| s.get("first_violation_depth"))
        .and_then(|d| d.as_u64())
        .map(|d| d as usize)
}

fn baseline_violation_kind(baseline: &dpor_checker::baseline::BaselineResult) -> Option<String> {
    if let Some(invariant) = baseline
        .raw_json
        .as_ref()
        .and_then(|v| v.get("invariant_violation"))
        .and_then(|iv| iv.get("invariant"))
        .and_then(|v| v.as_str())
    {
        return Some(invariant.to_string());
    }

    if baseline
        .raw_json
        .as_ref()
        .and_then(|v| v.get("deadlock"))
        .filter(|v| !v.is_null())
        .is_some()
    {
        return Some("__deadlock__".to_string());
    }

    let from_summary = baseline
        .raw_json
        .as_ref()
        .and_then(|v| v.get("summary"))
        .and_then(|s| s.get("first_violation_invariant"))
        .and_then(|v| v.as_str())
        .map(|s| s.to_string());

    if from_summary.is_some() {
        return from_summary;
    }

    match baseline.result.as_str() {
        "deadlock_detected" => Some("__deadlock__".to_string()),
        "invariant_violated" => Some("invariant_violated".to_string()),
        _ => None,
    }
}

#[allow(clippy::too_many_arguments)]
fn classify_shadow_outcome(
    baseline_verdict: &str,
    dpor_verdict: &str,
    verdict_match: bool,
    state_match: Option<bool>,
    witness_depth_match: Option<bool>,
    baseline_kind: Option<&str>,
    dpor_kind: Option<&str>,
) -> &'static str {
    if !verdict_match {
        return "verdict_mismatch";
    }

    if baseline_verdict == "ok" && dpor_verdict == "ok" {
        if state_match == Some(true) {
            return "positive_exact";
        }
        return "positive_state_mismatch";
    }

    let kind_match = match (baseline_kind, dpor_kind) {
        (Some(b), Some(d)) => b == d,
        _ => false,
    };
    let depth_match = witness_depth_match == Some(true);
    if kind_match && depth_match {
        "negative_witness_match"
    } else {
        "negative_witness_mismatch"
    }
}

fn path_as_string(path: &Path) -> String {
    path.to_string_lossy().to_string()
}

fn print_help() {
    println!("dpor-checker commands:");
    println!("  shadow-compare   Run baseline + DPOR on one spec/model pair");
    println!();
    println!("Run `dpor-checker shadow-compare --help` for options.");
}

fn print_shadow_compare_help() {
    println!("Usage:");
    println!("  dpor-checker shadow-compare --spec <file.rs> --model <file.toml> [options]");
    println!();
    println!("Options:");
    println!("  --types <file.rs>            Optional types.rs companion file");
    println!("  --invariant <name>           Invariant name (repeatable); `L` prefix optional");
    println!("  --check-deadlock             Enable deadlock detection in DPOR run");
    println!("  --max-depth <n>              DPOR max depth (default: 100)");
    println!("  --max-states <n>             DPOR max states (default: 100000)");
    println!("  --timeout-sec <n>            Baseline timeout in seconds (default: 30)");
    println!("  --json-out <path>            Also write JSON report to file");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_shadow_compare_args_with_options() {
        let args = vec![
            "--spec".to_string(),
            "spec.rs".to_string(),
            "--model".to_string(),
            "model.toml".to_string(),
            "--types".to_string(),
            "types.rs".to_string(),
            "--invariant".to_string(),
            "Safety".to_string(),
            "--invariant".to_string(),
            "LTypeOk".to_string(),
            "--check-deadlock".to_string(),
            "--max-depth".to_string(),
            "12".to_string(),
            "--max-states".to_string(),
            "345".to_string(),
            "--timeout-sec".to_string(),
            "9".to_string(),
            "--json-out".to_string(),
            "out.json".to_string(),
        ];
        let parsed = parse_shadow_compare_args(&args).expect("parse should succeed");
        assert_eq!(parsed.types_file, Some(PathBuf::from("types.rs")));
        assert_eq!(
            parsed.invariants,
            vec!["LSafety".to_string(), "LTypeOk".to_string()]
        );
        assert!(parsed.check_deadlock);
        assert_eq!(parsed.max_depth, Some(12));
        assert_eq!(parsed.max_states, 345);
        assert_eq!(parsed.timeout_sec, 9);
        assert_eq!(parsed.json_out, Some(PathBuf::from("out.json")));
    }

    #[test]
    fn test_run_shadow_compare_aplusb_smoke() {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let spec_file = manifest_dir.join("tests/tla-rs/01_aplusb/APlusB.rs");
        if !spec_file.exists() {
            eprintln!("Skipping: {} missing", spec_file.display());
            return;
        }
        if find_transpiler_bin().is_none() {
            eprintln!("Skipping: transpiler binary not available");
            return;
        }

        let tmp = tempfile::tempdir().expect("temp dir");
        let model_path = dpor_checker::baseline::create_default_model_toml(tmp.path());

        let args = ShadowCompareArgs {
            spec_file,
            model_file: model_path,
            types_file: None,
            invariants: vec!["LSumInvariant".to_string()],
            check_deadlock: false,
            max_depth: Some(30),
            max_states: 10_000,
            timeout_sec: 30,
            json_out: None,
        };

        let report = run_shadow_compare(&args).expect("shadow compare should succeed");
        assert!(report.verdict_match, "expected verdict parity: {:?}", report);
        assert_eq!(report.baseline.verdict, "ok");
        assert_eq!(report.dpor.verdict, "ok");
    }
}
