#!/usr/bin/env python3
"""Run model checker on all 20 cases and extract solver branch telemetry.

Usage:
  # Run all cases and print diagnostics table:
  python3 scripts/solver_diagnostics.py

  # Write markdown table to file:
  python3 scripts/solver_diagnostics.py --output tests/reports/solver_diagnostics.md

  # Parse a single pre-existing JSON report:
  python3 scripts/solver_diagnostics.py --file report.json

Produces a per-branch table showing:
  - Eq vs Predicate constraint counts
  - Direct assignment vs enumeration fallback
  - Fallback reason (why direct assignment was not used)
  - Candidate evaluations and wall time
"""

import argparse
import json
import os
import re
import subprocess
import sys

try:
    import tomllib
except ImportError:
    try:
        import tomli as tomllib
    except ImportError:
        tomllib = None


def extract_json_from_output(content):
    """Extract JSON object from model-check output (may have stderr mixed in)."""
    try:
        return json.loads(content)
    except (json.JSONDecodeError, ValueError):
        m = re.search(r'^\{.*^\}', content, re.MULTILINE | re.DOTALL)
        if m:
            try:
                return json.loads(m.group())
            except (json.JSONDecodeError, ValueError):
                pass
    return None


def extract_branch_telemetry(report):
    """Extract branch_telemetry from a JSON report dict."""
    if not report:
        return []
    if "branch_telemetry" in report:
        return report["branch_telemetry"]
    if "summary" in report and "branch_telemetry" in report["summary"]:
        return report["summary"]["branch_telemetry"]
    if "details" in report and "branch_telemetry" in report["details"]:
        return report["details"]["branch_telemetry"]
    return []


def run_case(transpiler, case_id, rs_entry, model_toml, manifest_entry, timeout=60):
    """Run model checker for one case and return branch telemetry."""
    expected_result = manifest_entry.get("expected_result", "ok")
    expected_property = manifest_entry.get("expected_property", "")

    inv_args = []
    if expected_property and expected_result != "deadlock":
        inv_args = ["--invariant", f"L{expected_property}"]

    cmd = [
        transpiler, "model-check",
        "--input", rs_entry,
        "--init", "LInit", "--next", "LNext",
        "--model", model_toml,
        "--json-report",
    ] + inv_args

    try:
        result = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout
        )
        output = result.stdout + result.stderr
        report = extract_json_from_output(output)
        return extract_branch_telemetry(report)
    except subprocess.TimeoutExpired:
        print(f"  [{case_id}] TIMEOUT ({timeout}s)", file=sys.stderr)
        return []
    except Exception as e:
        print(f"  [{case_id}] ERROR: {e}", file=sys.stderr)
        return []


def format_table(all_cases):
    """Format a markdown table of per-case, per-branch solver diagnostics."""
    lines = []
    lines.append("# Solver Branch Diagnostics (Phase 38.17.1)")
    lines.append("")
    lines.append("| Case | Branch | Eq | Pred | Solver | Fallback Reason | Invocations | Eval Calls | Solve ms |")
    lines.append("|------|--------|----|------|--------|-----------------|-------------|------------|----------|")

    total_direct = 0
    total_enum = 0
    total_branches = 0

    for case_id, branches in sorted(all_cases.items()):
        for b in branches:
            total_branches += 1
            solver = "direct" if b.get("direct_solver_hits", 0) > 0 else "enum"
            if solver == "direct":
                total_direct += 1
            else:
                total_enum += 1
            fallback = b.get("fallback_reason", "direct")
            eq = b.get("eq_constraints", "?")
            pred = b.get("predicate_constraints", "?")
            invocations = b.get("invocations", 0)
            eval_calls = b.get("evaluator_calls", 0)
            solve_ms = b.get("cumulative_solve_elapsed_ms", 0)
            label = b.get("branch_label", "?")
            lines.append(
                f"| {case_id} | {label} | {eq} | {pred} | {solver} | {fallback} | {invocations} | {eval_calls} | {solve_ms} |"
            )

    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- Total branches across all cases: {total_branches}")
    lines.append(f"- Direct assignment: {total_direct} ({100*total_direct/max(total_branches,1):.0f}%)")
    lines.append(f"- Enumeration fallback: {total_enum} ({100*total_enum/max(total_branches,1):.0f}%)")
    lines.append("")

    # Per-fallback-reason breakdown
    reason_counts = {}
    for case_id, branches in all_cases.items():
        for b in branches:
            reason = b.get("fallback_reason", "direct")
            reason_counts[reason] = reason_counts.get(reason, 0) + 1
    lines.append("### Fallback reason breakdown")
    lines.append("")
    for reason, count in sorted(reason_counts.items()):
        lines.append(f"- `{reason}`: {count} branches")
    lines.append("")

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description="Solver diagnostics extractor")
    parser.add_argument("--file", help="Single JSON report file to parse (skip running)")
    parser.add_argument("--output", help="Write markdown to this file")
    parser.add_argument("--timeout", type=int, default=120, help="Per-case timeout in seconds")
    args = parser.parse_args()

    all_cases = {}

    if args.file:
        with open(args.file) as f:
            content = f.read()
        report = extract_json_from_output(content)
        branches = extract_branch_telemetry(report)
        case_id = os.path.basename(args.file).replace(".json", "").replace(".txt", "")
        if branches:
            all_cases[case_id] = branches
    else:
        # Auto-detect paths relative to script location
        script_dir = os.path.dirname(os.path.abspath(__file__))
        workfolder = os.path.dirname(script_dir)
        repo_root = os.path.dirname(os.path.dirname(workfolder))
        transpiler_dir = os.path.join(repo_root, "transpiler")
        transpiler = os.path.join(transpiler_dir, "target", "release", "verus-transpile")

        if not os.path.isfile(transpiler):
            print("Building transpiler (release)...", file=sys.stderr)
            subprocess.run(
                ["cargo", "build", "--manifest-path",
                 os.path.join(transpiler_dir, "Cargo.toml"),
                 "--bin", "verus-transpile", "--release"],
                check=True, capture_output=True,
            )

        tlars_dir = os.path.join(workfolder, "tests", "tla-rs")
        configs_dir = os.path.join(workfolder, "tests", "model_configs")
        manifest_path = os.path.join(workfolder, "tests", "manifest.toml")

        if tomllib is None:
            print("Error: tomllib (Python 3.11+) or tomli package required", file=sys.stderr)
            sys.exit(1)

        with open(manifest_path, "rb") as f:
            manifest = tomllib.load(f)

        cases = manifest.get("case", [])
        print(f"Running {len(cases)} cases for solver diagnostics...", file=sys.stderr)

        for case in cases:
            case_id = case["id"]
            tla_entry = case.get("tla_entry", "")
            rs_name = tla_entry.replace(".tla", ".rs") if tla_entry else ""
            rs_entry = os.path.join(tlars_dir, case_id, rs_name)
            model_toml = os.path.join(configs_dir, f"{case_id}.toml")

            if not os.path.isfile(rs_entry):
                print(f"  [{case_id}] SKIP (no .rs file)", file=sys.stderr)
                continue
            if not os.path.isfile(model_toml):
                print(f"  [{case_id}] SKIP (no model config)", file=sys.stderr)
                continue

            print(f"  [{case_id}] running...", file=sys.stderr, end="", flush=True)
            branches = run_case(transpiler, case_id, rs_entry, model_toml, case, args.timeout)
            if branches:
                all_cases[case_id] = branches
                print(f" {len(branches)} branches", file=sys.stderr)
            else:
                print(f" no telemetry", file=sys.stderr)

    if not all_cases:
        print("No branch telemetry found.", file=sys.stderr)
        sys.exit(1)

    table = format_table(all_cases)

    if args.output:
        os.makedirs(os.path.dirname(os.path.abspath(args.output)), exist_ok=True)
        with open(args.output, "w") as f:
            f.write(table + "\n")
        print(f"Written to {args.output}", file=sys.stderr)
    else:
        print(table)


if __name__ == "__main__":
    main()
