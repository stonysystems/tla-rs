#!/usr/bin/env bash
# Verify shadow parity subset report schema/fields consumed by migration docs/tests.
#
# This is the Phase 38.10.4.c drift guard. It intentionally fails fast when
# required fields or semantics drift from the current contract.

set -euo pipefail

usage() {
    cat <<USAGE
Usage: scripts/verify_shadow_subset_report_schema.sh [options]

Options:
  --report-json <path>    JSON report to validate
                          (default: tests/reports/shadow_parity_subset_latest.json)
  --report-md <path>      Markdown report to validate
                          (default: tests/reports/shadow_parity_subset_latest.md)
  --expected-total <n>    Expected number of subset cases (default: 12)
  -h, --help              Show this help
USAGE
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORKFOLDER="$(cd "$SCRIPT_DIR/.." && pwd)"

REPORT_JSON="$WORKFOLDER/tests/reports/shadow_parity_subset_latest.json"
REPORT_MD="$WORKFOLDER/tests/reports/shadow_parity_subset_latest.md"
EXPECTED_TOTAL=12

while [[ $# -gt 0 ]]; do
    case "$1" in
        --report-json)
            REPORT_JSON="${2:-}"
            shift 2
            ;;
        --report-md)
            REPORT_MD="${2:-}"
            shift 2
            ;;
        --expected-total)
            EXPECTED_TOTAL="${2:-}"
            shift 2
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            echo "Unknown option: $1" >&2
            usage >&2
            exit 2
            ;;
    esac
done

if ! [[ "$EXPECTED_TOTAL" =~ ^[0-9]+$ ]]; then
    echo "--expected-total must be a non-negative integer, got: $EXPECTED_TOTAL" >&2
    exit 2
fi

if [[ ! -f "$REPORT_JSON" ]]; then
    echo "JSON report not found: $REPORT_JSON" >&2
    exit 1
fi
if [[ ! -f "$REPORT_MD" ]]; then
    echo "Markdown report not found: $REPORT_MD" >&2
    exit 1
fi

python3 - "$REPORT_JSON" "$REPORT_MD" "$EXPECTED_TOTAL" <<'PY'
import json
import sys
from pathlib import Path

json_path = Path(sys.argv[1])
md_path = Path(sys.argv[2])
expected_total = int(sys.argv[3])

errors = []


def fail(msg: str) -> None:
    errors.append(msg)


def expect(condition: bool, msg: str) -> None:
    if not condition:
        fail(msg)


def expect_key(obj, key: str, obj_name: str):
    if not isinstance(obj, dict):
        fail(f"{obj_name} is not an object")
        return None
    if key not in obj:
        fail(f"{obj_name} missing key `{key}`")
        return None
    return obj[key]


try:
    payload = json.loads(json_path.read_text(encoding="utf-8"))
except Exception as exc:
    print(f"ERROR: failed to parse JSON report {json_path}: {exc}", file=sys.stderr)
    sys.exit(1)

schema_version = expect_key(payload, "schema_version", "root")
if schema_version is not None:
    expect(isinstance(schema_version, int), "root.schema_version must be int")
    expect(schema_version == 1, f"root.schema_version must be 1 (got {schema_version})")

subset_source = expect_key(payload, "subset_source", "root")
if subset_source is not None:
    expect(
        subset_source == "src/dpor.rs::test_automated_baseline_vs_dpor_comparison",
        "root.subset_source drifted",
    )

command = expect_key(payload, "command", "root")
if command is not None:
    expect(command == "scripts/run_shadow_subset_report.sh", "root.command drifted")

timeout_sec = expect_key(payload, "timeout_sec", "root")
if timeout_sec is not None:
    expect(isinstance(timeout_sec, int), "root.timeout_sec must be int")

summary = expect_key(payload, "summary", "root")
cases = expect_key(payload, "cases", "root")
if cases is not None:
    expect(isinstance(cases, list), "root.cases must be array")

summary_keys = [
    "total_cases",
    "positive_exact",
    "negative_witness_match",
    "positive_state_mismatch",
    "negative_witness_mismatch",
    "verdict_mismatch",
    "other_classifications",
    "parity_failures",
]

if isinstance(summary, dict):
    for key in summary_keys:
        value = expect_key(summary, key, "summary")
        if value is not None:
            expect(isinstance(value, int), f"summary.{key} must be int")

if isinstance(summary, dict) and isinstance(cases, list):
    total_cases = summary.get("total_cases")
    if isinstance(total_cases, int):
        expect(total_cases == len(cases), "summary.total_cases != len(cases)")
        expect(total_cases == expected_total, f"summary.total_cases != expected_total ({expected_total})")

    pf = summary.get("parity_failures")
    psm = summary.get("positive_state_mismatch")
    nwm = summary.get("negative_witness_mismatch")
    vm = summary.get("verdict_mismatch")
    oc = summary.get("other_classifications")
    if all(isinstance(v, int) for v in [pf, psm, nwm, vm, oc]):
        expect(
            pf == (psm + nwm + vm + oc),
            "summary.parity_failures does not match mismatch bucket sum",
        )

case_required_keys = [
    "case_id",
    "spec_file",
    "model_file",
    "model_source",
    "classification",
    "verdict_match",
    "state_match",
    "witness_depth_match",
    "baseline_verdict",
    "baseline_states",
    "baseline_first_violation_kind",
    "baseline_first_violation_depth",
    "dpor_verdict",
    "dpor_states",
    "dpor_first_violation_kind",
    "dpor_first_violation_depth",
    "shadow_report",
]

shadow_required_keys = [
    "command",
    "classification",
    "verdict_match",
    "state_match",
    "witness_depth_match",
    "baseline",
    "dpor",
]

allowed_classifications = {
    "positive_exact",
    "positive_state_mismatch",
    "negative_witness_match",
    "negative_witness_mismatch",
    "verdict_mismatch",
}

seen_case_ids = set()
if isinstance(cases, list):
    for idx, case in enumerate(cases):
        obj_name = f"cases[{idx}]"
        if not isinstance(case, dict):
            fail(f"{obj_name} must be object")
            continue

        for key in case_required_keys:
            expect_key(case, key, obj_name)

        case_id = case.get("case_id")
        if isinstance(case_id, str):
            expect(case_id not in seen_case_ids, f"duplicate case_id `{case_id}`")
            seen_case_ids.add(case_id)
        else:
            fail(f"{obj_name}.case_id must be string")

        model_source = case.get("model_source")
        expect(
            model_source in {"per_case", "default"},
            f"{obj_name}.model_source must be per_case/default",
        )

        classification = case.get("classification")
        expect(
            classification in allowed_classifications,
            f"{obj_name}.classification unknown: {classification}",
        )

        expect(isinstance(case.get("baseline_states"), int), f"{obj_name}.baseline_states must be int")
        expect(isinstance(case.get("dpor_states"), int), f"{obj_name}.dpor_states must be int")

        verdict_match = case.get("verdict_match")
        expect(isinstance(verdict_match, bool), f"{obj_name}.verdict_match must be bool")

        state_match = case.get("state_match")
        expect(
            isinstance(state_match, bool) or state_match is None,
            f"{obj_name}.state_match must be bool|null",
        )
        witness_depth_match = case.get("witness_depth_match")
        expect(
            isinstance(witness_depth_match, bool) or witness_depth_match is None,
            f"{obj_name}.witness_depth_match must be bool|null",
        )

        baseline_kind = case.get("baseline_first_violation_kind")
        expect(
            isinstance(baseline_kind, str) or baseline_kind is None,
            f"{obj_name}.baseline_first_violation_kind must be str|null",
        )
        baseline_depth = case.get("baseline_first_violation_depth")
        expect(
            isinstance(baseline_depth, int) or baseline_depth is None,
            f"{obj_name}.baseline_first_violation_depth must be int|null",
        )
        dpor_kind = case.get("dpor_first_violation_kind")
        expect(
            isinstance(dpor_kind, str) or dpor_kind is None,
            f"{obj_name}.dpor_first_violation_kind must be str|null",
        )
        dpor_depth = case.get("dpor_first_violation_depth")
        expect(
            isinstance(dpor_depth, int) or dpor_depth is None,
            f"{obj_name}.dpor_first_violation_depth must be int|null",
        )

        shadow = case.get("shadow_report")
        if isinstance(shadow, dict):
            for key in shadow_required_keys:
                expect_key(shadow, key, f"{obj_name}.shadow_report")
            expect(
                shadow.get("command") == "shadow-compare",
                f"{obj_name}.shadow_report.command drifted",
            )
            expect(
                shadow.get("classification") == classification,
                f"{obj_name}.classification != shadow_report.classification",
            )
            expect(
                shadow.get("verdict_match") == verdict_match,
                f"{obj_name}.verdict_match != shadow_report.verdict_match",
            )

            bl = shadow.get("baseline")
            dp = shadow.get("dpor")
            if isinstance(bl, dict):
                expect_key(bl, "verdict", f"{obj_name}.shadow_report.baseline")
                expect_key(bl, "distinct_states", f"{obj_name}.shadow_report.baseline")
            else:
                fail(f"{obj_name}.shadow_report.baseline must be object")
            if isinstance(dp, dict):
                expect_key(dp, "verdict", f"{obj_name}.shadow_report.dpor")
                expect_key(dp, "distinct_states", f"{obj_name}.shadow_report.dpor")
            else:
                fail(f"{obj_name}.shadow_report.dpor must be object")
        else:
            fail(f"{obj_name}.shadow_report must be object")

md = md_path.read_text(encoding="utf-8")
for frag in [
    "# Shadow Parity Subset Report",
    "## Summary",
    "## Cases",
    "| Case | Classification | Baseline verdict/states | DPOR verdict/states |",
    "- parity_failures:",
]:
    expect(frag in md, f"markdown missing fragment: {frag}")

if isinstance(cases, list):
    for case in cases:
        cid = case.get("case_id")
        if isinstance(cid, str):
            expect(f"| {cid} |" in md, f"markdown missing case row for {cid}")

if errors:
    print("Shadow subset schema drift guard failed:", file=sys.stderr)
    for err in errors:
        print(f"  - {err}", file=sys.stderr)
    sys.exit(1)

print(f"shadow schema guard passed: {json_path} ({expected_total} expected rows)")
PY
