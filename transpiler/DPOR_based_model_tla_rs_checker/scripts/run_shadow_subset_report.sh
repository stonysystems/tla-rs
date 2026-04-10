#!/usr/bin/env bash
# Run shadow-mode baseline-vs-DPOR comparison on the declared parity subset
# (Phase 38.10.4.b) and emit reproducible report artifacts.
#
# Usage:
#   ./scripts/run_shadow_subset_report.sh
#   ./scripts/run_shadow_subset_report.sh --timeout-sec 30
#   ./scripts/run_shadow_subset_report.sh --skip-build
#   ./scripts/run_shadow_subset_report.sh --output-json tests/reports/foo.json --output-md tests/reports/foo.md

set -euo pipefail

usage() {
    cat <<USAGE
Usage: scripts/run_shadow_subset_report.sh [options]

Options:
  --timeout-sec <n>   Timeout passed to shadow-compare baseline run (default: 30)
  --skip-build        Skip cargo build steps (requires binaries already built)
  --case <id>         Run only one declared subset case (repeatable)
  --output-json <p>   Output JSON report path (default: tests/reports/shadow_parity_subset_latest.json)
  --output-md <p>     Output Markdown summary path (default: tests/reports/shadow_parity_subset_latest.md)
  -h, --help          Show this help
USAGE
}

TIMEOUT_SEC=30
SKIP_BUILD=0
SELECTED_CASES=()

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORKFOLDER="$(cd "$SCRIPT_DIR/.." && pwd)"
REPO_ROOT="$(cd "$WORKFOLDER/../.." && pwd)"
TRANSPILER_DIR="$REPO_ROOT/transpiler"
REPORTS_DIR="$WORKFOLDER/tests/reports"
OUTPUT_JSON="$REPORTS_DIR/shadow_parity_subset_latest.json"
OUTPUT_MD="$REPORTS_DIR/shadow_parity_subset_latest.md"

while [[ $# -gt 0 ]]; do
    case "$1" in
        --timeout-sec)
            TIMEOUT_SEC="${2:-}"
            shift 2
            ;;
        --skip-build)
            SKIP_BUILD=1
            shift
            ;;
        --case)
            SELECTED_CASES+=("${2:-}")
            shift 2
            ;;
        --output-json)
            OUTPUT_JSON="${2:-}"
            shift 2
            ;;
        --output-md)
            OUTPUT_MD="${2:-}"
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

if ! [[ "$TIMEOUT_SEC" =~ ^[0-9]+$ ]] || [[ "$TIMEOUT_SEC" -le 0 ]]; then
    echo "--timeout-sec must be a positive integer, got: $TIMEOUT_SEC" >&2
    exit 2
fi

mkdir -p "$(dirname "$OUTPUT_JSON")"
mkdir -p "$(dirname "$OUTPUT_MD")"

if [[ "$SKIP_BUILD" -eq 0 ]]; then
    echo "Building transpiler binary (debug)..."
    cargo build --manifest-path "$TRANSPILER_DIR/Cargo.toml" --bin verus-transpile >/dev/null

    echo "Building dpor-checker binary (debug)..."
    cargo build --manifest-path "$WORKFOLDER/Cargo.toml" --bin dpor-checker >/dev/null
fi

DPOR_BIN="$WORKFOLDER/target/debug/dpor-checker"
if [[ ! -x "$DPOR_BIN" ]]; then
    echo "Missing dpor-checker binary at $DPOR_BIN (run without --skip-build first)" >&2
    exit 1
fi

TRANSPILER_BIN="$TRANSPILER_DIR/target/debug/verus-transpile"
if [[ ! -x "$TRANSPILER_BIN" ]]; then
    echo "Missing verus-transpile binary at $TRANSPILER_BIN (run without --skip-build first)" >&2
    exit 1
fi

# Ensure translated corpus exists.
if [[ ! -f "$WORKFOLDER/tests/tla-rs/01_aplusb/APlusB.rs" ]]; then
    echo "Translated corpus missing; regenerating..."
    "$SCRIPT_DIR/regenerate_corpus.sh"
fi

TMP_DIR="$(mktemp -d)"
trap 'rm -rf "$TMP_DIR"' EXIT

ENTRIES_JSONL="$TMP_DIR/entries.jsonl"

# Declared parity subset source of truth:
# src/dpor.rs::test_automated_baseline_vs_dpor_comparison
# Format: case_id|spec_filename|comma_separated_invariants|check_deadlock
CASES=(
  "01_aplusb|APlusB.rs|LSumInvariant|false"
  "02_counter_incdec|CounterIncDec.rs|LTypeOK|false"
  "03_counter_race_bug|CounterRaceBug.rs|LTotalCorrect|false"
  "04_lock_basic|LockBasic.rs|LMutualExclusion|false"
  "05_broken_lock_bug|BrokenLockBug.rs|LMutualExclusion|false"
  "06_ticket_lock|TicketLock.rs|LMutualExclusion|false"
  "07_producer_consumer_1slot|ProducerConsumer1Slot.rs|LSafetyInvariant|false"
  "08_bounded_buffer_2slot|BoundedBuffer2Slot.rs||false"
  "09_peterson_mutex_2p|PetersonMutex.rs|LMutualExclusion|false"
  "11_readers_writers_small|ReadersWritersBug.rs|LSafety|false"
  "12_dining_philosophers_3|DiningPhilosophers.rs||true"
  "13_twophase_small|TwoPhase.rs|LTCConsistent|false"
)

if [[ "${#SELECTED_CASES[@]}" -gt 0 ]]; then
    FILTERED_CASES=()
    for entry in "${CASES[@]}"; do
        IFS='|' read -r case_id _rest <<<"$entry"
        for selected in "${SELECTED_CASES[@]}"; do
            if [[ "$case_id" == "$selected" ]]; then
                FILTERED_CASES+=("$entry")
            fi
        done
    done

    if [[ "${#FILTERED_CASES[@]}" -ne "${#SELECTED_CASES[@]}" ]]; then
        echo "Unknown --case id requested. Declared subset ids are:" >&2
        for entry in "${CASES[@]}"; do
            IFS='|' read -r case_id _rest <<<"$entry"
            echo "  - $case_id" >&2
        done
        exit 2
    fi

    CASES=("${FILTERED_CASES[@]}")
fi

cd "$WORKFOLDER"

echo "Running shadow-compare parity subset (${#CASES[@]} cases)..."
for entry in "${CASES[@]}"; do
    IFS='|' read -r case_id spec_filename invariants_csv check_deadlock <<<"$entry"

    spec_rel="tests/tla-rs/$case_id/$spec_filename"
    if [[ ! -f "$spec_rel" ]]; then
        echo "Missing spec for case $case_id: $spec_rel" >&2
        exit 1
    fi

    per_case_model_rel="tests/model_configs/${case_id}.toml"
    if [[ -f "$per_case_model_rel" ]]; then
        model_rel="$per_case_model_rel"
        model_source="per_case"
    else
        model_rel="tests/model_configs/_shadow_default.toml"
        model_source="default"
    fi

    case_json="$TMP_DIR/${case_id}.json"
    cmd=(
        "$DPOR_BIN"
        shadow-compare
        --spec "$spec_rel"
        --model "$model_rel"
        --max-depth 20
        --max-states 10000
        --timeout-sec "$TIMEOUT_SEC"
    )

    if [[ -n "$invariants_csv" ]]; then
        IFS=',' read -r -a invs <<<"$invariants_csv"
        for inv in "${invs[@]}"; do
            if [[ -n "$inv" ]]; then
                cmd+=(--invariant "$inv")
            fi
        done
    fi

    if [[ "$check_deadlock" == "true" ]]; then
        cmd+=(--check-deadlock)
    fi

    "${cmd[@]}" > "$case_json"

    python3 - "$case_json" "$case_id" "$spec_rel" "$model_rel" "$model_source" <<'PY' >> "$ENTRIES_JSONL"
import json
import sys

report_path, case_id, spec_rel, model_rel, model_source = sys.argv[1:6]
with open(report_path, "r", encoding="utf-8") as fh:
    report = json.load(fh)

entry = {
    "case_id": case_id,
    "spec_file": spec_rel,
    "model_file": model_rel,
    "model_source": model_source,
    "classification": report.get("classification"),
    "verdict_match": report.get("verdict_match"),
    "state_match": report.get("state_match"),
    "witness_depth_match": report.get("witness_depth_match"),
    "baseline_verdict": report.get("baseline", {}).get("verdict"),
    "baseline_states": report.get("baseline", {}).get("distinct_states"),
    "baseline_first_violation_kind": report.get("baseline", {}).get("first_violation_kind"),
    "baseline_first_violation_depth": report.get("baseline", {}).get("first_violation_depth"),
    "dpor_verdict": report.get("dpor", {}).get("verdict"),
    "dpor_states": report.get("dpor", {}).get("distinct_states"),
    "dpor_first_violation_kind": report.get("dpor", {}).get("first_violation_kind"),
    "dpor_first_violation_depth": report.get("dpor", {}).get("first_violation_depth"),
    "shadow_report": report,
}
print(json.dumps(entry, sort_keys=True))
PY

    classification="$(python3 - "$case_json" <<'PY'
import json
import sys
with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)
print(report.get("classification", "<missing>"))
PY
)"

    echo "  [$case_id] $classification"
done

TIMESTAMP="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

python3 - "$ENTRIES_JSONL" "$OUTPUT_JSON" "$OUTPUT_MD" "$TIMESTAMP" "$TIMEOUT_SEC" <<'PY'
import json
import pathlib
import sys
from collections import Counter

entries_path, output_json, output_md, timestamp, timeout_sec = sys.argv[1:6]
entries = []
with open(entries_path, "r", encoding="utf-8") as fh:
    for line in fh:
        line = line.strip()
        if not line:
            continue
        entries.append(json.loads(line))

entries.sort(key=lambda x: x["case_id"])

counts = Counter(e.get("classification", "unknown") for e in entries)
positive_exact = counts.get("positive_exact", 0)
positive_state_mismatch = counts.get("positive_state_mismatch", 0)
negative_witness_match = counts.get("negative_witness_match", 0)
negative_witness_mismatch = counts.get("negative_witness_mismatch", 0)
verdict_mismatch = counts.get("verdict_mismatch", 0)

known = {
    "positive_exact",
    "positive_state_mismatch",
    "negative_witness_match",
    "negative_witness_mismatch",
    "verdict_mismatch",
}
other = sum(v for k, v in counts.items() if k not in known)

parity_failures = (
    positive_state_mismatch
    + negative_witness_mismatch
    + verdict_mismatch
    + other
)

summary = {
    "total_cases": len(entries),
    "positive_exact": positive_exact,
    "negative_witness_match": negative_witness_match,
    "positive_state_mismatch": positive_state_mismatch,
    "negative_witness_mismatch": negative_witness_mismatch,
    "verdict_mismatch": verdict_mismatch,
    "other_classifications": other,
    "parity_failures": parity_failures,
}

payload = {
    "schema_version": 1,
    "timestamp": timestamp,
    "subset_source": "src/dpor.rs::test_automated_baseline_vs_dpor_comparison",
    "command": "scripts/run_shadow_subset_report.sh",
    "timeout_sec": int(timeout_sec),
    "summary": summary,
    "cases": entries,
}

output_json_path = pathlib.Path(output_json)
output_json_path.parent.mkdir(parents=True, exist_ok=True)
output_json_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

md_lines = [
    "# Shadow Parity Subset Report",
    "",
    f"Timestamp: {timestamp}",
    "",
    "Subset source: `src/dpor.rs::test_automated_baseline_vs_dpor_comparison`",
    "",
    "## Summary",
    "",
    f"- Total cases: {summary['total_cases']}",
    f"- positive_exact: {summary['positive_exact']}",
    f"- negative_witness_match: {summary['negative_witness_match']}",
    f"- positive_state_mismatch: {summary['positive_state_mismatch']}",
    f"- negative_witness_mismatch: {summary['negative_witness_mismatch']}",
    f"- verdict_mismatch: {summary['verdict_mismatch']}",
    f"- other_classifications: {summary['other_classifications']}",
    f"- parity_failures: {summary['parity_failures']}",
    "",
    "## Cases",
    "",
    "| Case | Classification | Baseline verdict/states | DPOR verdict/states |",
    "|---|---|---|---|",
]

for entry in entries:
    md_lines.append(
        "| {case_id} | {classification} | {bl_verdict} / {bl_states} | {dp_verdict} / {dp_states} |".format(
            case_id=entry["case_id"],
            classification=entry.get("classification", ""),
            bl_verdict=entry.get("baseline_verdict", ""),
            bl_states=entry.get("baseline_states", ""),
            dp_verdict=entry.get("dpor_verdict", ""),
            dp_states=entry.get("dpor_states", ""),
        )
    )

output_md_path = pathlib.Path(output_md)
output_md_path.parent.mkdir(parents=True, exist_ok=True)
output_md_path.write_text("\n".join(md_lines) + "\n", encoding="utf-8")

if parity_failures > 0:
    print(
        f"shadow subset parity failures detected: {parity_failures}",
        file=sys.stderr,
    )
    sys.exit(1)
PY

echo ""
echo "========================================"
echo "Shadow Subset Summary ($TIMESTAMP)"
echo "========================================"
python3 - "$OUTPUT_JSON" <<'PY'
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    payload = json.load(fh)
summary = payload["summary"]
print(f"  Total cases:             {summary['total_cases']}")
print(f"  positive_exact:          {summary['positive_exact']}")
print(f"  negative_witness_match:  {summary['negative_witness_match']}")
print(f"  parity_failures:         {summary['parity_failures']}")
PY

echo "========================================"
echo "JSON report: $OUTPUT_JSON"
echo "MD report:   $OUTPUT_MD"
