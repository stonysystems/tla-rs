#!/usr/bin/env bash
# Cross-check native codegen vs baseline (bytecode/AST) model checker.
# Phase 38.22.1.c.vi: verifies that --native-codegen produces identical
# verdicts and state counts as the default evaluation pipeline.
#
# Usage:
#   ./scripts/run_native_cross_check.sh
#   ./scripts/run_native_cross_check.sh --skip-build
#   ./scripts/run_native_cross_check.sh --case 01_aplusb
#   ./scripts/run_native_cross_check.sh --output-json tests/reports/native_cross_check.json

set -euo pipefail

SKIP_BUILD=0
SELECTED_CASES=()

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORKFOLDER="$(cd "$SCRIPT_DIR/.." && pwd)"
REPO_ROOT="$(cd "$WORKFOLDER/../.." && pwd)"
TRANSPILER_DIR="$REPO_ROOT/transpiler"
REPORTS_DIR="$WORKFOLDER/tests/reports"
OUTPUT_JSON="$REPORTS_DIR/native_cross_check_latest.json"
OUTPUT_MD="$REPORTS_DIR/native_cross_check_latest.md"

while [[ $# -gt 0 ]]; do
    case "$1" in
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
            echo "Usage: scripts/run_native_cross_check.sh [--skip-build] [--case <id>]"
            exit 0
            ;;
        *)
            echo "Unknown option: $1" >&2
            exit 1
            ;;
    esac
done

# Build transpiler if needed
if [[ "$SKIP_BUILD" -eq 0 ]]; then
    echo "Building transpiler (release)..."
    (cd "$TRANSPILER_DIR" && cargo build --release --bin verus-transpile 2>&1 | tail -3)
fi

TRANSPILER_BIN="$TRANSPILER_DIR/target/release/verus-transpile"
if [[ ! -x "$TRANSPILER_BIN" ]]; then
    TRANSPILER_BIN="$TRANSPILER_DIR/target/debug/verus-transpile"
fi
if [[ ! -x "$TRANSPILER_BIN" ]]; then
    echo "ERROR: transpiler binary not found. Run cargo build first." >&2
    exit 1
fi

# Ensure translated corpus exists
if [[ ! -f "$WORKFOLDER/tests/tla-rs/01_aplusb/APlusB.rs" ]]; then
    echo "Translated corpus missing; regenerating..."
    "$SCRIPT_DIR/regenerate_corpus.sh"
fi

# Same 12-case subset as shadow-compare (the cases that finish quickly)
CASES=(
  "01_aplusb|APlusB.rs|LSumInvariant"
  "02_counter_incdec|CounterIncDec.rs|LTypeOK"
  "03_counter_race_bug|CounterRaceBug.rs|LTotalCorrect"
  "04_lock_basic|LockBasic.rs|LMutualExclusion"
  "05_broken_lock_bug|BrokenLockBug.rs|LMutualExclusion"
  "06_ticket_lock|TicketLock.rs|LMutualExclusion"
  "07_producer_consumer_1slot|ProducerConsumer1Slot.rs|LSafetyInvariant"
  "08_bounded_buffer_2slot|BoundedBuffer2Slot.rs|"
  "09_peterson_mutex_2p|PetersonMutex.rs|LMutualExclusion"
  "11_readers_writers_small|ReadersWritersBug.rs|LSafety"
  "12_dining_philosophers_3|DiningPhilosophers.rs|"
  "13_twophase_small|TwoPhase.rs|LTCConsistent"
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
    CASES=("${FILTERED_CASES[@]}")
fi

TMP_DIR="$(mktemp -d)"
trap 'rm -rf "$TMP_DIR"' EXIT

# Create a default model.toml for cases without per-case config
DEFAULT_MODEL="$TMP_DIR/model.toml"
cat > "$DEFAULT_MODEL" <<'TOML'
[search]
max_depth = 50
max_states = 10000
timeout_ms = 60000

[properties]
invariants = []
check_deadlock = false
successor_semantics = "deadlock"

[quantifiers]
int = { min = 0, max = 5 }
max_set_len = 4
max_seq_len = 4
TOML

cd "$WORKFOLDER"

TOTAL=0
EXACT_MATCH=0
MISMATCH=0
ERRORS=0
ENTRIES_JSONL="$TMP_DIR/entries.jsonl"

echo "Running native codegen cross-check (${#CASES[@]} cases)..."
echo ""
printf "%-30s %-12s %-10s %-10s %-8s\n" "CASE" "VERDICT" "BASELINE" "NATIVE" "STATUS"
printf "%-30s %-12s %-10s %-10s %-8s\n" "----" "-------" "--------" "------" "------"

for entry in "${CASES[@]}"; do
    IFS='|' read -r case_id spec_filename invariants_csv <<<"$entry"
    TOTAL=$((TOTAL + 1))

    spec_rel="tests/tla-rs/$case_id/$spec_filename"
    if [[ ! -f "$spec_rel" ]]; then
        echo "  SKIP $case_id: spec file not found"
        ERRORS=$((ERRORS + 1))
        continue
    fi

    per_case_model="tests/model_configs/${case_id}.toml"
    if [[ -f "$per_case_model" ]]; then
        model_file="$per_case_model"
    else
        model_file="$DEFAULT_MODEL"
    fi

    # Build invariant flags
    INV_FLAGS=()
    if [[ -n "$invariants_csv" ]]; then
        IFS=',' read -ra INVS <<<"$invariants_csv"
        for inv in "${INVS[@]}"; do
            INV_FLAGS+=(--invariant "$inv")
        done
    fi

    # Run baseline (bytecode/AST)
    baseline_json=$("$TRANSPILER_BIN" model-check \
        --input "$spec_rel" --init LInit --next LNext \
        --model "$model_file" --json-report \
        "${INV_FLAGS[@]}" 2>/dev/null || echo '{"result":"error","summary":{"distinct_states":0}}')

    baseline_verdict=$(echo "$baseline_json" | python3 -c "import sys,json; d=json.load(sys.stdin); print(d.get('result','error'))" 2>/dev/null || echo "error")
    baseline_states=$(echo "$baseline_json" | python3 -c "import sys,json; d=json.load(sys.stdin); print(d.get('summary',{}).get('distinct_states',0))" 2>/dev/null || echo "0")

    # Run with --native-codegen
    native_json=$("$TRANSPILER_BIN" model-check \
        --input "$spec_rel" --init LInit --next LNext \
        --model "$model_file" --json-report --native-codegen \
        "${INV_FLAGS[@]}" 2>/dev/null || echo '{"result":"error","summary":{"distinct_states":0}}')

    native_verdict=$(echo "$native_json" | python3 -c "import sys,json; d=json.load(sys.stdin); print(d.get('result','error'))" 2>/dev/null || echo "error")
    native_states=$(echo "$native_json" | python3 -c "import sys,json; d=json.load(sys.stdin); print(d.get('summary',{}).get('distinct_states',0))" 2>/dev/null || echo "0")

    # Compare
    if [[ "$baseline_verdict" == "$native_verdict" && "$baseline_states" == "$native_states" ]]; then
        status="PASS"
        EXACT_MATCH=$((EXACT_MATCH + 1))
    elif [[ "$baseline_verdict" == "error" || "$native_verdict" == "error" ]]; then
        status="ERROR"
        ERRORS=$((ERRORS + 1))
    else
        status="FAIL"
        MISMATCH=$((MISMATCH + 1))
    fi

    printf "%-30s %-12s %-10s %-10s %-8s\n" "$case_id" "$baseline_verdict" "$baseline_states" "$native_states" "$status"

    # Write JSONL entry
    cat >> "$ENTRIES_JSONL" <<ENTRY
{"case_id":"$case_id","baseline_verdict":"$baseline_verdict","baseline_states":$baseline_states,"native_verdict":"$native_verdict","native_states":$native_states,"status":"$status"}
ENTRY
done

echo ""
echo "Summary: $EXACT_MATCH exact match, $MISMATCH mismatch, $ERRORS errors (of $TOTAL cases)"

# Generate JSON report
mkdir -p "$(dirname "$OUTPUT_JSON")"
TIMESTAMP=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
{
    echo "{"
    echo "  \"schema_version\": 1,"
    echo "  \"timestamp\": \"$TIMESTAMP\","
    echo "  \"command\": \"scripts/run_native_cross_check.sh\","
    echo "  \"summary\": {"
    echo "    \"total_cases\": $TOTAL,"
    echo "    \"exact_match\": $EXACT_MATCH,"
    echo "    \"mismatch\": $MISMATCH,"
    echo "    \"errors\": $ERRORS"
    echo "  },"
    echo "  \"cases\": ["
    first=1
    while IFS= read -r line; do
        if [[ "$first" -eq 1 ]]; then
            first=0
        else
            echo ","
        fi
        echo -n "    $line"
    done < "$ENTRIES_JSONL"
    echo ""
    echo "  ]"
    echo "}"
} > "$OUTPUT_JSON"

# Generate Markdown summary
{
    echo "# Native Codegen Cross-Check Report"
    echo ""
    echo "Generated: $TIMESTAMP"
    echo ""
    echo "## Summary"
    echo ""
    echo "| Metric | Count |"
    echo "|--------|-------|"
    echo "| Total cases | $TOTAL |"
    echo "| Exact match | $EXACT_MATCH |"
    echo "| Mismatch | $MISMATCH |"
    echo "| Errors | $ERRORS |"
    echo ""
    echo "## Per-Case Results"
    echo ""
    echo "| Case | Verdict | Baseline States | Native States | Status |"
    echo "|------|---------|----------------|--------------|--------|"
    while IFS= read -r line; do
        cid=$(echo "$line" | python3 -c "import sys,json; print(json.load(sys.stdin)['case_id'])")
        bv=$(echo "$line" | python3 -c "import sys,json; print(json.load(sys.stdin)['baseline_verdict'])")
        bs=$(echo "$line" | python3 -c "import sys,json; print(json.load(sys.stdin)['baseline_states'])")
        ns=$(echo "$line" | python3 -c "import sys,json; print(json.load(sys.stdin)['native_states'])")
        st=$(echo "$line" | python3 -c "import sys,json; print(json.load(sys.stdin)['status'])")
        echo "| $cid | $bv | $bs | $ns | $st |"
    done < "$ENTRIES_JSONL"
} > "$OUTPUT_MD"

echo "Reports written to:"
echo "  JSON: $OUTPUT_JSON"
echo "  MD:   $OUTPUT_MD"

if [[ "$MISMATCH" -gt 0 ]]; then
    echo "FAIL: $MISMATCH cases have mismatched state counts!"
    exit 1
fi
