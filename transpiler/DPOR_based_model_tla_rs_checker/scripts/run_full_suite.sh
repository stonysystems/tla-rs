#!/usr/bin/env bash
# Run all 20 DPOR checker test cases and produce a scoreboard.
#
# This script:
# 1. Ensures the corpus is generated (calls regenerate_corpus.sh if needed)
# 2. For each case, runs the baseline model checker (verus-transpile model-check)
# 3. Records per-case results as JSON in tests/reports/
# 4. Writes a summary scoreboard to tests/reports/latest.json
#
# Usage:
#   ./scripts/run_full_suite.sh                # from the DPOR workfolder
#   ./scripts/run_full_suite.sh --timeout 30   # per-case timeout in seconds (default: 30)

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORKFOLDER="$(cd "$SCRIPT_DIR/.." && pwd)"
REPO_ROOT="$(cd "$WORKFOLDER/../.." && pwd)"
TRANSPILER_DIR="$REPO_ROOT/transpiler"
TLA_DIR="$WORKFOLDER/tests/tla"
TLARS_DIR="$WORKFOLDER/tests/tla-rs"
MANIFEST="$WORKFOLDER/tests/manifest.toml"
REPORTS_DIR="$WORKFOLDER/tests/reports"

TIMEOUT_SEC=30
if [[ "${1:-}" == "--timeout" ]]; then
    TIMEOUT_SEC="${2:-30}"
fi

# Build transpiler
echo "Building transpiler (release)..."
cargo build --manifest-path "$TRANSPILER_DIR/Cargo.toml" --bin verus-transpile --release 2>&1 | tail -1
TRANSPILER="$TRANSPILER_DIR/target/release/verus-transpile"

# Ensure corpus exists
if [[ ! -d "$TLARS_DIR" ]] || [[ -z "$(ls -A "$TLARS_DIR" 2>/dev/null)" ]]; then
    echo "Corpus not found. Running regenerate_corpus.sh..."
    "$SCRIPT_DIR/regenerate_corpus.sh"
fi

# Clean reports
rm -rf "$REPORTS_DIR"
mkdir -p "$REPORTS_DIR"

# Timestamp
TIMESTAMP="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

# Counters
TOTAL=0
PASSED=0
FAILED=0
KNOWN_UNIMPL=0
TRANSLATION_FAILED=0
ERRORS=0

# Results array for JSON
RESULTS_JSON="["

# Process each case
for case_dir in "$TLA_DIR"/*/; do
    case_id="$(basename "$case_dir")"
    TOTAL=$((TOTAL + 1))

    # Read manifest fields
    tla_entry=""
    expected_result=""
    expected_property=""
    in_case=false
    while IFS= read -r line; do
        if [[ "$line" == *"id = \"$case_id\""* ]]; then
            in_case=true
        elif $in_case && [[ "$line" == "[[case]]"* ]]; then
            break
        elif $in_case; then
            case "$line" in
                tla_entry*) tla_entry="$(echo "$line" | sed 's/tla_entry = "\(.*\)"/\1/')" ;;
                expected_primary_result*) expected_result="$(echo "$line" | sed 's/expected_primary_result = "\(.*\)"/\1/')" ;;
                expected_property*) expected_property="$(echo "$line" | sed 's/expected_property = "\(.*\)"/\1/')" ;;
            esac
        fi
    done < "$MANIFEST"

    # Check for translation failure
    rs_dir="$TLARS_DIR/$case_id"
    if [[ -f "$rs_dir/TRANSLATION_FAILED" ]]; then
        echo "  [$case_id] TRANSLATION_FAILED (transpiler cannot translate this TLA+ yet)"
        TRANSLATION_FAILED=$((TRANSLATION_FAILED + 1))
        result_status="translation_failed"
        stop_reason="translation_failed"
        states=0
        elapsed_ms=0
    elif [[ "$expected_result" == "known_unimplemented" ]]; then
        echo "  [$case_id] KNOWN_UNIMPLEMENTED"
        KNOWN_UNIMPL=$((KNOWN_UNIMPL + 1))
        result_status="known_unimplemented"
        stop_reason="known_unimplemented"
        states=0
        elapsed_ms=0
    else
        # Find the .rs entry file
        rs_entry="$rs_dir/${tla_entry%.tla}.rs"
        if [[ ! -f "$rs_entry" ]]; then
            echo "  [$case_id] ERROR: translated file not found: $rs_entry"
            ERRORS=$((ERRORS + 1))
            result_status="error"
            stop_reason="missing_translated_file"
            states=0
            elapsed_ms=0
        else
            # Create minimal model config
            model_toml=$(mktemp /tmp/dpor_model_${case_id}_XXXXXX.toml)
            cat > "$model_toml" <<MODELEOF
[search]
max_depth = 100
max_states = 10000
timeout_ms = $((TIMEOUT_SEC * 1000))

[properties]
invariants = []
check_deadlock = false
successor_semantics = "deadlock"
MODELEOF

            # Build invariant args
            inv_args=""
            if [[ -n "$expected_property" ]]; then
                inv_args="--invariant L${expected_property}"
            fi

            # Run model checker
            start_ms=$(date +%s%3N 2>/dev/null || python3 -c "import time; print(int(time.time()*1000))")
            mc_allout="/tmp/dpor_allout_${case_id}.txt"
            mc_output=""
            timeout "${TIMEOUT_SEC}s" "$TRANSPILER" model-check \
                --input "$rs_entry" \
                --init LInit --next LNext \
                --model "$model_toml" \
                --json-report \
                $inv_args > "$mc_allout" 2>&1 && true
            # Extract JSON (last line starting with {) or empty
            mc_output="$(grep '^{' "$mc_allout" 2>/dev/null | tail -1 || true)"
            end_ms=$(date +%s%3N 2>/dev/null || python3 -c "import time; print(int(time.time()*1000))")
            elapsed_ms=$((end_ms - start_ms))

            rm -f "$model_toml" "$mc_allout"

            if [[ -z "$mc_output" ]]; then
                err_snippet="$(head -3 "$mc_allout" 2>/dev/null | tr '\n' ' ' | head -c 120)"
                echo "  [$case_id] ERROR: model checker failed ($err_snippet)"
                ERRORS=$((ERRORS + 1))
                result_status="error"
                stop_reason="checker_error"
                states=0
            else
                # Parse JSON result
                result_status=$(echo "$mc_output" | python3 -c "import sys,json; d=json.loads(sys.stdin.read()); print(d.get('result','error'))" 2>/dev/null || echo "parse_error")
                states=$(echo "$mc_output" | python3 -c "import sys,json; d=json.loads(sys.stdin.read()); s=d.get('summary',{}); print(s.get('distinct_states', s.get('states', 0)))" 2>/dev/null || echo "0")
                stop_reason=$(echo "$mc_output" | python3 -c "import sys,json; d=json.loads(sys.stdin.read()); print(d.get('stop_reason','unknown'))" 2>/dev/null || echo "unknown")

                # Determine pass/fail
                if [[ "$expected_result" == "ok" && "$result_status" == "ok" ]]; then
                    echo "  [$case_id] PASS (ok, $states states, ${elapsed_ms}ms)"
                    PASSED=$((PASSED + 1))
                elif [[ "$expected_result" == "invariant_violation" && "$result_status" == "invariant_violated" ]]; then
                    echo "  [$case_id] PASS (invariant_violation found, ${elapsed_ms}ms)"
                    PASSED=$((PASSED + 1))
                elif [[ "$expected_result" == "deadlock" && "$result_status" == "deadlock_detected" ]]; then
                    echo "  [$case_id] PASS (deadlock found, ${elapsed_ms}ms)"
                    PASSED=$((PASSED + 1))
                else
                    echo "  [$case_id] FAIL (expected=$expected_result, got=$result_status, $states states, ${elapsed_ms}ms)"
                    FAILED=$((FAILED + 1))
                fi
            fi
        fi
    fi

    # Build JSON result entry
    if [[ "$TOTAL" -gt 1 ]]; then
        RESULTS_JSON="$RESULTS_JSON,"
    fi
    RESULTS_JSON="$RESULTS_JSON
  {\"case_id\": \"$case_id\", \"engine\": \"baseline\", \"result\": \"$result_status\", \"stop_reason\": \"$stop_reason\", \"states\": $states, \"elapsed_ms\": $elapsed_ms, \"expected\": \"$expected_result\"}"
done

RESULTS_JSON="$RESULTS_JSON
]"

# Write results
cat > "$REPORTS_DIR/latest.json" <<JSONEOF
{
  "timestamp": "$TIMESTAMP",
  "engine": "baseline",
  "timeout_sec": $TIMEOUT_SEC,
  "total": $TOTAL,
  "passed": $PASSED,
  "failed": $FAILED,
  "translation_failed": $TRANSLATION_FAILED,
  "known_unimplemented": $KNOWN_UNIMPL,
  "errors": $ERRORS,
  "cases": $RESULTS_JSON
}
JSONEOF

echo ""
echo "========================================"
echo "Full Suite Summary ($TIMESTAMP)"
echo "========================================"
echo "  Total cases:          $TOTAL"
echo "  Passed:               $PASSED"
echo "  Failed:               $FAILED"
echo "  Translation failed:   $TRANSLATION_FAILED"
echo "  Known unimplemented:  $KNOWN_UNIMPL"
echo "  Errors:               $ERRORS"
echo "========================================"
echo "Results written to: tests/reports/latest.json"
