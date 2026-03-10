#!/usr/bin/env bash
# Run source-first model-check 1-hour benchmarks for the 4 benchmark protocols.
#
# These are long-running benchmarks (1h timeout per protocol) intended for
# performance comparison, NOT for CI smoke tests. For fast CI tests, use
# scripts/run_model_check_matrix.sh instead.
#
# Usage:
#   ./scripts/run_model_check_benchmarks.sh
#   OUTPUT_DIR=reports/benchmarks/source_first ./scripts/run_model_check_benchmarks.sh
#   TRANSPILER_BIN=transpiler/target/release/verus-transpile ./scripts/run_model_check_benchmarks.sh
#   PROTOCOLS="twophase primarybackup" ./scripts/run_model_check_benchmarks.sh  # subset

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
OUTPUT_DIR="${OUTPUT_DIR:-$PROJECT_ROOT/reports/benchmarks/source_first}"
TRANSPILER_BIN="${TRANSPILER_BIN:-$PROJECT_ROOT/transpiler/target/debug/verus-transpile}"
PROTOCOLS="${PROTOCOLS:-twophase primarybackup leaderelection paxos}"
TIMEOUT_MS="${TIMEOUT_MS:-}"

FIXTURE_DIR="$PROJECT_ROOT/transpiler/tests/model_check_fixtures/benchmarks_1h"

# Protocol source paths
declare -A PROTOCOL_INPUT=(
    [twophase]="src/protocol/TwoPhase/twophase.rs"
    [primarybackup]="src/protocol/PrimaryBackup/primarybackup.rs"
    [leaderelection]="src/protocol/LeaderElection/election.rs"
    [paxos]="src/protocol/Paxos/paxos.rs"
)
declare -A PROTOCOL_TYPES=(
    [twophase]="src/protocol/TwoPhase/types.rs"
    [primarybackup]="src/protocol/PrimaryBackup/types.rs"
    [leaderelection]="src/protocol/LeaderElection/types.rs"
    [paxos]="src/protocol/Paxos/types.rs"
)
declare -A PROTOCOL_MODEL=(
    [twophase]="twophase_benchmark.model.toml"
    [primarybackup]="primarybackup_benchmark.model.toml"
    [leaderelection]="leaderelection_benchmark.model.toml"
    [paxos]="paxos_benchmark.model.toml"
)

mkdir -p "$OUTPUT_DIR"

if [[ ! -x "$TRANSPILER_BIN" ]]; then
    echo "Building transpiler binary ($TRANSPILER_BIN)..."
    cargo build --manifest-path "$PROJECT_ROOT/transpiler/Cargo.toml" --bin verus-transpile
fi

echo "=== Source-first 1-hour benchmark campaign ==="
echo "Output: ${OUTPUT_DIR#$PROJECT_ROOT/}"
echo "Protocols: $PROTOCOLS"
if [[ -n "$TIMEOUT_MS" ]]; then
    echo "Timeout override: ${TIMEOUT_MS}ms"
fi
echo ""

SUMMARY_FILE="$OUTPUT_DIR/SUMMARY.md"
{
    echo "# Source-first Benchmark Results"
    echo ""
    echo "Generated: $(date -u '+%Y-%m-%d %H:%M:%S UTC')"
    echo "Git rev: $(git -C "$PROJECT_ROOT" rev-parse --short HEAD)"
    echo ""
    echo "| Protocol | Result | States | Distinct | Depth | Wall time (s) |"
    echo "|----------|--------|--------|----------|-------|---------------|"
} > "$SUMMARY_FILE"

for proto in $PROTOCOLS; do
    input="${PROTOCOL_INPUT[$proto]}"
    types="${PROTOCOL_TYPES[$proto]}"
    model="${FIXTURE_DIR}/${PROTOCOL_MODEL[$proto]}"

    if [[ ! -f "$model" ]]; then
        echo "SKIP: $proto — model config not found: $model"
        continue
    fi

    artifact="$OUTPUT_DIR/${proto}_benchmark.json"
    echo "Running: $proto (1h timeout) ..."
    start_time=$(date +%s)

    (
        cd "$PROJECT_ROOT"
        run_cmd=(
            "$TRANSPILER_BIN" model-check
            --input "$input" \
            --types "$types" \
            --model "$model" \
            --search bfs \
            --json-report
        )
        if [[ -n "$TIMEOUT_MS" ]]; then
            run_cmd+=(--timeout "$TIMEOUT_MS")
        fi
        "${run_cmd[@]}"
    ) > "$artifact" 2>&1 || true

    end_time=$(date +%s)
    wall_secs=$((end_time - start_time))

    # Extract result fields from JSON (fields are in top-level "result",
    # "stop_reason", and nested "summary.states", "summary.depth")
    result=$(python3 -c "
import json, sys
try:
    d = json.load(open('$artifact'))
    r = d.get('result', 'error')
    sr = d.get('stop_reason', '')
    s = d.get('summary', {})
    print(f\"{r}({sr})|{s.get('states','?')}|{s.get('states','?')}|{s.get('depth','?')}\")
except: print('error|?|?|?')
" 2>/dev/null || echo "error|?|?|?")
    IFS='|' read -r result states distinct depth <<< "$result"

    echo "  Done: $result ($states states, ${wall_secs}s)"
    echo "| $proto | $result | $states | $distinct | $depth | $wall_secs |" >> "$SUMMARY_FILE"
done

echo "" >> "$SUMMARY_FILE"
echo "Benchmark configs: \`transpiler/tests/model_check_fixtures/benchmarks_1h/\`" >> "$SUMMARY_FILE"

echo ""
echo "Summary written to: ${SUMMARY_FILE#$PROJECT_ROOT/}"
echo "Individual artifacts in: ${OUTPUT_DIR#$PROJECT_ROOT/}"
