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
#   BUILD_PROFILE=release ./scripts/run_model_check_benchmarks.sh
#   TRANSPILER_BIN=transpiler/target/release/verus-transpile ./scripts/run_model_check_benchmarks.sh
#   PROTOCOLS="twophase primarybackup" ./scripts/run_model_check_benchmarks.sh  # subset

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
BUILD_PROFILE="${BUILD_PROFILE:-debug}"
if [[ "$BUILD_PROFILE" != "debug" && "$BUILD_PROFILE" != "release" ]]; then
    echo "Error: BUILD_PROFILE must be one of: debug, release (got: $BUILD_PROFILE)" >&2
    exit 1
fi
if [[ "$BUILD_PROFILE" == "release" ]]; then
    OUTPUT_DIR_DEFAULT="$PROJECT_ROOT/reports/benchmarks/source_first_release"
    TRANSPILER_BIN_DEFAULT="$PROJECT_ROOT/transpiler/target/release/verus-transpile"
    CARGO_BUILD_ARGS=(--release)
else
    OUTPUT_DIR_DEFAULT="$PROJECT_ROOT/reports/benchmarks/source_first"
    TRANSPILER_BIN_DEFAULT="$PROJECT_ROOT/transpiler/target/debug/verus-transpile"
    CARGO_BUILD_ARGS=()
fi
OUTPUT_DIR="${OUTPUT_DIR:-$OUTPUT_DIR_DEFAULT}"
TRANSPILER_BIN="${TRANSPILER_BIN:-$TRANSPILER_BIN_DEFAULT}"
PROTOCOLS="${PROTOCOLS:-twophase primarybackup leaderelection paxos}"
TIMEOUT_MS="${TIMEOUT_MS:-}"
HARD_TIMEOUT_SECS="${HARD_TIMEOUT_SECS:-}"
THREADING_MODE="${THREADING_MODE:-single-thread}"
WORKER_COUNT="${WORKER_COUNT:-1}"

if [[ -z "$HARD_TIMEOUT_SECS" && -n "$TIMEOUT_MS" ]]; then
    HARD_TIMEOUT_SECS=$(( (TIMEOUT_MS / 1000) + 120 ))
fi

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
METADATA_DIR="$OUTPUT_DIR/metadata"
mkdir -p "$METADATA_DIR"

HOSTNAME_VALUE="$(hostname 2>/dev/null || echo unknown)"
PLATFORM="$(uname -srmo 2>/dev/null || uname -a)"
CPU_COUNT="$(nproc 2>/dev/null || getconf _NPROCESSORS_ONLN 2>/dev/null || echo unknown)"
CPU_MODEL="$(
    grep -m1 'model name' /proc/cpuinfo 2>/dev/null \
    | cut -d: -f2- \
    | sed 's/^[[:space:]]*//' \
    || echo unknown
)"

if [[ "$TRANSPILER_BIN" == "$TRANSPILER_BIN_DEFAULT" ]]; then
    echo "Building transpiler binary ($TRANSPILER_BIN, profile=$BUILD_PROFILE)..."
    cargo build --manifest-path "$PROJECT_ROOT/transpiler/Cargo.toml" --bin verus-transpile "${CARGO_BUILD_ARGS[@]}"
elif [[ ! -x "$TRANSPILER_BIN" ]]; then
    echo "Error: transpiler binary not found or not executable: $TRANSPILER_BIN" >&2
    exit 1
fi

echo "=== Source-first 1-hour benchmark campaign ==="
echo "Output: ${OUTPUT_DIR#$PROJECT_ROOT/}"
echo "Build profile: $BUILD_PROFILE"
echo "Threading mode: $THREADING_MODE (workers=$WORKER_COUNT)"
echo "Transpiler binary: $TRANSPILER_BIN"
echo "Protocols: $PROTOCOLS"
if [[ -n "$TIMEOUT_MS" ]]; then
    echo "Timeout override: ${TIMEOUT_MS}ms"
fi
if [[ -n "$HARD_TIMEOUT_SECS" ]]; then
    echo "Hard timeout wrapper: ${HARD_TIMEOUT_SECS}s"
fi
echo "Machine: $PLATFORM"
echo "Host: $HOSTNAME_VALUE, CPUs: $CPU_COUNT"
echo ""

SUMMARY_FILE="$OUTPUT_DIR/SUMMARY.md"
{
    echo "# Source-first Benchmark Results"
    echo ""
    echo "Generated: $(date -u '+%Y-%m-%d %H:%M:%S UTC')"
    echo "Git rev: $(git -C "$PROJECT_ROOT" rev-parse --short HEAD)"
    echo "Build profile: $BUILD_PROFILE"
    echo "Transpiler binary: $TRANSPILER_BIN"
    echo "Threading mode: $THREADING_MODE"
    echo "Workers: $WORKER_COUNT"
    if [[ -n "$TIMEOUT_MS" ]]; then
        echo "Timeout override (ms): $TIMEOUT_MS"
    else
        echo "Timeout override (ms): model-config"
    fi
    if [[ -n "$HARD_TIMEOUT_SECS" ]]; then
        echo "Hard timeout wrapper (s): $HARD_TIMEOUT_SECS"
    else
        echo "Hard timeout wrapper (s): disabled"
    fi
    echo "Machine: $PLATFORM"
    echo "Host: $HOSTNAME_VALUE"
    echo "CPU count: $CPU_COUNT"
    echo "CPU model: $CPU_MODEL"
    echo ""
    echo "| Protocol | Result | States | Distinct | Depth | Wall time (s) |"
    echo "|----------|--------|--------|----------|-------|---------------|"
} > "$SUMMARY_FILE"

RUN_CONTEXT_FILE="$METADATA_DIR/run_context.json"
BUILD_PROFILE="$BUILD_PROFILE" \
OUTPUT_DIR="$OUTPUT_DIR" \
TRANSPILER_BIN="$TRANSPILER_BIN" \
THREADING_MODE="$THREADING_MODE" \
WORKER_COUNT="$WORKER_COUNT" \
TIMEOUT_MS="$TIMEOUT_MS" \
HARD_TIMEOUT_SECS="$HARD_TIMEOUT_SECS" \
PLATFORM="$PLATFORM" \
HOSTNAME_VALUE="$HOSTNAME_VALUE" \
CPU_COUNT="$CPU_COUNT" \
CPU_MODEL="$CPU_MODEL" \
PROTOCOLS="$PROTOCOLS" \
python3 - <<'PY' > "$RUN_CONTEXT_FILE"
import json
import os


def maybe_int(raw: str):
    if raw and raw.isdigit():
        return int(raw)
    return None


payload = {
    "build_profile": os.environ.get("BUILD_PROFILE"),
    "output_dir": os.environ.get("OUTPUT_DIR"),
    "transpiler_bin": os.environ.get("TRANSPILER_BIN"),
    "threading_mode": os.environ.get("THREADING_MODE"),
    "worker_count": maybe_int(os.environ.get("WORKER_COUNT", "")),
    "timeout_override_ms": maybe_int(os.environ.get("TIMEOUT_MS", "")),
    "hard_timeout_secs": maybe_int(os.environ.get("HARD_TIMEOUT_SECS", "")),
    "machine": {
        "platform": os.environ.get("PLATFORM"),
        "hostname": os.environ.get("HOSTNAME_VALUE"),
        "cpu_count": maybe_int(os.environ.get("CPU_COUNT", "")),
        "cpu_model": os.environ.get("CPU_MODEL"),
    },
    "protocols": [p for p in os.environ.get("PROTOCOLS", "").split() if p],
}
print(json.dumps(payload, indent=2))
PY

for proto in $PROTOCOLS; do
    input="${PROTOCOL_INPUT[$proto]}"
    types="${PROTOCOL_TYPES[$proto]}"
    model="${FIXTURE_DIR}/${PROTOCOL_MODEL[$proto]}"

    if [[ ! -f "$model" ]]; then
        echo "SKIP: $proto — model config not found: $model"
        continue
    fi

    artifact="$OUTPUT_DIR/${proto}_benchmark.json"
    if [[ -n "$TIMEOUT_MS" ]]; then
        run_timeout_label="${TIMEOUT_MS}ms timeout override"
    else
        run_timeout_label="model-config timeout"
    fi
    echo "Running: $proto ($run_timeout_label) ..."
    start_time=$(date +%s)

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
    cmd_escaped="$(printf '%q ' "${run_cmd[@]}")"
    run_exit_code=0

    (
        cd "$PROJECT_ROOT"
        if [[ -n "$HARD_TIMEOUT_SECS" ]]; then
            timeout "$HARD_TIMEOUT_SECS" "${run_cmd[@]}"
        else
            "${run_cmd[@]}"
        fi
    ) > "$artifact" 2>&1 || run_exit_code=$?

    end_time=$(date +%s)
    wall_secs=$((end_time - start_time))
    run_exit_code="${run_exit_code:-0}"

    # Extract result fields from JSON (fields are in top-level "result",
    # "stop_reason", and nested "summary.states", "summary.depth")
    result=$(python3 -c "
import json, sys
try:
    d = json.load(open('$artifact'))
    r = d.get('result', 'error')
    sr = d.get('stop_reason', '')
    s = d.get('summary', {})
    print(f\"{r}({sr})|{sr}|{s.get('states','?')}|{s.get('states','?')}|{s.get('depth','?')}|{s.get('transitions','?')}|{s.get('elapsed_ms','?')}\")
except: print('error|error|?|?|?|?|?')
" 2>/dev/null || echo "error|error|?|?|?|?|?")
    IFS='|' read -r result stop_reason states distinct depth transitions elapsed_ms <<< "$result"
    if [[ "$run_exit_code" -eq 124 && "$result" == error* ]]; then
        result="timeout_reached(HardTimeout)"
        stop_reason="HardTimeout"
    fi

    echo "  Done: $result ($states states, ${wall_secs}s)"
    echo "| $proto | $result | $states | $distinct | $depth | $wall_secs |" >> "$SUMMARY_FILE"

    RUN_META_FILE="$METADATA_DIR/${proto}_benchmark.meta.json"
    BUILD_PROFILE="$BUILD_PROFILE" \
    PROTOCOL="$proto" \
    OUTPUT_ARTIFACT="${artifact#$PROJECT_ROOT/}" \
    ARTIFACT_FILE="$artifact" \
    COMMAND="$cmd_escaped" \
    THREADING_MODE="$THREADING_MODE" \
    WORKER_COUNT="$WORKER_COUNT" \
    TIMEOUT_MS="$TIMEOUT_MS" \
    HARD_TIMEOUT_SECS="$HARD_TIMEOUT_SECS" \
    PLATFORM="$PLATFORM" \
    HOSTNAME_VALUE="$HOSTNAME_VALUE" \
    CPU_COUNT="$CPU_COUNT" \
    CPU_MODEL="$CPU_MODEL" \
    RESULT="$result" \
    STOP_REASON="$stop_reason" \
    STATES="$states" \
    TRANSITIONS="$transitions" \
    DEPTH="$depth" \
    WALL_SECS="$wall_secs" \
    ELAPSED_MS="$elapsed_ms" \
    python3 - <<'PY' > "$RUN_META_FILE"
import json
import os


def maybe_int(raw: str):
    if raw and raw.isdigit():
        return int(raw)
    return None


payload = {
    "protocol": os.environ.get("PROTOCOL"),
    "build_profile": os.environ.get("BUILD_PROFILE"),
    "artifact": os.environ.get("OUTPUT_ARTIFACT"),
    "command": os.environ.get("COMMAND", "").strip(),
    "threading_mode": os.environ.get("THREADING_MODE"),
    "worker_count": maybe_int(os.environ.get("WORKER_COUNT", "")),
    "timeout_override_ms": maybe_int(os.environ.get("TIMEOUT_MS", "")),
    "hard_timeout_secs": maybe_int(os.environ.get("HARD_TIMEOUT_SECS", "")),
    "machine": {
        "platform": os.environ.get("PLATFORM"),
        "hostname": os.environ.get("HOSTNAME_VALUE"),
        "cpu_count": maybe_int(os.environ.get("CPU_COUNT", "")),
        "cpu_model": os.environ.get("CPU_MODEL"),
    },
    "result": os.environ.get("RESULT"),
    "stop_reason": os.environ.get("STOP_REASON"),
    "summary": {
        "states": maybe_int(os.environ.get("STATES", "")),
        "transitions": maybe_int(os.environ.get("TRANSITIONS", "")),
        "depth": maybe_int(os.environ.get("DEPTH", "")),
        "wall_secs": maybe_int(os.environ.get("WALL_SECS", "")),
        "elapsed_ms": maybe_int(os.environ.get("ELAPSED_MS", "")),
    },
}

artifact_file = os.environ.get("ARTIFACT_FILE", "")
if artifact_file and os.path.exists(artifact_file):
    try:
        artifact = json.load(open(artifact_file))
        summary = artifact.get("summary") or {}
        timing = summary.get("timing")
        if isinstance(timing, dict):
            payload["summary"]["timing"] = timing
        branch_telemetry = summary.get("branch_telemetry")
        if isinstance(branch_telemetry, list):
            payload["summary"]["branch_telemetry"] = branch_telemetry
    except Exception:
        pass
print(json.dumps(payload, indent=2))
PY
done

echo "" >> "$SUMMARY_FILE"
echo "Benchmark configs: \`transpiler/tests/model_check_fixtures/benchmarks_1h/\`" >> "$SUMMARY_FILE"
echo "Run context metadata: \`${RUN_CONTEXT_FILE#$PROJECT_ROOT/}\`" >> "$SUMMARY_FILE"
echo "Per-run metadata: \`${METADATA_DIR#$PROJECT_ROOT/}/*_benchmark.meta.json\`" >> "$SUMMARY_FILE"

echo ""
echo "Summary written to: ${SUMMARY_FILE#$PROJECT_ROOT/}"
echo "Individual artifacts in: ${OUTPUT_DIR#$PROJECT_ROOT/}"
