#!/usr/bin/env bash
# Run TLC model-check 1-hour benchmarks for the 4 benchmark protocols.
#
# Requires:
#   - Java 11+ (set JAVA to override)
#   - tla2tools.jar (set TLA2TOOLS to the path)
#
# Usage:
#   TLA2TOOLS=/path/to/tla2tools.jar ./scripts/run_tlc_benchmarks.sh
#   JAVA=/usr/lib/jvm/java-11-openjdk-amd64/bin/java TLA2TOOLS=~/tla2tools.jar ./scripts/run_tlc_benchmarks.sh
#   PROTOCOLS="twophase paxos" TLA2TOOLS=~/tla2tools.jar ./scripts/run_tlc_benchmarks.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
OUTPUT_DIR="${OUTPUT_DIR:-$PROJECT_ROOT/reports/benchmarks/tlc}"
JAVA="${JAVA:-java}"
TLA2TOOLS="${TLA2TOOLS:-}"
PROTOCOLS="${PROTOCOLS:-twophase primarybackup leaderelection paxos}"
TIMEOUT_SECS="${TIMEOUT_SECS:-3600}"
TLC_WORKERS="${TLC_WORKERS:-auto}"

TLA_DIR="$PROJECT_ROOT/transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h"

# Protocol TLA+ module names
declare -A PROTOCOL_MODULE=(
    [twophase]="TwoPhase_Benchmark_MC"
    [primarybackup]="PrimaryBackup_Benchmark_MC"
    [leaderelection]="LeaderElection_Benchmark_MC"
    [paxos]="Paxos_Benchmark_MC"
)

# Check prerequisites
if [[ -z "$TLA2TOOLS" ]]; then
    echo "Error: TLA2TOOLS not set. Provide path to tla2tools.jar." >&2
    echo "  TLA2TOOLS=/path/to/tla2tools.jar $0" >&2
    exit 1
fi

if [[ ! -f "$TLA2TOOLS" ]]; then
    echo "Error: tla2tools.jar not found at $TLA2TOOLS" >&2
    exit 1
fi

# Check Java version
java_version=$("$JAVA" -version 2>&1 | head -1 | grep -oP '(?<=")\d+' | head -1 || echo "0")
if [[ "$java_version" -lt 11 ]]; then
    echo "Error: Java 11+ required. Found version $java_version." >&2
    echo "  Set JAVA=/path/to/java11+ to override." >&2
    exit 1
fi

mkdir -p "$OUTPUT_DIR"

echo "=== TLC 1-hour benchmark campaign ==="
echo "Java: $JAVA (version $java_version)"
echo "TLA2 tools: $TLA2TOOLS"
echo "Workers: $TLC_WORKERS"
echo "Timeout: ${TIMEOUT_SECS}s per protocol"
echo "Output: ${OUTPUT_DIR#$PROJECT_ROOT/}"
echo "Protocols: $PROTOCOLS"
echo ""

SUMMARY_FILE="$OUTPUT_DIR/SUMMARY.md"
{
    echo "# TLC Benchmark Results"
    echo ""
    echo "Generated: $(date -u '+%Y-%m-%d %H:%M:%S UTC')"
    echo "Git rev: $(git -C "$PROJECT_ROOT" rev-parse --short HEAD)"
    echo "Java: $java_version, Workers: $TLC_WORKERS"
    echo ""
    echo "| Protocol | Result | States | Distinct | Depth | Wall time (s) |"
    echo "|----------|--------|--------|----------|-------|---------------|"
} > "$SUMMARY_FILE"

for proto in $PROTOCOLS; do
    module="${PROTOCOL_MODULE[$proto]}"
    tla_file="$TLA_DIR/${module}.tla"
    cfg_file="$TLA_DIR/${module}.cfg"

    if [[ ! -f "$tla_file" ]]; then
        echo "SKIP: $proto — TLA+ file not found: $tla_file"
        continue
    fi
    if [[ ! -f "$cfg_file" ]]; then
        echo "SKIP: $proto — cfg file not found: $cfg_file"
        continue
    fi

    log_file="$OUTPUT_DIR/${proto}_benchmark.log"
    echo "Running: $proto (${TIMEOUT_SECS}s timeout) ..."
    start_time=$(date +%s)

    # Run TLC with timeout
    (
        cd "$TLA_DIR"
        timeout "$TIMEOUT_SECS" "$JAVA" \
            -XX:+UseParallelGC \
            -Xmx4g \
            -cp "$TLA2TOOLS" tlc2.TLC \
            -workers "$TLC_WORKERS" \
            -config "${module}.cfg" \
            "${module}.tla"
    ) > "$log_file" 2>&1 || true

    end_time=$(date +%s)
    wall_secs=$((end_time - start_time))

    # Parse TLC output for stats
    result="unknown"
    if grep -q "Model checking completed. No error has been found." "$log_file" 2>/dev/null; then
        result="pass"
    elif grep -q "Error:" "$log_file" 2>/dev/null; then
        result="error"
    elif [[ $wall_secs -ge $TIMEOUT_SECS ]]; then
        result="timeout"
    fi

    parsed_stats=$(python3 - "$log_file" <<'PY' 2>/dev/null || echo "?|?|?"
import re, sys
path = sys.argv[1]
states = "?"
distinct = "?"
depth = "?"
with open(path, "r", encoding="utf-8", errors="ignore") as fh:
    for line in fh:
        pair = re.search(r'([0-9][0-9,]*) states generated.*?([0-9][0-9,]*) distinct states found', line)
        if pair:
            states = pair.group(1).replace(",", "")
            distinct = pair.group(2).replace(",", "")
        depth_match = re.search(r'The depth of the complete state graph search is ([0-9][0-9,]*)', line)
        if depth_match:
            depth = depth_match.group(1).replace(",", "")
print(f"{states}|{distinct}|{depth}")
PY
)
    IFS='|' read -r states distinct depth <<< "$parsed_stats"

    echo "  Done: $result ($states states, ${wall_secs}s)"
    echo "| $proto | $result | $states | $distinct | $depth | $wall_secs |" >> "$SUMMARY_FILE"
done

echo "" >> "$SUMMARY_FILE"
echo "TLC wrappers: \`transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/\`" >> "$SUMMARY_FILE"

echo ""
echo "Summary written to: ${SUMMARY_FILE#$PROJECT_ROOT/}"
echo "Individual logs in: ${OUTPUT_DIR#$PROJECT_ROOT/}"
