#!/bin/bash
# Run TLC with -dump for each shared benchmark protocol and produce
# parity JSONL exports under reports/model_check/parity/tlc/.
#
# Requirements:
#   - java (JDK 11+)
#   - TLA2TOOLS env var pointing to tla2tools.jar
#     e.g.: TLA2TOOLS=/home/shuai/tools/tla2tools.jar ./scripts/run_tlc_parity_export.sh
#
# Protocols: twophase, primarybackup, leaderelection, paxos

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WRAPPER_DIR="$REPO_ROOT/transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h"
PARSER="$REPO_ROOT/scripts/tlc_dump_to_parity_jsonl.py"
OUTPUT_DIR="$REPO_ROOT/reports/model_check/parity/tlc"
TMP_DIR=$(mktemp -d)
trap "rm -rf $TMP_DIR" EXIT

JAVA="${JAVA:-java}"
TLA2TOOLS="${TLA2TOOLS:-}"

if [ -z "$TLA2TOOLS" ]; then
    # Try common locations
    for candidate in ~/tla2tools.jar ~/tools/tla2tools.jar /usr/local/lib/tla2tools.jar; do
        if [ -f "$candidate" ]; then
            TLA2TOOLS="$candidate"
            break
        fi
    done
fi

if [ -z "$TLA2TOOLS" ] || [ ! -f "$TLA2TOOLS" ]; then
    echo "Error: tla2tools.jar not found. Set TLA2TOOLS=/path/to/tla2tools.jar" >&2
    exit 1
fi

echo "Using TLA2TOOLS=$TLA2TOOLS"
echo "Output: $OUTPUT_DIR"

# Protocol configs: (dir_name, tla_module, protocol_flag)
declare -A PROTOCOLS
PROTOCOLS[twophase]="TwoPhase_Benchmark_MC:twophase"
PROTOCOLS[primarybackup]="PrimaryBackup_Benchmark_MC:primarybackup"
PROTOCOLS[leaderelection]="LeaderElection_Benchmark_MC:leaderelection"
PROTOCOLS[paxos]="Paxos_Benchmark_MC:paxos"

SELECTED="${PROTOCOLS_FILTER:-twophase primarybackup leaderelection paxos}"

for proto in $SELECTED; do
    IFS=':' read -r module pflag <<< "${PROTOCOLS[$proto]}"
    echo ""
    echo "=== $proto ($module) ==="

    mkdir -p "$OUTPUT_DIR/$proto"
    dump_file="$TMP_DIR/${proto}_dump"

    echo "  Running TLC with -dump..."
    cd "$WRAPPER_DIR"
    if timeout 120 "$JAVA" -XX:+UseParallelGC -Xmx4g \
        -cp "$TLA2TOOLS" tlc2.TLC \
        -workers 1 \
        -dump "$dump_file" \
        "$module.tla" > "$TMP_DIR/${proto}_log" 2>&1; then
        echo "  TLC completed successfully."
    else
        status=$?
        if [ $status -eq 124 ]; then
            echo "  TLC timed out (120s). Partial dump may exist."
        else
            echo "  TLC exited with code $status."
        fi
    fi

    if [ -f "${dump_file}.dump" ]; then
        echo "  Converting dump to parity JSONL..."
        python3 "$PARSER" "${dump_file}.dump" \
            --protocol "$pflag" \
            --output "$OUTPUT_DIR/$proto/states.jsonl"
    else
        echo "  No dump file generated." >&2
    fi
done

echo ""
echo "Done. Exports in $OUTPUT_DIR/"
