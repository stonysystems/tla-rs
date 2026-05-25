#!/usr/bin/env bash
# bench_epaxos.sh — Run an EPaxos 3-node cluster and report throughput.
#
# EPaxos is self-driving (no client needed). Each server proposes commands
# via try_propose() in a round-robin loop. The host prints periodic
# [METRICS] lines to stderr with committed count and throughput.
#
# Usage: ./scripts/bench_epaxos.sh [duration_seconds] [num_trials]
# Default: 30 seconds, 2 trials
#
# Prerequisites:
#   - liblib.so built: verus --crate-type=cdylib -C opt-level=3 --compile src/lib.rs --no-verify
#   - bin/IronProtocolServer.dll built: scons --skip-verus
#   - bench/certs/ directory with IronProtocol certs (3 servers on 127.0.0.1:4001-4003)

set -euo pipefail

DURATION=${1:-30}
TRIALS=${2:-2}
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CERT_DIR="$REPO_ROOT/bench/certs"
SERVICE="$CERT_DIR/MyRaft.IronProtocol.service.txt"

export LD_LIBRARY_PATH="$REPO_ROOT"

NUM_NODES=3

if [ ! -f "$SERVICE" ]; then
    echo "ERROR: service file not found: $SERVICE"
    echo "Generate certs first: dotnet bin/CreateIronServiceCerts.dll outputdir=bench/certs ..."
    exit 1
fi

echo "=== EPaxos Bench: ${NUM_NODES} nodes, ${DURATION}s x ${TRIALS} trials ==="

for trial in $(seq 1 "$TRIALS"); do
    echo ""
    echo "--- Trial $trial ---"

    # Start servers, capture stderr (where [METRICS] goes) to temp files
    PIDS=()
    METRIC_FILES=()
    for i in $(seq 1 $NUM_NODES); do
        metric_file=$(mktemp /tmp/epaxos_metrics_${i}_XXXXXX)
        METRIC_FILES+=("$metric_file")
        private_key="$CERT_DIR/MyRaft.IronProtocol.server${i}.private.txt"

        dotnet "$REPO_ROOT/bin/IronProtocolServer.dll" \
            "$SERVICE" "$private_key" protocol=epaxos \
            2>"$metric_file" &
        PIDS+=($!)
    done

    # Wait for all servers to reach READY state
    sleep 2

    echo "Running for ${DURATION}s..."
    sleep "$DURATION"

    # Kill servers
    for pid in "${PIDS[@]}"; do
        kill "$pid" 2>/dev/null || true
    done
    wait "${PIDS[@]}" 2>/dev/null || true

    # Parse [METRICS] lines from each server
    echo ""
    total_committed=0
    for i in $(seq 1 $NUM_NODES); do
        idx=$((i - 1))
        metric_file="${METRIC_FILES[$idx]}"
        last_line=$(grep '\[METRICS\]' "$metric_file" | tail -1 || echo "")
        if [ -n "$last_line" ]; then
            committed=$(echo "$last_line" | sed 's/.*committed=\([0-9]*\).*/\1/')
            throughput=$(echo "$last_line" | sed 's/.*throughput=\([0-9.]*\).*/\1/')
            echo "  Node $i: committed=$committed (last-second throughput=${throughput} ops/s)"
            total_committed=$((total_committed + committed))
        else
            echo "  Node $i: no [METRICS] output found"
            if [ -s "$metric_file" ]; then
                echo "  (stderr had $(wc -l < "$metric_file") lines)"
                tail -3 "$metric_file" | sed 's/^/    /'
            fi
        fi
        rm -f "$metric_file"
    done

    # In EPaxos, committed_count is per-node (each node commits as leader).
    # The aggregate is the total cluster committed instances.
    if [ "$total_committed" -gt 0 ]; then
        aggregate=$(echo "scale=1; $total_committed / $DURATION" | bc)
        per_node=$(echo "scale=1; $total_committed / $NUM_NODES / $DURATION" | bc)
        echo ""
        echo "  Aggregate: total_committed=$total_committed over ${DURATION}s"
        echo "  Cluster throughput: ${aggregate} commits/s (${per_node} per node)"
    else
        echo ""
        echo "  Aggregate: no commits recorded"
    fi

    sleep 1
done

echo ""
echo "=== Done ==="
