#!/usr/bin/env bash
# bench_primarybackup.sh — Run a PrimaryBackup 2-node cluster with client and report throughput.
#
# PrimaryBackup uses a fire-and-forget UDP client. The primary commits
# ClientRequest messages via the backup and reports throughput via
# [METRICS] lines on stderr (log_length increments/s).
#
# Usage: ./scripts/bench_primarybackup.sh [duration_seconds] [num_trials]
# Default: 30 seconds, 2 trials
#
# Prerequisites:
#   - liblib.so built: verus --crate-type=cdylib -C opt-level=3 --compile src/lib.rs --no-verify
#   - bin/IronProtocolServer.dll built: scons --skip-verus
#   - bin/IronPrimaryBackupClient.dll built
#   - bench/certs/ directory with IronProtocol certs (2+ servers on 127.0.0.1:4001-4002)

set -euo pipefail

DURATION=${1:-30}
TRIALS=${2:-2}
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CERT_DIR="$REPO_ROOT/bench/certs"
SERVICE="$CERT_DIR/MyRaft.IronProtocol.service.txt"

export LD_LIBRARY_PATH="$REPO_ROOT"

NUM_NODES=2
CLIENT_THREADS=1

if [ ! -f "$SERVICE" ]; then
    echo "ERROR: service file not found: $SERVICE"
    echo "Generate certs first: dotnet bin/CreateIronServiceCerts.dll outputdir=bench/certs ..."
    exit 1
fi

echo "=== PrimaryBackup Bench: ${NUM_NODES} nodes, ${CLIENT_THREADS} client thread(s), ${DURATION}s x ${TRIALS} trials ==="

for trial in $(seq 1 "$TRIALS"); do
    echo ""
    echo "--- Trial $trial ---"

    # Start servers
    PIDS=()
    METRIC_FILES=()
    for i in $(seq 1 $NUM_NODES); do
        metric_file=$(mktemp /tmp/pb_metrics_${i}_XXXXXX)
        METRIC_FILES+=("$metric_file")
        private_key="$CERT_DIR/MyRaft.IronProtocol.server${i}.private.txt"

        dotnet "$REPO_ROOT/bin/IronProtocolServer.dll" \
            "$SERVICE" "$private_key" protocol=primarybackup \
            2>"$metric_file" &
        PIDS+=($!)
    done

    # Wait for servers to initialize
    sleep 2

    # Start client (fire-and-forget UDP to primary on port 4001)
    client_out=$(mktemp /tmp/pb_client_XXXXXX)
    dotnet "$REPO_ROOT/bin/IronPrimaryBackupClient.dll" \
        ip=127.0.0.1 port=4001 nthreads=$CLIENT_THREADS duration=$DURATION \
        >"$client_out" 2>&1 &
    CLIENT_PID=$!

    echo "Running for ${DURATION}s..."
    sleep "$((DURATION + 2))"

    # Kill servers and client
    kill $CLIENT_PID "${PIDS[@]}" 2>/dev/null || true
    wait $CLIENT_PID "${PIDS[@]}" 2>/dev/null || true

    # Parse [METRICS] lines from primary (node 1)
    echo ""
    for i in $(seq 1 $NUM_NODES); do
        idx=$((i - 1))
        metric_file="${METRIC_FILES[$idx]}"
        last_line=$(grep '\[METRICS\]' "$metric_file" | tail -1 || echo "")
        if [ -n "$last_line" ]; then
            role=$(echo "$last_line" | sed 's/.*role=\([a-z]*\).*/\1/')
            log_length=$(echo "$last_line" | sed 's/.*log_length=\([0-9]*\).*/\1/')
            throughput=$(echo "$last_line" | sed 's/.*throughput=\([0-9.]*\).*/\1/')
            echo "  Node $i ($role): log_length=$log_length (last-second throughput=${throughput} ops/s)"
        else
            echo "  Node $i: no [METRICS] output found"
            if [ -s "$metric_file" ]; then
                echo "  (stderr had $(wc -l < "$metric_file") lines)"
                tail -3 "$metric_file" | sed 's/^/    /'
            fi
        fi
        rm -f "$metric_file"
    done

    # Client injection rate
    if [ -f "$client_out" ]; then
        inj=$(grep 'injection_rate' "$client_out" || echo "")
        if [ -n "$inj" ]; then
            echo "  Client: $inj"
        fi
        rm -f "$client_out"
    fi

    # Report primary throughput
    metric_file="${METRIC_FILES[0]}"
    # Already cleaned up above; use the parsed values
    echo ""

    sleep 1
done

echo ""
echo "=== Done ==="
