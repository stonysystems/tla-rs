#!/usr/bin/env bash
# bench_pbft.sh — Run a PBFT 4-node cluster with client and report throughput.
#
# PBFT uses a fire-and-forget UDP client. The primary drives requests
# through the pre-prepare/prepare/commit pipeline and reports throughput
# via [METRICS] lines on stderr (seq_num increments/s).
#
# Usage: ./scripts/bench_pbft.sh [duration_seconds] [num_trials]
# Default: 30 seconds, 2 trials
#
# Prerequisites:
#   - liblib.so built: verus --crate-type=cdylib -C opt-level=3 --compile src/lib.rs --no-verify
#   - bin/IronProtocolServer.dll built: scons --skip-verus
#   - bin/IronPBFTClient.dll built
#   - bench/certs4/ directory with 4-node IronProtocol certs

set -euo pipefail

DURATION=${1:-30}
TRIALS=${2:-2}
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CERT_DIR="$REPO_ROOT/bench/certs4"
SERVICE="$CERT_DIR/MyPBFT.IronProtocol.service.txt"

export LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-$REPO_ROOT}"

NUM_NODES=4
CLIENT_THREADS=1

if [ ! -f "$SERVICE" ]; then
    echo "ERROR: service file not found: $SERVICE"
    echo "Generate certs: dotnet bin/CreateIronServiceCerts.dll outputdir=bench/certs4 name=MyPBFT type=IronProtocol addr1=127.0.0.1 port1=4001 addr2=127.0.0.1 port2=4002 addr3=127.0.0.1 port3=4003 addr4=127.0.0.1 port4=4004"
    exit 1
fi

echo "=== PBFT Bench: ${NUM_NODES} nodes (f=1), ${CLIENT_THREADS} client thread(s), ${DURATION}s x ${TRIALS} trials ==="

for trial in $(seq 1 "$TRIALS"); do
    echo ""
    echo "--- Trial $trial ---"

    # Start servers
    PIDS=()
    METRIC_FILES=()
    for i in $(seq 1 $NUM_NODES); do
        metric_file=$(mktemp /tmp/pbft_metrics_${i}_XXXXXX)
        METRIC_FILES+=("$metric_file")
        private_key="$CERT_DIR/MyPBFT.IronProtocol.server${i}.private.txt"

        dotnet "$REPO_ROOT/bin/IronProtocolServer.dll" \
            "$SERVICE" "$private_key" protocol=pbft \
            2>"$metric_file" &
        PIDS+=($!)
    done

    # Wait for servers to initialize
    sleep 5

    # Start client (fire-and-forget UDP to primary on port 4001)
    client_out=$(mktemp /tmp/pbft_client_XXXXXX)
    dotnet "$REPO_ROOT/bin/IronPBFTClient.dll" \
        ip=127.0.0.1 port=4001 nthreads=$CLIENT_THREADS duration=$DURATION \
        >"$client_out" 2>&1 &
    CLIENT_PID=$!

    echo "Running for ${DURATION}s..."
    sleep "$((DURATION + 2))"

    # Kill servers and client
    kill $CLIENT_PID "${PIDS[@]}" 2>/dev/null || true
    wait $CLIENT_PID "${PIDS[@]}" 2>/dev/null || true

    # Parse [METRICS] lines from each node
    echo ""
    for i in $(seq 1 $NUM_NODES); do
        idx=$((i - 1))
        metric_file="${METRIC_FILES[$idx]}"
        metric_lines=$(grep '\[METRICS\]' "$metric_file" || echo "")
        if [ -n "$metric_lines" ]; then
            last_line=$(echo "$metric_lines" | tail -1)
            role=$(echo "$last_line" | sed 's/.*role=\([a-z]*\).*/\1/')
            seq_num=$(echo "$last_line" | sed 's/.*seq_num=\([0-9]*\).*/\1/')
            # Compute average throughput from all lines (skip first/last which may be partial)
            num_lines=$(echo "$metric_lines" | wc -l)
            if [ "$num_lines" -gt 2 ]; then
                avg_throughput=$(echo "$metric_lines" | head -n $((num_lines - 1)) | tail -n +2 | \
                    sed 's/.*throughput=\([0-9.]*\).*/\1/' | \
                    awk '{sum+=$1; n++} END {if(n>0) printf "%.1f", sum/n; else print "0.0"}')
            else
                avg_throughput=$(echo "$metric_lines" | \
                    sed 's/.*throughput=\([0-9.]*\).*/\1/' | \
                    awk '{sum+=$1; n++} END {if(n>0) printf "%.1f", sum/n; else print "0.0"}')
            fi
            echo "  Node $i ($role): seq_num=$seq_num avg_throughput=${avg_throughput} ops/s ($num_lines samples)"
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

    echo ""
    sleep 1
done

echo ""
echo "=== Done ==="
