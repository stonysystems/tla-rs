#!/usr/bin/env bash
# bench_generic.sh — Run a protocol cluster with IronGenericClient and report throughput.
#
# Usage: ./scripts/bench_generic.sh <protocol> [duration_seconds] [num_trials] [nthreads]
#   protocol: raft, pb, pbft, epaxos
#   Default: 30 seconds, 2 trials, 1 thread
#
# Prerequisites:
#   - liblib.so built (optimized)
#   - bin/IronProtocolServer.dll + bin/IronGenericClient.dll built

set -euo pipefail

PROTOCOL=${1:?Usage: bench_generic.sh <protocol> [duration] [trials] [nthreads]}
DURATION=${2:-30}
TRIALS=${3:-2}
NTHREADS=${4:-1}
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

export LD_LIBRARY_PATH="$REPO_ROOT"

# Protocol-specific config
case "$PROTOCOL" in
    raft)
        NUM_NODES=3
        CERT_DIR="$REPO_ROOT/bench/certs"
        ;;
    pb|primarybackup)
        NUM_NODES=2
        CERT_DIR="$REPO_ROOT/bench/certs"
        PROTOCOL_ARG="primarybackup"
        ;;
    pbft)
        NUM_NODES=4
        CERT_DIR="$REPO_ROOT/bench/certs_4node"
        ;;
    epaxos)
        NUM_NODES=3
        CERT_DIR="$REPO_ROOT/bench/certs"
        ;;
    *)
        echo "Unknown protocol: $PROTOCOL"
        echo "Supported: raft, pb, pbft, epaxos"
        exit 1
        ;;
esac

PROTOCOL_ARG=${PROTOCOL_ARG:-$PROTOCOL}
SERVICE="$CERT_DIR/MyRaft.IronProtocol.service.txt"

if [ ! -f "$SERVICE" ]; then
    echo "ERROR: service file not found: $SERVICE"
    exit 1
fi

echo "=== $PROTOCOL bench: ${NUM_NODES} nodes, ${NTHREADS} client thread(s), ${DURATION}s x ${TRIALS} trials ==="

# Build port args for client
PORT_ARGS=""
for i in $(seq 1 $NUM_NODES); do
    PORT_ARGS="$PORT_ARGS port${i}=$((4000 + i))"
done

for trial in $(seq 1 "$TRIALS"); do
    echo ""
    echo "--- Trial $trial ---"

    # Start servers
    PIDS=()
    LOG_FILES=()
    for i in $(seq 1 $NUM_NODES); do
        log_file=$(mktemp /tmp/bench_${PROTOCOL}_${i}_XXXXXX)
        LOG_FILES+=("$log_file")
        private_key="$CERT_DIR/MyRaft.IronProtocol.server${i}.private.txt"

        dotnet "$REPO_ROOT/bin/IronProtocolServer.dll" \
            "$SERVICE" "$private_key" protocol=$PROTOCOL_ARG \
            2>"$log_file" &
        PIDS+=($!)
    done

    # Wait for servers to initialize
    sleep 3

    # Start client
    client_out=$(mktemp /tmp/bench_client_${PROTOCOL}_XXXXXX)
    dotnet "$REPO_ROOT/bin/IronGenericClient.dll" \
        protocol=$PROTOCOL nservers=$NUM_NODES nthreads=$NTHREADS \
        duration=$DURATION $PORT_ARGS \
        >"$client_out" 2>&1 &
    CLIENT_PID=$!

    echo "Running for ${DURATION}s..."
    wait $CLIENT_PID 2>/dev/null || true

    # Kill servers
    kill "${PIDS[@]}" 2>/dev/null || true
    wait "${PIDS[@]}" 2>/dev/null || true

    # Show client output (contains throughput)
    echo ""
    echo "Client output:"
    cat "$client_out"

    # Show server metrics if any
    for i in $(seq 1 $NUM_NODES); do
        idx=$((i - 1))
        log_file="${LOG_FILES[$idx]}"
        metric_lines=$(grep '\[METRICS\]' "$log_file" 2>/dev/null | tail -1 || echo "")
        if [ -n "$metric_lines" ]; then
            echo "  Server $i metrics: $metric_lines"
        fi
        rm -f "$log_file"
    done

    rm -f "$client_out"
    sleep 1
done

echo ""
echo "=== Done ==="
