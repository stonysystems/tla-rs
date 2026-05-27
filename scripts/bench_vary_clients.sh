#!/usr/bin/env bash
# bench_vary_clients.sh — Sweep client thread count for 4 protocols.
#
# Protocols: rsl, raft, epaxos, pbft
# Client counts: 1, 2, 4, 8, 16, 32, 64
# Duration: 30s per run, 2 trials per (protocol, client_n)
#
# For RSL: max_batch_size is set equal to client_n by editing
# src/implementation/RSL/cparameters.rs and rebuilding liblib.so.
#
# Flags:
#   --fresh      Clobber results.csv (otherwise appends)
#   --optimized  Build RSL with --cfg 'feature="optimized_rsl"' and
#                tag results as "rsl-opt" in CSV (Phase 46.4)
#
# Output: bench/vary_clients/results.csv with columns
#   protocol,client_n,trial,throughput_ops_sec,avg_latency_ms,timestamp,note

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

OUT_DIR="$REPO_ROOT/bench/vary_clients"
RESULTS_CSV="$OUT_DIR/results.csv"
RUN_LOG_DIR="$OUT_DIR/logs"
mkdir -p "$OUT_DIR" "$RUN_LOG_DIR"

export LD_LIBRARY_PATH="$REPO_ROOT"
source "$HOME/.bashrc" 2>/dev/null || true

DURATION=30
TRIALS=2
CLIENT_COUNTS=(1 2 4 8 16 32 64)
PROTOCOLS=(rsl raft epaxos pbft)

VERUS=/home/users/zihao/verus/verus
PARAMS_FILE="$REPO_ROOT/src/implementation/RSL/cparameters.rs"

# --optimized: build RSL with optimized_rsl feature, tag results as rsl-opt
OPTIMIZED_RSL=false
RSL_PROTOCOL_TAG="rsl"
VERUS_EXTRA_FLAGS=""

# Parse flags
POSITIONAL_ARGS=()
for arg in "$@"; do
    case $arg in
        --optimized)
            OPTIMIZED_RSL=true
            RSL_PROTOCOL_TAG="rsl-opt"
            VERUS_EXTRA_FLAGS="--cfg feature=\"optimized_rsl\""
            ;;
        *)
            POSITIONAL_ARGS+=("$arg")
            ;;
    esac
done

# Initialize CSV (preserve existing rows by default; clobber with --fresh)
if [ "${POSITIONAL_ARGS[0]:-}" = "--fresh" ] || [ ! -f "$RESULTS_CSV" ]; then
    echo "protocol,client_n,trial,throughput_ops_sec,avg_latency_ms,timestamp,note" > "$RESULTS_CSV"
fi

# --- helpers ---
kill_servers() {
    pkill -9 -f IronProtocolServer 2>/dev/null || true
    pkill -9 -f IronRSLServer 2>/dev/null || true
    pkill -9 -f IronGenericClient 2>/dev/null || true
    pkill -9 -f IronRSLClient 2>/dev/null || true
    sleep 2
}

# Edit RSL max_batch_size and rebuild liblib.so. Returns 0 on success.
rebuild_rsl_with_batch() {
    local batch=$1
    # The line is: `        max_batch_size: 32,` (or similar value)
    # Use sed in-place; match the field name to avoid touching anything else.
    sed -i "s/^\(\s*max_batch_size:\)\s*[0-9]\+,/\1 $batch,/" "$PARAMS_FILE"
    local got
    got=$(grep -E "^\s*max_batch_size:\s*[0-9]+," "$PARAMS_FILE" | head -1 | tr -d ' ' | tr -d ',' | awk -F: '{print $2}')
    if [ "$got" != "$batch" ]; then
        echo "ERROR: sed did not set max_batch_size to $batch (got '$got')" >&2
        return 1
    fi
    echo "Rebuilding liblib.so with max_batch_size=$batch${OPTIMIZED_RSL:+ (optimized_rsl)}..."
    # shellcheck disable=SC2086
    "$VERUS" --crate-type=cdylib -C opt-level=3 --compile src/lib.rs --no-verify $VERUS_EXTRA_FLAGS > "$RUN_LOG_DIR/rebuild_batch${batch}.log" 2>&1
    local rc=$?
    if [ $rc -ne 0 ]; then
        echo "ERROR: rebuild failed (rc=$rc); see $RUN_LOG_DIR/rebuild_batch${batch}.log" >&2
        return 1
    fi
    return 0
}

# Parse "throughput <N>(.<F>)? (ops/sec)? | avg latency ms <X>" → outputs "TPUT LAT"
parse_throughput_line() {
    local line="$1"
    local tput lat
    tput=$(echo "$line" | sed -nE 's/.*throughput[[:space:]]+([0-9.]+).*latency.*/\1/p')
    lat=$(echo "$line"  | sed -nE 's/.*latency ms[[:space:]]+([0-9.]+).*/\1/p')
    echo "${tput:-0} ${lat:-0}"
}

# Run one trial. Args: protocol client_n trial → echoes "TPUT LAT NOTE"
run_one_trial_rsl() {
    local client_n=$1 trial=$2
    local cert_dir="$REPO_ROOT/bench/certs_udp"
    local svc="$cert_dir/MyRSL.IronRSL.service.txt"
    local client_log="$RUN_LOG_DIR/rsl_c${client_n}_t${trial}.client.log"
    local server_logs=()

    for i in 1 2 3; do
        local sl="$RUN_LOG_DIR/rsl_c${client_n}_t${trial}.server${i}.log"
        server_logs+=("$sl")
        dotnet "$REPO_ROOT/bin/IronRSLServerUDP.dll" \
            "$svc" "$cert_dir/MyRSL.IronRSL.server${i}.private.txt" \
            > "$sl" 2>&1 &
    done
    sleep 5
    # RSL effective bench duration adds a fixed 8s discount; pass duration as-is.
    timeout $((DURATION + 30)) dotnet "$REPO_ROOT/bin/IronRSLClientUDP.dll" \
        ip1=127.0.0.1 port1=4001 \
        ip2=127.0.0.1 port2=4002 \
        ip3=127.0.0.1 port3=4003 \
        nthreads=$client_n duration=$((DURATION + 8)) \
        > "$client_log" 2>&1
    local rc=$?
    kill_servers
    local line
    line=$(grep -E "^throughput " "$client_log" | tail -1)
    if [ -z "$line" ]; then
        echo "0 0 client_no_output_rc${rc}"
        return
    fi
    local pair note
    pair=$(parse_throughput_line "$line")
    note="ok"
    echo "$pair $note"
}

run_one_trial_generic() {
    local protocol=$1 client_n=$2 trial=$3 num_nodes=$4 cert_dir=$5
    local svc="$cert_dir/MyRaft.IronProtocol.service.txt"
    local client_log="$RUN_LOG_DIR/${protocol}_c${client_n}_t${trial}.client.log"
    for i in $(seq 1 $num_nodes); do
        local sl="$RUN_LOG_DIR/${protocol}_c${client_n}_t${trial}.server${i}.log"
        dotnet "$REPO_ROOT/bin/IronProtocolServer.dll" \
            "$svc" "$cert_dir/MyRaft.IronProtocol.server${i}.private.txt" \
            protocol=$protocol \
            > "$sl" 2>&1 &
    done
    sleep 3
    local port_args=""
    for i in $(seq 1 $num_nodes); do
        port_args="$port_args port${i}=$((4000 + i))"
    done
    timeout $((DURATION + 30)) dotnet "$REPO_ROOT/bin/IronGenericClient.dll" \
        protocol=$protocol nservers=$num_nodes nthreads=$client_n \
        duration=$DURATION $port_args \
        > "$client_log" 2>&1
    local rc=$?
    kill_servers
    local line
    line=$(grep -E "^throughput " "$client_log" | tail -1)
    if [ -z "$line" ]; then
        echo "0 0 client_no_output_rc${rc}"
        return
    fi
    local pair note
    pair=$(parse_throughput_line "$line")
    note="ok"
    echo "$pair $note"
}

run_one_trial() {
    local protocol=$1 client_n=$2 trial=$3
    case $protocol in
        rsl)   run_one_trial_rsl    "$client_n" "$trial" ;;
        raft)  run_one_trial_generic raft   "$client_n" "$trial" 3 "$REPO_ROOT/bench/certs" ;;
        epaxos)run_one_trial_generic epaxos "$client_n" "$trial" 3 "$REPO_ROOT/bench/certs" ;;
        pbft)  run_one_trial_generic pbft   "$client_n" "$trial" 4 "$REPO_ROOT/bench/certs_4node" ;;
        *) echo "0 0 unknown_protocol_${protocol}" ;;
    esac
}

# --- main loop ---
echo "=== Vary-client-number bench ==="
if [ "$OPTIMIZED_RSL" = true ]; then
    echo "Mode: OPTIMIZED RSL (feature=optimized_rsl, tag=$RSL_PROTOCOL_TAG)"
fi
echo "Protocols: ${PROTOCOLS[*]}"
echo "Client counts: ${CLIENT_COUNTS[*]}"
echo "Duration per trial: ${DURATION}s, trials per cell: ${TRIALS}"
echo "Output CSV: $RESULTS_CSV"
echo "Run logs: $RUN_LOG_DIR/"
echo

for protocol in "${PROTOCOLS[@]}"; do
    for client_n in "${CLIENT_COUNTS[@]}"; do
        echo "===== $protocol client_n=$client_n ====="

        # RSL rebuild path
        csv_protocol="$protocol"
        if [ "$protocol" = "rsl" ]; then
            csv_protocol="$RSL_PROTOCOL_TAG"
            if ! rebuild_rsl_with_batch "$client_n"; then
                ts=$(date -Iseconds)
                for trial in $(seq 1 $TRIALS); do
                    echo "$csv_protocol,$client_n,$trial,0,0,$ts,rebuild_failed_skip" >> "$RESULTS_CSV"
                done
                echo "  SKIPPED (rebuild failed)"
                continue
            fi
        fi

        kill_servers
        for trial in $(seq 1 $TRIALS); do
            echo "  trial $trial..."
            ts=$(date -Iseconds)
            read -r tput lat note <<< "$(run_one_trial "$protocol" "$client_n" "$trial")"
            echo "$csv_protocol,$client_n,$trial,$tput,$lat,$ts,$note" >> "$RESULTS_CSV"
            printf "    -> tput=%s ops/sec lat=%s ms note=%s\n" "$tput" "$lat" "$note"
            # PBFT inter-trial spacing (Q4 A: hard kill + extra sleep)
            if [ "$protocol" = "pbft" ]; then
                kill_servers
                sleep 5
            fi
        done
        kill_servers
    done
done

# Restore RSL params to default 32 after run
echo
echo "Restoring RSL max_batch_size to 32..."
sed -i "s/^\(\s*max_batch_size:\)\s*[0-9]\+,/\1 32,/" "$PARAMS_FILE"

echo
echo "=== DONE ==="
echo "Results: $RESULTS_CSV"
echo
echo "Summary (per-cell avg of trials):"
awk -F, 'NR>1 {
    key=$1","$2; sum[key]+=$4; cnt[key]++; latsum[key]+=$5
}
END {
    for (k in sum) printf "  %-25s avg_tput=%.1f avg_lat_ms=%.2f n=%d\n", k, sum[k]/cnt[k], latsum[k]/cnt[k], cnt[k]
}' "$RESULTS_CSV" | sort
