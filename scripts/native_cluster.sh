#!/usr/bin/env bash
# Shared native-only cluster lifecycle. Callers own EXIT/INT/TERM traps.
NATIVE_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
NATIVE_BIN="${BIN_DIR:-$NATIVE_ROOT/bin}"
PIDS=()
CLIENT_PID=""

native_fail() { printf 'ERROR: %s\n' "$*" >&2; exit 1; }
native_positive() { [[ "$2" =~ ^[1-9][0-9]*$ ]] || native_fail "$1 must be a positive integer"; }
native_require() {
    local binary
    if [[ "${BUILD:-0}" == 1 ]]; then "$NATIVE_ROOT/scripts/build_lion_runtime.sh"; fi
    for binary in tla-rs-config tla-rs-server tla-rs-client; do
        [[ -x "$NATIVE_BIN/$binary" ]] || native_fail "missing $NATIVE_BIN/$binary; run scripts/build_lion_runtime.sh (or BUILD=1)"
    done
    command -v timeout >/dev/null || native_fail 'timeout is required'
}

native_stop() {
    local pid deadline
    if [[ -n "$CLIENT_PID" ]]; then
        kill "$CLIENT_PID" 2>/dev/null || true
        wait "$CLIENT_PID" 2>/dev/null || true
        CLIENT_PID=""
    fi
    for pid in "${PIDS[@]}"; do kill "$pid" 2>/dev/null || true; done
    deadline=$((SECONDS + 3))
    for pid in "${PIDS[@]}"; do
        while kill -0 "$pid" 2>/dev/null && (( SECONDS < deadline )); do sleep 0.05; done
        if kill -0 "$pid" 2>/dev/null; then kill -KILL "$pid" 2>/dev/null || true; fi
        wait "$pid" 2>/dev/null || true
    done
    PIDS=()
}

native_ready() {
    local pid=$1 log=$2 deadline=$((SECONDS + ${READY_TIMEOUT:-15}))
    while (( SECONDS < deadline )); do
        if ! kill -0 "$pid" 2>/dev/null; then cat "$log" >&2; native_fail "server $pid exited before readiness"; fi
        if grep -Fq '[[READY]]' "$log"; then return; fi
        sleep 0.1
    done
    cat "$log" >&2
    native_fail "server $pid not ready; log: $log"
}

native_alive() {
    local pid
    for pid in "${PIDS[@]}"; do kill -0 "$pid" 2>/dev/null || native_fail "server $pid exited unexpectedly"; done
}

native_launch_node() {
    local node=$1 suffix=${2:-} log="$CLUSTER_DIR/server$1${2:-}.log"
    local transport_args=()
    [[ -z "${TRANSPORT:-}" ]] || transport_args=("transport=$TRANSPORT")
    "$NATIVE_BIN/tla-rs-server" "$SERVICE" "$CLUSTER_DIR/Cluster.$SERVICE_TYPE.server$node.private.txt" \
        "protocol=$PROTOCOL" "${transport_args[@]}" verbose=false >"$log" 2>&1 &
    NODE_PID=$!
    PIDS+=("$NODE_PID")
    native_ready "$NODE_PID" "$log"
}

# Sets SERVICE, SERVICE_TYPE, CLUSTER_DIR, PROTOCOL and owned PIDS.
native_start() {
    PROTOCOL=$1 CLUSTER_DIR=$2
    local base=$3 nodes=3 node
    [[ "$PROTOCOL" != pbft ]] || nodes=4
    native_positive BASE_PORT "$base"
    (( base + nodes - 1 <= 65535 )) || native_fail 'BASE_PORT out of range'
    SERVICE_TYPE=IronProtocol
    [[ "$PROTOCOL" != rsl ]] || SERVICE_TYPE=IronRSL
    mkdir -p "$CLUSTER_DIR"
    local args=("outputdir=$CLUSTER_DIR" name=Cluster "type=$SERVICE_TYPE" "usessl=${USE_SSL:-false}")
    for ((node=1; node<=nodes; node++)); do
        args+=("addr$node=127.0.0.1" "port$node=$((base + node - 1))")
    done
    "$NATIVE_BIN/tla-rs-config" "${args[@]}" >"$CLUSTER_DIR/config.log" 2>&1 || {
        cat "$CLUSTER_DIR/config.log" >&2; native_fail 'native configuration failed';
    }
    SERVICE="$CLUSTER_DIR/Cluster.$SERVICE_TYPE.service.txt"
    for ((node=1; node<=nodes; node++)); do native_launch_node "$node"; done
}

native_workload() {
    local log=$1 threads=$2 duration=$3 warmup=$4 service=${5:-$SERVICE}
    local transport_args=()
    [[ -z "${TRANSPORT:-}" ]] || transport_args=("transport=$TRANSPORT")
    timeout --signal=TERM --kill-after=3 "$((duration + warmup + 20))" \
        "$NATIVE_BIN/tla-rs-client" "protocol=$PROTOCOL" "${transport_args[@]}" \
        "service=$service" "nthreads=$threads" "duration=$duration" "warmup=$warmup" >"$log" 2>&1 &
    CLIENT_PID=$!
    if ! wait "$CLIENT_PID"; then
        CLIENT_PID=""
        cat "$log" >&2; native_fail "workload failed; log: $log"
    fi
    CLIENT_PID=""
    cat "$log"
}
