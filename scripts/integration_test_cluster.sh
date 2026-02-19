#!/bin/bash
# Phase 17.6.3: Integration test harness for protocol clusters
# Launches N-node clusters for each protocol, verifies startup and stability.
#
# Usage:
#   ./scripts/integration_test_cluster.sh [protocol ...]
#   ./scripts/integration_test_cluster.sh              # test all protocols
#   ./scripts/integration_test_cluster.sh raft paxos   # test specific protocols

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
BIN_DIR="$PROJECT_ROOT/bin"
CERT_TOOL="$BIN_DIR/CreateIronServiceCerts.dll"
SERVER="$BIN_DIR/IronProtocolServer.dll"

# Cluster parameters
NUM_NODES=3
BASE_PORT=17600
READY_TIMEOUT=10     # seconds to wait for [[READY]]
RUN_DURATION=5       # seconds to let the cluster run
TEMP_DIR=""
PIDS=()

# All supported protocols (excluding rsl which uses a different server binary)
ALL_PROTOCOLS=(twophase leaderelection primarybackup chainreplication paxos verticalpaxos raft pbft epaxos)

cleanup() {
    # Kill any remaining background processes
    for pid in "${PIDS[@]}"; do
        if kill -0 "$pid" 2>/dev/null; then
            kill "$pid" 2>/dev/null || true
        fi
    done
    wait "${PIDS[@]}" 2>/dev/null || true
    PIDS=()

    # Remove temp directory
    if [ -n "$TEMP_DIR" ] && [ -d "$TEMP_DIR" ]; then
        rm -rf "$TEMP_DIR"
    fi
}

trap cleanup EXIT

check_prerequisites() {
    if ! command -v dotnet &>/dev/null; then
        echo "FAIL: dotnet not found in PATH"
        exit 1
    fi
    if [ ! -f "$CERT_TOOL" ]; then
        echo "FAIL: $CERT_TOOL not found. Run: scons bin/CreateIronServiceCerts.dll"
        exit 1
    fi
    if [ ! -f "$SERVER" ]; then
        echo "FAIL: $SERVER not found. Run: scons bin/IronProtocolServer.dll"
        exit 1
    fi
    if [ ! -f "$PROJECT_ROOT/liblib.so" ]; then
        echo "FAIL: liblib.so not found. Run: scons --verus-path=... liblib.so"
        exit 1
    fi
}

# Generate certificates for an N-node cluster
# Args: $1=output_dir, $2=base_port, $3=num_nodes
generate_certs() {
    local out_dir="$1"
    local base_port="$2"
    local n="$3"

    local args=(dotnet "$CERT_TOOL" "name=TestCluster" "type=Proto" "outputdir=$out_dir" "usessl=false")
    for i in $(seq 1 "$n"); do
        local port=$((base_port + i - 1))
        args+=("addr${i}=127.0.0.1" "port${i}=${port}")
    done

    "${args[@]}" >/dev/null 2>&1
}

# Launch a single node and wait for [[READY]]
# Args: $1=protocol, $2=service_file, $3=private_file, $4=log_file
# Sets global: last_launched_pid
launch_node() {
    local protocol="$1"
    local service_file="$2"
    local private_file="$3"
    local log_file="$4"

    dotnet "$SERVER" "$service_file" "$private_file" "protocol=$protocol" \
        >"$log_file" 2>&1 &
    last_launched_pid=$!
}

# Wait for [[READY]] in a log file with timeout
# Args: $1=log_file, $2=timeout_secs, $3=label
wait_for_ready() {
    local log_file="$1"
    local timeout="$2"
    local label="$3"
    local deadline=$((SECONDS + timeout))

    while [ $SECONDS -lt $deadline ]; do
        if grep -q '\[\[READY\]\]' "$log_file" 2>/dev/null; then
            return 0
        fi
        sleep 0.2
    done
    return 1
}

# Test a single protocol with N nodes
# Args: $1=protocol, $2=base_port
# Returns: 0=pass, 1=fail
test_protocol() {
    local protocol="$1"
    local port_base="$2"
    local cert_dir="$TEMP_DIR/certs_${protocol}"
    local log_dir="$TEMP_DIR/logs_${protocol}"
    local local_pids=()

    mkdir -p "$cert_dir" "$log_dir"

    # Step 1: Generate certificates
    if ! generate_certs "$cert_dir" "$port_base" "$NUM_NODES"; then
        echo "  FAIL: Certificate generation failed"
        return 1
    fi

    local service_file="$cert_dir/TestCluster.Proto.service.txt"
    if [ ! -f "$service_file" ]; then
        echo "  FAIL: Service file not generated"
        return 1
    fi

    # Step 2: Launch all nodes
    for i in $(seq 1 "$NUM_NODES"); do
        local private_file="$cert_dir/TestCluster.Proto.server${i}.private.txt"
        local log_file="$log_dir/node${i}.log"

        if [ ! -f "$private_file" ]; then
            echo "  FAIL: Private key for node $i not generated"
            # Kill already-launched nodes
            for pid in "${local_pids[@]}"; do
                kill "$pid" 2>/dev/null || true
            done
            return 1
        fi

        launch_node "$protocol" "$service_file" "$private_file" "$log_file"
        local_pids+=("$last_launched_pid")
        PIDS+=("$last_launched_pid")
    done

    # Step 3: Wait for all nodes to become ready
    for i in $(seq 1 "$NUM_NODES"); do
        local log_file="$log_dir/node${i}.log"
        if ! wait_for_ready "$log_file" "$READY_TIMEOUT" "node $i"; then
            echo "  FAIL: Node $i did not become ready within ${READY_TIMEOUT}s"
            echo "  Log contents:"
            cat "$log_file" 2>/dev/null | head -20 | sed 's/^/    /'
            for pid in "${local_pids[@]}"; do
                kill "$pid" 2>/dev/null || true
            done
            return 1
        fi
    done

    # Step 4: Let cluster run and exchange messages
    sleep "$RUN_DURATION"

    # Step 5: Verify all nodes are still running (haven't crashed)
    local all_alive=true
    for idx in "${!local_pids[@]}"; do
        local pid="${local_pids[$idx]}"
        local node_num=$((idx + 1))
        if ! kill -0 "$pid" 2>/dev/null; then
            all_alive=false
            local log_file="$log_dir/node${node_num}.log"
            echo "  FAIL: Node $node_num (pid $pid) exited prematurely"
            echo "  Last 10 lines of log:"
            tail -10 "$log_file" 2>/dev/null | sed 's/^/    /'
        fi
    done

    # Step 6: Clean shutdown
    for pid in "${local_pids[@]}"; do
        kill "$pid" 2>/dev/null || true
    done
    # Wait up to 3 seconds for graceful exit
    local wait_deadline=$((SECONDS + 3))
    for pid in "${local_pids[@]}"; do
        while [ $SECONDS -lt $wait_deadline ] && kill -0 "$pid" 2>/dev/null; do
            sleep 0.1
        done
        # Force kill if still running
        kill -9 "$pid" 2>/dev/null || true
    done
    wait "${local_pids[@]}" 2>/dev/null || true

    # Remove killed PIDs from global array
    for pid in "${local_pids[@]}"; do
        PIDS=("${PIDS[@]/$pid/}")
    done

    if [ "$all_alive" = true ]; then
        return 0
    else
        return 1
    fi
}

# ---- Main ----

check_prerequisites

# Select protocols to test
if [ $# -gt 0 ]; then
    PROTOCOLS=("$@")
else
    PROTOCOLS=("${ALL_PROTOCOLS[@]}")
fi

TEMP_DIR="$(mktemp -d /tmp/ironfleet_integration_XXXXXX)"

echo "Integration Test: Protocol Cluster Harness"
echo "==========================================="
echo "Nodes per cluster: $NUM_NODES"
echo "Ready timeout: ${READY_TIMEOUT}s"
echo "Run duration: ${RUN_DURATION}s"
echo "Temp dir: $TEMP_DIR"
echo ""

passed=0
failed=0
skipped=0
port_offset=0

for protocol in "${PROTOCOLS[@]}"; do
    port_base=$((BASE_PORT + port_offset))
    port_offset=$((port_offset + NUM_NODES))

    printf "%-20s ... " "$protocol"

    if test_protocol "$protocol" "$port_base"; then
        echo "PASS"
        passed=$((passed + 1))
    else
        echo "FAIL"
        failed=$((failed + 1))
    fi
done

echo ""
echo "==========================================="
echo "Results: $passed passed, $failed failed, $skipped skipped out of ${#PROTOCOLS[@]} protocols"

if [ "$failed" -gt 0 ]; then
    exit 1
fi
echo "All integration tests passed."
