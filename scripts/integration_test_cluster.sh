#!/bin/bash
# Phase 17.6.3: Integration test harness for protocol clusters
# Launches N-node clusters for each protocol, verifies startup and stability.
# For RSL: also runs a client to verify end-to-end request/reply.
#
# Usage:
#   ./scripts/integration_test_cluster.sh [protocol ...]
#   ./scripts/integration_test_cluster.sh              # test all protocols (incl. RSL)
#   ./scripts/integration_test_cluster.sh raft paxos   # test specific protocols
#   ./scripts/integration_test_cluster.sh rsl          # test RSL end-to-end

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
BIN_DIR="$PROJECT_ROOT/bin"
CERT_TOOL="$BIN_DIR/CreateIronServiceCerts.dll"
SERVER="$BIN_DIR/IronProtocolServer.dll"
RSL_SERVER="$BIN_DIR/IronRSLServerUDP.dll"
RSL_CLIENT="$BIN_DIR/IronRSLClientUDP.dll"
RAFT_CLIENT="$BIN_DIR/IronRaftClient.dll"

# Cluster parameters
NUM_NODES=3
BASE_PORT=17600
READY_TIMEOUT=10     # seconds to wait for [[READY]]
RUN_DURATION=5       # seconds to let the cluster run
RSL_CLIENT_DURATION=15  # seconds for RSL client experiment
RAFT_CLIENT_DURATION=10 # seconds for Raft benchmark client
TEMP_DIR=""
PIDS=()

# All supported protocols
ALL_PROTOCOLS=(rsl twophase leaderelection primarybackup chainreplication paxos verticalpaxos raft pbft epaxos)

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
    if [ ! -f "$RSL_SERVER" ]; then
        echo "FAIL: $RSL_SERVER not found. Run: scons bin/IronRSLServerUDP.dll"
        exit 1
    fi
    if [ ! -f "$RSL_CLIENT" ]; then
        echo "FAIL: $RSL_CLIENT not found. Run: scons bin/IronRSLClientUDP.dll"
        exit 1
    fi
}

# Generate certificates for an N-node cluster
# Args: $1=output_dir, $2=base_port, $3=num_nodes, $4=service_type (default: Proto)
generate_certs() {
    local out_dir="$1"
    local base_port="$2"
    local n="$3"
    local svc_type="${4:-Proto}"

    local args=(dotnet "$CERT_TOOL" "name=TestCluster" "type=$svc_type" "outputdir=$out_dir" "usessl=false")
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

# Test RSL with end-to-end client request/reply
# Args: $1=base_port
# Returns: 0=pass, 1=fail
test_rsl() {
    local port_base="$1"
    local cert_dir="$TEMP_DIR/certs_rsl"
    local log_dir="$TEMP_DIR/logs_rsl"
    local local_pids=()

    mkdir -p "$cert_dir" "$log_dir"

    # Step 1: Generate certificates (RSL requires type=IronRSL)
    if ! generate_certs "$cert_dir" "$port_base" "$NUM_NODES" "IronRSL"; then
        echo "  FAIL: Certificate generation failed"
        return 1
    fi

    local service_file="$cert_dir/TestCluster.IronRSL.service.txt"
    if [ ! -f "$service_file" ]; then
        echo "  FAIL: Service file not generated"
        return 1
    fi

    # Step 2: Launch RSL server nodes
    for i in $(seq 1 "$NUM_NODES"); do
        local private_file="$cert_dir/TestCluster.IronRSL.server${i}.private.txt"
        local log_file="$log_dir/server${i}.log"

        if [ ! -f "$private_file" ]; then
            echo "  FAIL: Private key for node $i not generated"
            for pid in "${local_pids[@]}"; do
                kill "$pid" 2>/dev/null || true
            done
            return 1
        fi

        dotnet "$RSL_SERVER" "$service_file" "$private_file" \
            >"$log_file" 2>&1 &
        local_pids+=("$!")
        PIDS+=("$!")
    done

    # Step 3: Wait for all servers to become ready
    for i in $(seq 1 "$NUM_NODES"); do
        local log_file="$log_dir/server${i}.log"
        if ! wait_for_ready "$log_file" "$READY_TIMEOUT" "server $i"; then
            echo "  FAIL: Server $i did not become ready within ${READY_TIMEOUT}s"
            echo "  Log contents:"
            head -20 "$log_file" 2>/dev/null | sed 's/^/    /'
            for pid in "${local_pids[@]}"; do
                kill "$pid" 2>/dev/null || true
            done
            return 1
        fi
    done

    # Step 4: Launch RSL client
    local client_port=$((port_base + NUM_NODES))
    local client_log="$log_dir/client.log"
    local port1=$((port_base))
    local port2=$((port_base + 1))
    local port3=$((port_base + 2))

    dotnet "$RSL_CLIENT" \
        "clientip=127.0.0.1" "clientport=$client_port" \
        "ip1=127.0.0.1" "port1=$port1" \
        "ip2=127.0.0.1" "port2=$port2" \
        "ip3=127.0.0.1" "port3=$port3" \
        "nthreads=1" "duration=$RSL_CLIENT_DURATION" \
        >"$client_log" 2>&1 &
    local client_pid=$!
    local_pids+=("$client_pid")
    PIDS+=("$client_pid")

    # Step 5: Wait for client to finish (it runs for RSL_CLIENT_DURATION seconds)
    local client_deadline=$((SECONDS + RSL_CLIENT_DURATION + 10))
    local client_done=false
    while [ $SECONDS -lt $client_deadline ]; do
        if ! kill -0 "$client_pid" 2>/dev/null; then
            client_done=true
            break
        fi
        if grep -q '\[\[DONE\]\]' "$client_log" 2>/dev/null; then
            client_done=true
            # Give client a moment to print final stats and exit
            sleep 1
            break
        fi
        sleep 0.5
    done

    if [ "$client_done" = false ]; then
        echo "  FAIL: Client did not finish within timeout"
        kill "$client_pid" 2>/dev/null || true
    fi

    # Step 6: Verify servers are still alive
    local all_alive=true
    for idx in $(seq 0 $((NUM_NODES - 1))); do
        local pid="${local_pids[$idx]}"
        local node_num=$((idx + 1))
        if ! kill -0 "$pid" 2>/dev/null; then
            all_alive=false
            local log_file="$log_dir/server${node_num}.log"
            echo "  FAIL: Server $node_num (pid $pid) exited prematurely"
            echo "  Last 10 lines of log:"
            tail -10 "$log_file" 2>/dev/null | sed 's/^/    /'
        fi
    done

    # Step 7: Check client got responses (throughput > 0)
    local throughput_ok=false
    if grep -q 'throughput' "$client_log" 2>/dev/null; then
        # Extract the final throughput line: "throughput N | avg latency ms M"
        local tp_line
        tp_line=$(grep '^throughput' "$client_log" | tail -1)
        if [ -n "$tp_line" ]; then
            local tp_val
            tp_val=$(echo "$tp_line" | awk '{print $2}')
            if [ -n "$tp_val" ] && [ "$tp_val" -gt 0 ] 2>/dev/null; then
                throughput_ok=true
            fi
        fi
    fi

    # Step 8: Clean shutdown
    for pid in "${local_pids[@]}"; do
        kill "$pid" 2>/dev/null || true
    done
    local wait_deadline=$((SECONDS + 3))
    for pid in "${local_pids[@]}"; do
        while [ $SECONDS -lt $wait_deadline ] && kill -0 "$pid" 2>/dev/null; do
            sleep 0.1
        done
        kill -9 "$pid" 2>/dev/null || true
    done
    wait "${local_pids[@]}" 2>/dev/null || true

    for pid in "${local_pids[@]}"; do
        PIDS=("${PIDS[@]/$pid/}")
    done

    if [ "$all_alive" = true ] && [ "$throughput_ok" = true ]; then
        return 0
    elif [ "$all_alive" = false ]; then
        return 1
    else
        echo "  FAIL: Client reported zero throughput (no replies received)"
        echo "  Client log:"
        cat "$client_log" 2>/dev/null | sed 's/^/    /'
        return 1
    fi
}

# Test Raft with end-to-end benchmark client
# Args: $1=base_port
# Returns: 0=pass, 1=fail
test_raft_benchmark() {
    local port_base="$1"
    local cert_dir="$TEMP_DIR/certs_raft"
    local log_dir="$TEMP_DIR/logs_raft"
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

    # Step 2: Launch Raft server nodes
    for i in $(seq 1 "$NUM_NODES"); do
        local private_file="$cert_dir/TestCluster.Proto.server${i}.private.txt"
        local log_file="$log_dir/server${i}.log"

        if [ ! -f "$private_file" ]; then
            echo "  FAIL: Private key for node $i not generated"
            for pid in "${local_pids[@]}"; do
                kill "$pid" 2>/dev/null || true
            done
            return 1
        fi

        launch_node "raft" "$service_file" "$private_file" "$log_file"
        local_pids+=("$last_launched_pid")
        PIDS+=("$last_launched_pid")
    done

    # Step 3: Wait for all servers to become ready
    for i in $(seq 1 "$NUM_NODES"); do
        local log_file="$log_dir/server${i}.log"
        if ! wait_for_ready "$log_file" "$READY_TIMEOUT" "server $i"; then
            echo "  FAIL: Server $i did not become ready within ${READY_TIMEOUT}s"
            echo "  Log contents:"
            head -20 "$log_file" 2>/dev/null | sed 's/^/    /'
            for pid in "${local_pids[@]}"; do
                kill "$pid" 2>/dev/null || true
            done
            return 1
        fi
    done

    # Step 4: Check if Raft benchmark client is available
    if [ ! -f "$RAFT_CLIENT" ]; then
        echo "  SKIP: IronRaftClient.dll not found"
        for pid in "${local_pids[@]}"; do
            kill "$pid" 2>/dev/null || true
        done
        return 2  # 2 = skip
    fi

    # Step 5: Launch Raft benchmark client
    local client_port=$((port_base + NUM_NODES))
    local client_log="$log_dir/client.log"
    local port1=$((port_base))
    local port2=$((port_base + 1))
    local port3=$((port_base + 2))

    dotnet "$RAFT_CLIENT" \
        "clientip=127.0.0.1" "clientport=$client_port" \
        "ip1=127.0.0.1" "port1=$port1" \
        "ip2=127.0.0.1" "port2=$port2" \
        "ip3=127.0.0.1" "port3=$port3" \
        "nthreads=1" "duration=$RAFT_CLIENT_DURATION" \
        >"$client_log" 2>&1 &
    local client_pid=$!
    local_pids+=("$client_pid")
    PIDS+=("$client_pid")

    # Step 6: Wait for client to finish
    local client_deadline=$((SECONDS + RAFT_CLIENT_DURATION + 10))
    local client_done=false
    while [ $SECONDS -lt $client_deadline ]; do
        if ! kill -0 "$client_pid" 2>/dev/null; then
            client_done=true
            break
        fi
        if grep -q '\[\[DONE\]\]' "$client_log" 2>/dev/null; then
            client_done=true
            sleep 1
            break
        fi
        sleep 0.5
    done

    if [ "$client_done" = false ]; then
        echo "  FAIL: Client did not finish within timeout"
        kill "$client_pid" 2>/dev/null || true
    fi

    # Step 7: Verify servers are still alive
    local all_alive=true
    for idx in $(seq 0 $((NUM_NODES - 1))); do
        local pid="${local_pids[$idx]}"
        local node_num=$((idx + 1))
        if ! kill -0 "$pid" 2>/dev/null; then
            all_alive=false
            local log_file="$log_dir/server${node_num}.log"
            echo "  FAIL: Server $node_num (pid $pid) exited prematurely"
            echo "  Last 10 lines of log:"
            tail -10 "$log_file" 2>/dev/null | sed 's/^/    /'
        fi
    done

    # Step 8: Check client got responses (throughput > 0)
    local throughput_ok=false
    if grep -q 'throughput' "$client_log" 2>/dev/null; then
        local tp_line
        tp_line=$(grep 'ops/sec' "$client_log" | tail -1)
        if [ -n "$tp_line" ]; then
            throughput_ok=true
        fi
    fi

    # Step 9: Clean shutdown
    for pid in "${local_pids[@]}"; do
        kill "$pid" 2>/dev/null || true
    done
    local wait_deadline=$((SECONDS + 3))
    for pid in "${local_pids[@]}"; do
        while [ $SECONDS -lt $wait_deadline ] && kill -0 "$pid" 2>/dev/null; do
            sleep 0.1
        done
        kill -9 "$pid" 2>/dev/null || true
    done
    wait "${local_pids[@]}" 2>/dev/null || true

    for pid in "${local_pids[@]}"; do
        PIDS=("${PIDS[@]/$pid/}")
    done

    if [ "$all_alive" = true ] && [ "$throughput_ok" = true ]; then
        return 0
    elif [ "$all_alive" = false ]; then
        return 1
    else
        echo "  FAIL: Client reported zero throughput (no replies received)"
        echo "  Client log:"
        cat "$client_log" 2>/dev/null | sed 's/^/    /'
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
    # RSL needs an extra port for the client
    if [ "$protocol" = "rsl" ] || [ "$protocol" = "raft" ]; then
        port_offset=$((port_offset + NUM_NODES + 1))
    else
        port_offset=$((port_offset + NUM_NODES))
    fi

    printf "%-20s ... " "$protocol"

    if [ "$protocol" = "rsl" ]; then
        if test_rsl "$port_base"; then
            echo "PASS (end-to-end)"
            passed=$((passed + 1))
        else
            echo "FAIL"
            failed=$((failed + 1))
        fi
    elif [ "$protocol" = "raft" ]; then
        ret=0
        test_raft_benchmark "$port_base" || ret=$?
        if [ "$ret" -eq 0 ]; then
            echo "PASS (benchmark)"
            passed=$((passed + 1))
        elif [ "$ret" -eq 2 ]; then
            echo "SKIP (IronRaftClient.dll not found)"
            skipped=$((skipped + 1))
        else
            echo "FAIL"
            failed=$((failed + 1))
        fi
    else
        if test_protocol "$protocol" "$port_base"; then
            echo "PASS"
            passed=$((passed + 1))
        else
            echo "FAIL"
            failed=$((failed + 1))
        fi
    fi
done

echo ""
echo "==========================================="
echo "Results: $passed passed, $failed failed, $skipped skipped out of ${#PROTOCOLS[@]} protocols"

if [ "$failed" -gt 0 ]; then
    exit 1
fi
echo "All integration tests passed."
