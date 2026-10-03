#!/usr/bin/env bash
# Native cluster smoke. Workloads validate request/reply values; the remaining
# protocols are explicitly startup-only, not consensus/application tests.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/native_cluster.sh"
BASE_PORT="${BASE_PORT:-17600}"
DURATION="${DURATION:-3}"
WARMUP_SECONDS="${WARMUP_SECONDS:-2}"
CLIENT_THREADS="${CLIENT_THREADS:-4}"
STARTUP_SECONDS="${STARTUP_SECONDS:-2}"
RECOVERY="${RECOVERY:-1}"
OUTPUT_DIR="${OUTPUT_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/tla-rs-native-smoke.XXXXXX")}"
trap native_stop EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
native_require
native_positive DURATION "$DURATION"
native_positive CLIENT_THREADS "$CLIENT_THREADS"
native_positive BASE_PORT "$BASE_PORT"
[[ "$WARMUP_SECONDS" =~ ^[0-9]+$ && "$STARTUP_SECONDS" =~ ^[0-9]+$ ]] || native_fail 'warmup/startup seconds must be nonnegative integers'
mkdir -p "$OUTPUT_DIR"
protocols=("$@")
if (( ${#protocols[@]} == 0 )); then
    protocols=(rsl twophase leaderelection primarybackup chainreplication paxos verticalpaxos raft pbft epaxos)
fi
printf 'Native smoke logs: %s\n' "$OUTPUT_DIR"
index=0
for protocol in "${protocols[@]}"; do
    case "$protocol" in
        rsl|raft|primarybackup|pbft|epaxos|twophase|leaderelection|chainreplication|paxos|verticalpaxos) ;;
        *) native_fail "unknown protocol $protocol" ;;
    esac
    native_start "$protocol" "$OUTPUT_DIR/$protocol" "$((BASE_PORT + index * 10))"
    case "$protocol" in
        rsl|raft|primarybackup|pbft|epaxos)
            native_workload "$CLUSTER_DIR/client.log" "$CLIENT_THREADS" "$DURATION" "$WARMUP_SECONDS"
            native_alive
            printf 'PASS end-to-end: %s (%s)\n' "$protocol" "${TRANSPORT:-udp}"
            ;;
        *)
            sleep "$STARTUP_SECONDS"
            native_alive
            printf 'PASS startup-only: %s (%s; no workload adapter)\n' "$protocol" "${TRANSPORT:-udp}"
            ;;
    esac
    if [[ "$protocol" == rsl && "$RECOVERY" == 1 ]]; then
        # Kill a replica (including the initial leader when node 1 leads), keep
        # quorum running, prove progress, restart it and prove progress again.
        stopped=${PIDS[0]}
        kill -KILL "$stopped"
        wait "$stopped" 2>/dev/null || true
        PIDS=("${PIDS[@]:1}")
        native_workload "$CLUSTER_DIR/client-failure.log" "$CLIENT_THREADS" "$DURATION" "$((WARMUP_SECONDS + 3))"
        native_alive
        native_launch_node 1 '-recovered'
        native_workload "$CLUSTER_DIR/client-recovery.log" "$CLIENT_THREADS" "$DURATION" "$((WARMUP_SECONDS + 3))"
        native_alive
        printf 'PASS failure/recovery: rsl (one killed replica; quorum progress; restarted replica alive)\n'
    fi
    native_stop
    index=$((index + 1))
done
if [[ "${TRANSPORT:-udp}" == udp && "${TCP_SMOKE:-1}" == 1 && " ${protocols[*]} " == *" rsl "* ]]; then
    TRANSPORT=tcp
    for USE_SSL in false true; do
        native_start rsl "$OUTPUT_DIR/rsl-tcp-tls-$USE_SSL" "$((BASE_PORT + index * 10))"
        native_workload "$CLUSTER_DIR/client.log" "$CLIENT_THREADS" "$DURATION" "$WARMUP_SECONDS"
        native_alive
        printf 'PASS end-to-end: rsl (tcp, TLS=%s)\n' "$USE_SSL"
        native_stop
        index=$((index + 1))
    done
fi
printf 'PASS native smoke: %s protocols; logs retained at %s\n' "${#protocols[@]}" "$OUTPUT_DIR"
