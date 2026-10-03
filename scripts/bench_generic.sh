#!/usr/bin/env bash
# Native request/reply benchmark; all counts/latencies come from matched replies.
# Usage: bench_generic.sh <protocol> [duration_seconds] [num_trials] [nthreads]
# Defaults: 30 seconds, 3 trials, 2 workers; RSL uses TCP, generic protocols UDP.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if (( $# < 1 || $# > 4 )); then
    printf 'Usage: %s <rsl|raft|primarybackup|pbft|epaxos> [duration] [trials] [nthreads]\n' "$0" >&2
    exit 1
fi
export PROTOCOL=$1
case "$PROTOCOL" in
    pb) PROTOCOL=primarybackup ;;
    rsl|raft|primarybackup|pbft|epaxos) ;;
    *) printf 'No native workload for protocol: %s\n' "$PROTOCOL" >&2; exit 1 ;;
esac
export DURATION="${2:-${DURATION:-30}}"
export TRIALS="${3:-${TRIALS:-3}}"
export CLIENT_THREADS="${4:-${CLIENT_THREADS:-2}}"
# The common driver records the same matrix/evidence for every native protocol.
# TRANSPORT, USE_SSL, CONFIGS and explicit concurrency overrides pass through.
exec "$ROOT/scripts/bench_rsl_runtime.sh"
