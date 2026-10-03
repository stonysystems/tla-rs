#!/usr/bin/env bash
# PBFT native 4-node request/reply workload; injection is not counted as success.
# Usage: bench_pbft.sh [duration_seconds] [num_trials] [nthreads]
set -euo pipefail
if (( $# > 3 )); then
    printf 'Usage: %s [duration_seconds] [num_trials] [nthreads]\n' "$0" >&2
    exit 1
fi
exec "$(dirname "${BASH_SOURCE[0]}")/bench_generic.sh" pbft "$@"
