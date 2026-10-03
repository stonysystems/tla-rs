#!/usr/bin/env bash
# EPaxos native 3-node request/reply workload, not self-driving commit estimates.
# Usage: bench_epaxos.sh [duration_seconds] [num_trials] [nthreads]
set -euo pipefail
if (( $# > 3 )); then
    printf 'Usage: %s [duration_seconds] [num_trials] [nthreads]\n' "$0" >&2
    exit 1
fi
exec "$(dirname "${BASH_SOURCE[0]}")/bench_generic.sh" epaxos "$@"
