#!/usr/bin/env bash
# PrimaryBackup native request/reply workload; measure acknowledged values.
# Usage: bench_primarybackup.sh [duration_seconds] [num_trials] [nthreads]
set -euo pipefail
if (( $# > 3 )); then
    printf 'Usage: %s [duration_seconds] [num_trials] [nthreads]\n' "$0" >&2
    exit 1
fi
exec "$(dirname "${BASH_SOURCE[0]}")/bench_generic.sh" primarybackup "$@"
