#!/usr/bin/env bash
# Lion-style local matrix; native is the only default runtime.
# Explicit comparison: RUNTIMES='native csharp' REFERENCE_SERVER=/path/to/launcher.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/native_cluster.sh"
(( $# == 0 )) || native_fail 'configure with environment variables; positional arguments are not supported'
[[ -z "${BASELINE_SERVICE:-}" ]] || native_fail 'BASELINE_SERVICE cannot establish matched parameters; use RUNTIMES="native csharp" and REFERENCE_SERVER'
native_require
command -v python3 >/dev/null || native_fail 'python3 is required for benchmark measurement'
export BIN_DIR="$NATIVE_BIN"
exec python3 "$NATIVE_ROOT/scripts/benchmark_matrix.py"
