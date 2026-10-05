#!/usr/bin/env bash
set -euo pipefail
mako_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
mako_verus="${VERUS_PATH:-verus}"
cd "$mako_root/src/protocol/Mako"
exec "$mako_verus" --crate-type=lib harness.rs --no-cheating \
    --num-threads 4 --triggers-mode selective "$@"
