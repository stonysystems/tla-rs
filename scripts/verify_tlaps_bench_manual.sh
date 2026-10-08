#!/usr/bin/env bash
set -euo pipefail
bench_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
bench_verus="${VERUS_PATH:-verus}"
cd "$bench_root"
exec "$bench_verus" --crate-type=lib --no-cheating --num-threads 4 \
    src/protocol/tlaps_bench_harness.rs "$@"
