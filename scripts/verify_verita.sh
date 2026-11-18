#!/usr/bin/env bash
# Match the tla-rs entry point in Verus tools/verita/run_configuration_all.toml.
set -euo pipefail
verita_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
verita_verus="${VERUS_PATH:-verus}"
cd "$verita_root"
read -r -a verita_cfg <<< "$(scripts/verus_cfg.sh "$verita_verus")"
exec "$verita_verus" src/lib.rs --output-json --time \
    --no-report-long-running --crate-type=dylib "${verita_cfg[@]}" "$@"
