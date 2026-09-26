#!/usr/bin/env bash
# Verify the paper-based Tiga model and every included proof/counterexample.
# A passing run is not by itself a positive strict-serializability theorem.
set -euo pipefail
tiga_repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tiga_verus="${VERUS_PATH:-verus}"
cd "$tiga_repo_root"
tiga_modules=()
for tiga_file in src/protocol/Tiga/*.rs; do
    tiga_module="${tiga_file##*/}"
    tiga_module="${tiga_module%.rs}"
    if [[ "$tiga_module" != mod ]]; then
        tiga_modules+=(--verify-only-module "protocol::Tiga::$tiga_module")
    fi
done
exec "$tiga_verus" --crate-type=lib src/lib.rs "${tiga_modules[@]}" \
    --num-threads 4 --triggers-mode selective "$@"
