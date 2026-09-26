#!/usr/bin/env bash
# Verify every EPaxos* model and proof module. See docs/epaxos-proof-plan.md
# for the exact theorem scope; a passing run is not a runtime refinement proof.
# Tested with Verus 0.2026.08.02.b677dd5.
set -euo pipefail

epaxos_repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
epaxos_verus="${VERUS_PATH:-verus}"
cd "$epaxos_repo_root"

epaxos_modules=()
for epaxos_module_file in src/protocol/EPaxos/star/*.rs; do
    epaxos_module="${epaxos_module_file##*/}"
    epaxos_module="${epaxos_module%.rs}"
    if [[ "$epaxos_module" != mod ]]; then
        epaxos_modules+=(--verify-only-module "protocol::EPaxos::star::$epaxos_module")
    fi
done

exec "$epaxos_verus" --crate-type=lib src/lib.rs "${epaxos_modules[@]}" \
    --num-threads 4 --triggers-mode selective "$@"
