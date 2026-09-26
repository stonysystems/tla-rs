#!/usr/bin/env bash
# Verify counterexamples and the existing EPaxos action contracts.
# A successful run confirms the audit findings, not EPaxos safety.
# Tested with Verus 0.2026.08.02.b677dd5.
set -euo pipefail

epaxos_repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
epaxos_verus="${VERUS_PATH:-verus}"
cd "$epaxos_repo_root"

exec "$epaxos_verus" --crate-type=lib src/lib.rs \
    --verify-only-module protocol::EPaxos::epaxos \
    --verify-only-module protocol::EPaxos::types \
    --verify-only-module protocol::EPaxos::safety_audit \
    --verify-only-module generated::EPaxos::epaxos_gen \
    --verify-only-module generated::EPaxos::types_gen \
    --num-threads 4 --triggers-mode selective "$@"
