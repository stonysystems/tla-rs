#!/usr/bin/env bash
# Verify the CausalMesh model, its safety theorem, and the single-round
# counterexample as a standalone crate with --no-cheating.
# See docs/causalmesh-proof.md for the exact scope.
set -euo pipefail
causalmesh_repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
causalmesh_verus="${VERUS_PATH:-verus}"
cd "$causalmesh_repo/src/protocol/CausalMesh"
exec "$causalmesh_verus" --crate-type=lib harness.rs \
    --num-threads 4 --triggers-mode selective --no-cheating "$@"
