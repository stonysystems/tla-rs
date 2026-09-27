#!/usr/bin/env bash
# Prove Jetpack recovery, agreement and conditional linearizability with Verus.
set -euo pipefail
consensus_repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
consensus_verus="${VERUS_PATH:-verus}"
cd "$consensus_repo"
"$consensus_verus" --crate-type=lib src/protocol/Jetpack/proof_harness.rs \
    --triggers-mode silent --no-cheating "$@"
