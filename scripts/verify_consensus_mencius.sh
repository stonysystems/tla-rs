#!/usr/bin/env bash
# Verify the single-instance Coordinated Paxos abstraction.
set -euo pipefail
consensus_repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
consensus_verus="${VERUS_PATH:-verus}"
cd "$consensus_repo"
"$consensus_verus" --crate-type=lib \
    src/protocol/Mencius/instance.rs --triggers-mode silent "$@"
