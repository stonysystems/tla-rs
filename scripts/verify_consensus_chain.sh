#!/usr/bin/env bash
# Prove the history-level Chain Replication model with Verus.
# This does not verify the master's distributed reconfiguration implementation.
set -euo pipefail
consensus_repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
consensus_verus="${VERUS_PATH:-verus}"
cd "$consensus_repo"
"$consensus_verus" --crate-type=lib \
    src/protocol/ChainReplication/paper_model.rs --triggers-mode silent "$@"
