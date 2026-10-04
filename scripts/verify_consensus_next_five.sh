#!/usr/bin/env bash
# Verus-only safety proofs for Om, Gaios, CORFU, Replicated Commit and SpecPaxos.
# Om includes a formally proved counterexample to the literal read/write model.
set -euo pipefail
consensus_repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
consensus_verus="${VERUS_PATH:-verus}"
cd "$consensus_repo"
if [[ "${1:-}" == "--integrated" ]]; then
    shift
    # Unrelated crate modules have trusted bodies. The standalone mode
    # is the --no-cheating authority for all files in this batch.
    consensus_modules=(
        ConsensusSafety::paxos ConsensusSafety::register_history ConsensusSafety::state_machine
        Om::consensus Om::lookup Om::read_write Gaios::reads Corfu::chain Corfu::layout
        ReplicatedCommit::commit SpecPaxos::reconciliation SpecPaxos::execution next_five_witnesses
    )
    consensus_args=()
    for consensus_module in "${consensus_modules[@]}"; do
        consensus_args+=(--verify-only-module "protocol::$consensus_module")
    done
    exec "$consensus_verus" --crate-type=lib src/lib.rs --triggers-mode silent "${consensus_args[@]}" "$@"
fi
"$consensus_verus" --crate-type=lib src/protocol/next_five_harness.rs \
    --triggers-mode silent --no-cheating "$@"
