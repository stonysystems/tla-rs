#!/usr/bin/env bash
# Verify the Figure 14 recovery counterexamples against the live Jetpack model.
# See docs/jetpack-recovery-audit.md. A passing run proves the counterexamples;
# the model they extend is verified by scripts/verify_consensus_jetpack.sh.
set -euo pipefail
audit_repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
audit_verus="${VERUS_PATH:-verus}"
cd "$audit_repo"
exec "$audit_verus" --crate-type=lib src/protocol/JetpackAudit/harness.rs \
    --verify-only-module figure14 --triggers-mode selective --no-cheating "$@"
