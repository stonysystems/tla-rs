#!/bin/bash
# Compare TLC and source-first parity state exports for a given protocol.
#
# Usage:
#   ./scripts/diff_tlc_vs_source_first_states.sh twophase
#   ./scripts/diff_tlc_vs_source_first_states.sh primarybackup
#   ./scripts/diff_tlc_vs_source_first_states.sh all
#
# Requires: python3, checked-in exports in reports/model_check/parity/

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SF_DIR="$REPO_ROOT/reports/model_check/parity/source_first"
TLC_DIR="$REPO_ROOT/reports/model_check/parity/tlc"
DIFF_TOOL="$REPO_ROOT/scripts/diff_parity_states.py"

PROTOCOLS="${1:-all}"

if [ "$PROTOCOLS" = "all" ]; then
    PROTOCOLS="twophase primarybackup leaderelection"
fi

exit_code=0

for proto in $PROTOCOLS; do
    sf_file="$SF_DIR/$proto/states.jsonl"
    tlc_file="$TLC_DIR/$proto/states.jsonl"

    if [ ! -f "$sf_file" ]; then
        echo "Warning: $sf_file not found, skipping $proto" >&2
        continue
    fi
    if [ ! -f "$tlc_file" ]; then
        echo "Warning: $tlc_file not found, skipping $proto" >&2
        continue
    fi

    echo ""
    echo ">>> Protocol: $proto"
    echo ""
    python3 "$DIFF_TOOL" "$sf_file" "$tlc_file" \
        --left-label "source-first" --right-label "TLC" || exit_code=1
done

exit $exit_code
