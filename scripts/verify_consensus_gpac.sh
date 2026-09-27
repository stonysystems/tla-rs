#!/usr/bin/env bash
# Reproduce the published PAC recovery defect and check the corrected replay.
set -euo pipefail
: "${TLA2TOOLS:?Set TLA2TOOLS to a tla2tools.jar path}"
consensus_repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
consensus_work="$(mktemp -d)"
trap 'rm -rf "$consensus_work"' EXIT
cd "$consensus_repo"

consensus_status=0
java -XX:+UseParallelGC -cp "$TLA2TOOLS" tlc2.TLC \
    -workers 1 -seed 1 -noGenerateSpecTE \
    -metadir "$consensus_work/original" \
    -config models/non_bft/gpac/PACOriginal.cfg \
    models/non_bft/gpac/PACRecovery.tla > "$consensus_work/original.log" 2>&1 \
    || consensus_status=$?
if [[ "$consensus_status" != 12 ]] \
    || ! grep -Fq 'Invariant Agreement is violated.' "$consensus_work/original.log" \
    || ! grep -Fq '13 distinct states found' "$consensus_work/original.log"; then
    cat "$consensus_work/original.log"
    echo 'Expected the published 13-state agreement counterexample.' >&2
    exit 1
fi
echo 'Original PAC: reproduced the published agreement violation in 13 states.'

if ! java -XX:+UseParallelGC -cp "$TLA2TOOLS" tlc2.TLC \
    -workers 1 -seed 1 -noGenerateSpecTE \
    -metadir "$consensus_work/corrected" \
    -config models/non_bft/gpac/PACCorrectedReplay.cfg \
    models/non_bft/gpac/PACRecovery.tla > "$consensus_work/corrected.log" 2>&1; then
    cat "$consensus_work/corrected.log"
    exit 1
fi
if ! grep -Fq '13 distinct states found' "$consensus_work/corrected.log"; then
    cat "$consensus_work/corrected.log"
    echo 'Corrected replay did not explore all 13 expected states.' >&2
    exit 1
fi
echo 'Corrected PAC: the same replay completes and preserves agreement.'
echo 'This checks one schedule, not a general correctness theorem for G-PAC.'
