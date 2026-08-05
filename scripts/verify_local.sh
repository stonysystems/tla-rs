#!/usr/bin/env bash
# Run the pinned Verus over the working tree, bypassing the `verus` launcher.
#
# Why this exists: the release `verus` launcher binary is linked against
# glibc 2.39, so on an older host it aborts before doing anything. That is a
# property of the *launcher*, not of the verifier — `rust_verify` itself needs
# only 2.34. The launcher's whole job is to set three variables and exec
# rust_verify, so reproducing them runs the real verifier on hosts where the
# launcher will not start:
#
#   RUSTUP_TOOLCHAIN   the toolchain rust_verify was built against
#   LD_LIBRARY_PATH    that toolchain's lib/ (for librustc_driver etc.)
#   VERUS_Z3_PATH      a z3 binary of the version Verus checks for
#
# The bundled z3 4.16.0 also wants glibc 2.38; the PyPI `z3-solver==4.16.0`
# wheel is manylinux_2_27 and satisfies Verus's version check, so it is a drop-in
# replacement on older hosts.
#
# Usage:
#   scripts/verify_local.sh                        # verify the working tree
#   scripts/verify_local.sh --time-expanded        # ... with per-module timings
#   scripts/verify_local.sh --triggers-mode all-modules
#   VERUS_DIR=/path/to/verus-x86-linux scripts/verify_local.sh
#
# Environment overrides (defaults are this dev box's cache):
#   VERUS_DIR   directory holding rust_verify        (default /tmp/verus-test/verus/<pin>/verus-x86-linux)
#   VERUS_TC    rustup toolchain name                (default 1.97.1-x86_64-unknown-linux-gnu)
#   RUSTUP_DIR  rustup home                          (default /tmp/verus-test/rustup)
#   Z3_PATH     z3 binary                            (default the PyPI 4.16.0 wheel's z3)
#   LOG         where to write the verification log  (default verus-verify.log)
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERUS_PIN="${VERUS_PIN:-0.2026.08.02.b677dd5}"
VERUS_DIR="${VERUS_DIR:-/tmp/verus-test/verus/${VERUS_PIN}/verus-x86-linux}"
VERUS_TC="${VERUS_TC:-1.97.1-x86_64-unknown-linux-gnu}"
RUSTUP_DIR="${RUSTUP_DIR:-/tmp/verus-test/rustup}"
Z3_PATH="${Z3_PATH:-/tmp/verus-test/z3pip/z3_solver-4.16.0.0.data/data/bin/z3}"
LOG="${LOG:-$REPO_ROOT/verus-verify.log}"

RUST_VERIFY="$VERUS_DIR/rust_verify"
for f in "$RUST_VERIFY" "$Z3_PATH"; do
  if [[ ! -x "$f" ]]; then
    echo "error: $f is missing or not executable" >&2
    echo "hint: set VERUS_DIR / Z3_PATH, or install the release + z3-solver wheel" >&2
    exit 2
  fi
done
if [[ ! -d "$RUSTUP_DIR/toolchains/$VERUS_TC" ]]; then
  echo "error: toolchain $VERUS_TC not found under $RUSTUP_DIR/toolchains" >&2
  exit 2
fi

export RUSTUP_HOME="$RUSTUP_DIR"
export RUSTUP_TOOLCHAIN="$VERUS_TC"
export LD_LIBRARY_PATH="$RUSTUP_DIR/toolchains/$VERUS_TC/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
export VERUS_Z3_PATH="$Z3_PATH"

cd "$REPO_ROOT"
START=$(date +%s)
set +e
"$RUST_VERIFY" --crate-type=dylib --expand-errors "$@" src/lib.rs >"$LOG" 2>&1
STATUS=$?
set -e
ELAPSED=$(( $(date +%s) - START ))

RESULT="$(grep -m1 'verification results::' "$LOG" | sed 's/.*results:: //' || true)"
echo "verus     : $VERUS_PIN"
echo "result    : ${RESULT:-<none — see $LOG>}"
echo "wall clock: ${ELAPSED}s"
echo "triggers  : $(grep -c 'automatically chose triggers' "$LOG" || true) auto-chosen notes"
echo "log       : $LOG"
exit $STATUS
