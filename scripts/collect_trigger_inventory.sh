#!/usr/bin/env bash
# Capture a Verus verification log and turn it into a trigger inventory
# (Phase 54.1 tooling; Phase 54.2 uses it to record the baseline).
#
# Usage:
#   scripts/collect_trigger_inventory.sh --verus-path /path/to/verus \
#       [--label "0.2026.08.02 full"] [--out-dir reports/triggers] \
#       [--triggers-mode selective|all-modules|verbose] [--keep-log]
#
# Writes <out-dir>/<slug>.json and <out-dir>/<slug>.md, where <slug> is derived
# from the Verus version and the trigger mode. The raw log is written to
# <out-dir>/<slug>.log and deleted afterwards unless --keep-log is given (logs
# are large and are regenerable; the JSON inventory is the artifact of record).
#
# Note: `--triggers-mode selective` (the Verus default) reports only the
# ambiguous cases; `all-modules` reports every automatically chosen trigger.
# The two counts are not comparable, so the mode is recorded in the label and
# in the output file name.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERUS=""
LABEL=""
OUT_DIR="$REPO_ROOT/reports/triggers"
MODE="all-modules"
KEEP_LOG=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --verus-path) VERUS="$2"; shift 2 ;;
    --label) LABEL="$2"; shift 2 ;;
    --out-dir) OUT_DIR="$2"; shift 2 ;;
    --triggers-mode) MODE="$2"; shift 2 ;;
    --keep-log) KEEP_LOG=1; shift ;;
    -h|--help) sed -n '2,20p' "${BASH_SOURCE[0]}"; exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

if [[ -z "$VERUS" ]]; then
  echo "error: --verus-path is required (this repo pins release/0.2026.08.02.b677dd5)" >&2
  exit 2
fi
if [[ ! -x "$VERUS" ]]; then
  echo "error: $VERUS is not executable" >&2
  exit 2
fi

VERSION="$("$VERUS" --version 2>&1 | awk '/Version:/ {print $2}' | head -1)"
if [[ -z "$VERSION" ]]; then
  echo "error: could not read the Verus version from $VERUS" >&2
  exit 2
fi

SLUG="${VERSION}-${MODE}"
mkdir -p "$OUT_DIR"
LOG="$OUT_DIR/$SLUG.log"
JSON="$OUT_DIR/$SLUG.json"
MD="$OUT_DIR/$SLUG.md"

echo "verus       : $VERUS ($VERSION)"
echo "trigger mode: $MODE"
echo "out         : $JSON"
echo

cd "$REPO_ROOT"
# Verus exits non-zero when the crate has verification errors; the trigger
# notes are still emitted, so capture them either way and report the status.
set +e
"$VERUS" --crate-type=lib src/lib.rs --triggers-mode "$MODE" >"$LOG" 2>&1
VERUS_STATUS=$?
set -e
echo "verus exit status: $VERUS_STATUS"
tail -1 "$LOG" || true
echo

python3 "$REPO_ROOT/scripts/trigger_inventory.py" parse "$LOG" \
  --label "${LABEL:-$VERSION $MODE}" \
  --verus-version "$VERSION" \
  --root "$REPO_ROOT" \
  -o "$JSON"

python3 "$REPO_ROOT/scripts/trigger_inventory.py" report "$JSON" -o "$MD"

if [[ "$KEEP_LOG" -eq 0 ]]; then
  rm -f "$LOG"
fi

echo
echo "wrote $JSON"
echo "wrote $MD"
