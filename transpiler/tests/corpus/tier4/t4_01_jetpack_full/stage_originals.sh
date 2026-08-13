#!/usr/bin/env bash
# Stage the upstream modules `jetpack_refinement.tla` INSTANCEs.
#
# The refinement check reads the ORIGINAL's own invariant definitions rather
# than a retyped copy -- that is the whole point of it -- so it needs the
# upstream modules present. They are NOT copied into this directory: a copy
# drifts from the thing it claims to be, and this check is worthless the moment
# it is checking a stale copy. They are generated here from
# `tier3/t3_01_jetpack/`, which is where the corpus keeps them.
#
# The only edits are the MODULE line and the INSTANCE targets, so that three
# files whose upstream names collide with the rewrite's can sit in one
# directory. Nothing else is touched -- `diff` against the tier3 originals to
# see that.
#
# `--fix-vacuous-min` additionally applies ONE line of correction to the staged
# copy: upstream's `CommittedLogAgreement` computes
# `limit == Min({ci, ci2} \cup {0})`, which is always 0, so `\A k \in 1..limit`
# compares nothing. Without the flag that invariant is checked exactly as
# upstream wrote it -- and passes vacuously. With it, the comparison is real.
# It is a flag rather than a default because editing upstream to make your own
# check look stronger is the thing this whole construction exists to avoid; you
# should have to ask.
#
#   ./stage_originals.sh <outdir> [--fix-vacuous-min]
#   cd <outdir> && java -cp tla2tools.jar tlc2.TLC -deadlock jetpack_refinement
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
upstream="$here/../../tier3/t3_01_jetpack"
out="${1:?usage: stage_originals.sh <outdir>}"

mkdir -p "$out"
cp "$here"/*.tla "$here"/*.cfg "$out"/

sed '1s/MODULE base_raft/MODULE orig_base_raft/' \
    "$upstream/base_raft.tla" > "$out/orig_base_raft.tla"
sed '1s/MODULE jetpack/MODULE orig_jetpack/' \
    "$upstream/jetpack.tla" > "$out/orig_jetpack.tla"
sed -e '1s/MODULE jetpack_raft_composition/MODULE orig_composition/' \
    -e 's/^B == INSTANCE base_raft$/B == INSTANCE orig_base_raft/' \
    -e 's/^J == INSTANCE jetpack WITH/J == INSTANCE orig_jetpack WITH/' \
    "$upstream/original.tla" > "$out/orig_composition.tla"

if [ "${2:-}" = "--fix-vacuous-min" ]; then
  before="$(grep -c 'limit == Min({ci, ci2} \\cup {0})' "$out/orig_jetpack.tla")"
  [ "$before" = "1" ] || { echo "the vacuous Min is not where it was; refusing to patch blind" >&2; exit 1; }
  sed -i 's|limit == Min({ci, ci2} \\cup {0})|limit == Min({ci, ci2})  \\* CORRECTED by stage_originals.sh --fix-vacuous-min|' \
      "$out/orig_jetpack.tla"
  echo "applied: CommittedLogAgreement's limit is now Min({ci, ci2}), not 0"
fi

echo "staged into $out:"
ls "$out"
