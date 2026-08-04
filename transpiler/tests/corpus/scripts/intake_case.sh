#!/usr/bin/env bash
#
# Phase 53.1 — corpus intake.
#
# Downloads a TLA+ spec from the wild into a new corpus case directory, pins the
# upstream commit so the download is reproducible, scaffolds the four-tuple, and
# (once Phase 52.M0 lands) measures the case's clean-distance with the linter.
#
# Usage:
#   intake_case.sh --tier 0 --id t0_01_peterson \
#       --url https://raw.githubusercontent.com/tlaplus/Examples/master/specifications/TeachingConcurrency/Simple.tla \
#       [--aux <url>]... [--cfg <url>] [--reference src/protocol/Paxos/paxos.rs] \
#       [--append-manifest] [--force]
#
# Exit codes: 0 ok, 1 usage error, 2 download failure.
set -euo pipefail

CORPUS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REPO_ROOT="$(cd "$CORPUS_DIR/../../.." && pwd)"
MANIFEST="$CORPUS_DIR/manifest.toml"

TIER=""; ID=""; URL=""; CFG_URL=""; REFERENCE=""; APPEND=0; FORCE=0
AUX_URLS=()

die() { echo "error: $*" >&2; exit 1; }

while [ $# -gt 0 ]; do
  case "$1" in
    --tier)             TIER="$2"; shift 2 ;;
    --id)               ID="$2"; shift 2 ;;
    --url)              URL="$2"; shift 2 ;;
    --aux)              AUX_URLS+=("$2"); shift 2 ;;
    --cfg)              CFG_URL="$2"; shift 2 ;;
    --reference)        REFERENCE="$2"; shift 2 ;;
    --append-manifest)  APPEND=1; shift ;;
    --force)            FORCE=1; shift ;;
    -h|--help)          sed -n '2,20p' "$0"; exit 0 ;;
    *)                  die "unknown argument: $1" ;;
  esac
done

[ -n "$TIER" ] || die "--tier is required"
[ -n "$ID" ]   || die "--id is required"
[ -n "$URL" ]  || die "--url is required"
case "$TIER" in 0|1|2|3) ;; *) die "--tier must be 0..3" ;; esac

CASE_DIR="$CORPUS_DIR/tier$TIER/$ID"
if [ -d "$CASE_DIR" ] && [ "$FORCE" -eq 0 ]; then
  die "$CASE_DIR already exists (use --force to re-intake; original.tla will be overwritten)"
fi
mkdir -p "$CASE_DIR"

# ---------------------------------------------------------------------------
# Pin the upstream commit. For raw.githubusercontent.com/<o>/<r>/<ref>/<path>
# we ask the API for the last commit touching <path> at <ref> and re-fetch from
# that sha, so a later re-run gets byte-identical content.
# ---------------------------------------------------------------------------
SOURCE_REPO="unknown"; SOURCE_PATH=""; SOURCE_COMMIT=""
# Sets PINNED_URL (and, for the primary spec, SOURCE_{REPO,PATH,COMMIT}).
# Deliberately not a command substitution: the metadata has to survive the call.
PINNED_URL=""
pin_url() {
  local url="$1" record_meta="${2:-0}"
  PINNED_URL="$url"
  if [[ "$url" =~ ^https://raw\.githubusercontent\.com/([^/]+)/([^/]+)/([^/]+)/(.*)$ ]]; then
    local owner="${BASH_REMATCH[1]}" repo="${BASH_REMATCH[2]}"
    local ref="${BASH_REMATCH[3]}" path="${BASH_REMATCH[4]}"
    local sha
    sha=$(curl -sS --max-time 30 \
      "https://api.github.com/repos/$owner/$repo/commits?path=$path&sha=$ref&per_page=1" \
      | python3 -c 'import json,sys
try:
    d=json.load(sys.stdin)
    print(d[0]["sha"] if isinstance(d,list) and d else "")
except Exception:
    print("")' 2>/dev/null) || sha=""
    if [ "$record_meta" = "1" ]; then
      SOURCE_REPO="$owner/$repo"; SOURCE_PATH="$path"; SOURCE_COMMIT="$sha"
    fi
    if [ -n "$sha" ]; then
      PINNED_URL="https://raw.githubusercontent.com/$owner/$repo/$sha/$path"
    else
      echo "warning: could not pin commit for $path; falling back to '$ref'" >&2
    fi
  fi
}

fetch() {  # fetch <url> <dest>
  local url="$1" dest="$2"
  if ! curl -sSfL --max-time 120 -o "$dest" "$url"; then
    echo "error: download failed: $url" >&2
    exit 2
  fi
}

pin_url "$URL" 1
fetch "$PINNED_URL" "$CASE_DIR/original.tla"
echo "intake: original.tla  <- $PINNED_URL"

for aux in ${AUX_URLS+"${AUX_URLS[@]}"}; do
  pin_url "$aux"
  fetch "$PINNED_URL" "$CASE_DIR/$(basename "${aux%%\?*}")"
  echo "intake: $(basename "${aux%%\?*}")  <- $PINNED_URL"
done

if [ -n "$CFG_URL" ]; then
  pin_url "$CFG_URL"
  fetch "$PINNED_URL" "$CASE_DIR/original.cfg"
  echo "intake: original.cfg  <- $PINNED_URL"
fi

if [ -n "$REFERENCE" ]; then
  if [ -f "$REPO_ROOT/$REFERENCE" ]; then
    cp "$REPO_ROOT/$REFERENCE" "$CASE_DIR/reference.rs"
    echo "intake: reference.rs  <- $REFERENCE (review aid only, never byte-diffed)"
  else
    echo "warning: reference $REFERENCE not found under $REPO_ROOT" >&2
  fi
fi

# ---------------------------------------------------------------------------
# Clean-distance: how many C1-C5 violations does original.tla have?
# The linter is Phase 52.M0; until it exists this stays "unmeasured".
# Contract: `verus-transpile tla-lint --json <file>` prints {"violations": N, ...}.
# ---------------------------------------------------------------------------
CLEAN_DISTANCE="unmeasured"
measure_clean_distance() {
  local out
  if ! out=$(cd "$REPO_ROOT/transpiler" && cargo run --quiet -- tla-lint --json "$CASE_DIR/original.tla" 2>/dev/null); then
    return 1
  fi
  python3 -c 'import json,sys
try:
    print(json.loads(sys.stdin.read())["violations"])
except Exception:
    sys.exit(1)' <<<"$out"
}
if n=$(measure_clean_distance); then
  CLEAN_DISTANCE="$n"
  echo "intake: clean-distance = $n C1-C5 violations"
else
  echo "intake: clean-distance unmeasured (Phase 52.M0 linter not available yet)"
fi

# ---------------------------------------------------------------------------
# Scaffold the human-authored half of the four-tuple.
# ---------------------------------------------------------------------------
if [ ! -f "$CASE_DIR/rewrite.md" ]; then
  cat > "$CASE_DIR/rewrite.md" <<EOF
# $ID — rewrite notes

**Source**: \`$SOURCE_REPO\` \`$SOURCE_PATH\`
**Pinned commit**: \`${SOURCE_COMMIT:-unpinned}\`
**Clean-distance at intake**: $CLEAN_DISTANCE

> Fill this in while writing \`clean.tla\`. It is the record of what a human decided,
> and it is what makes the rewrite reviewable. Do not leave TODOs in a case that is
> marked \`clean\` in the manifest.

## Which variable is the network (C4)

TODO — name the message variable, and the operators used to send/receive it.

## History variables removed (C3)

TODO — list each removed ghost/history variable and why it was safe to drop.

## Instantaneous cross-node reads message-ified (C2)

TODO — for each \`x[other]\` read: what message now carries that value, who sends it,
and what the receiving action does with it.

## Out-of-subset constructs stripped

TODO — reconfiguration (view/epoch) per Q2, and anything else dropped.

## Semantic-fidelity claim (V2)

TODO — how \`clean.tla\` was checked against \`original.tla\` with TLC: config, bounds,
observables compared, result.

## Golden review (before freezing golden.rs)

TODO — what was diffed against \`reference.rs\` (if any) and what differences were
accepted, with reasons.
EOF
  echo "intake: rewrite.md scaffolded"
fi

[ -f "$CASE_DIR/clean.tla" ] || cat > "$CASE_DIR/clean.tla" <<EOF
\\* $ID — clean-subset rewrite of original.tla.
\\* Not yet written. See rewrite.md. Delete this placeholder when starting the rewrite.
EOF

# ---------------------------------------------------------------------------
# Manifest entry.
# ---------------------------------------------------------------------------
ENTRY=$(cat <<EOF

[[case]]
id = "$ID"
tier = $TIER
status = "intake"
source_repo = "$SOURCE_REPO"
source_path = "$SOURCE_PATH"
source_commit = "$SOURCE_COMMIT"
golden_kind = "bootstrapped"
reference = "$REFERENCE"
clean_distance = "$CLEAN_DISTANCE"
milestone_gate = ""
notes = ""
EOF
)

if [ "$APPEND" -eq 1 ]; then
  if grep -q "^id = \"$ID\"$" "$MANIFEST"; then
    echo "intake: manifest already has '$ID' — update its status/clean_distance by hand"
  else
    printf '%s\n' "$ENTRY" >> "$MANIFEST"
    echo "intake: appended '$ID' to manifest.toml"
  fi
else
  echo "intake: manifest entry (add with --append-manifest, or paste):"
  printf '%s\n' "$ENTRY"
fi

echo "intake: done -> ${CASE_DIR#"$REPO_ROOT"/}"
