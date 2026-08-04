#!/usr/bin/env bash
# Refresh every corpus golden's `verus! { .. }` block from the translator,
# leaving the hand-written header prose alone.
#
# A golden is two things at once: the bytes the V3 guard compares (the verus!
# block) and the review notes that say why those bytes are right (the header).
# Only the first is generated, so overwriting the whole file with
# `clean-tla --output` destroys the review -- which is the part a human wrote.
#
#   tests/corpus/scripts/refresh_goldens.sh [case-dir ...]
#
# With no arguments, every case that has both a clean.tla and a golden.rs.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
corpus="$(dirname "$here")"
transpiler="$(dirname "$(dirname "$corpus")")"
bin="$transpiler/target/debug/verus-transpile"

[ -x "$bin" ] || { echo "build the transpiler first: cargo build" >&2; exit 1; }

cases=("$@")
if [ ${#cases[@]} -eq 0 ]; then
  mapfile -t cases < <(find "$corpus" -name golden.rs -printf '%h\n' | sort)
fi

for case_dir in "${cases[@]}"; do
  clean="$case_dir/clean.tla"
  golden="$case_dir/golden.rs"
  [ -f "$clean" ] && [ -f "$golden" ] || continue

  emitted="$(mktemp)"
  if ! "$bin" clean-tla "$clean" --output "$emitted" 2>"$emitted.err"; then
    echo "SKIP $(basename "$case_dir"): $(head -1 "$emitted.err")"
    rm -f "$emitted" "$emitted.err"
    continue
  fi

  python3 - "$golden" "$emitted" <<'PY'
import sys

golden_path, emitted_path = sys.argv[1], sys.argv[2]
golden = open(golden_path).read()
emitted = open(emitted_path).read()

def verus_block(text):
    start = text.index("verus! {")
    return start, text.rindex("}\n") + 2

gs, ge = verus_block(golden)
es, ee = verus_block(emitted)
new = golden[:gs] + emitted[es:ee] + golden[ge:]
if new != golden:
    open(golden_path, "w").write(new)
    print(f"updated {golden_path}")
PY
  rm -f "$emitted" "$emitted.err"
done
