#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
example_dir="$repo_root/examples/quickstart"
scratch_dir=$(mktemp -d /tmp/tla-rs-quickstart-XXXXXX)
trap 'rm -rf -- "$scratch_dir"' EXIT

# The spec carries inline `// @automan` directives (the default form); no
# sidecar is passed.
cargo run --quiet --manifest-path "$repo_root/transpiler/Cargo.toml" -- \
  -i "$example_dir/counter_spec.rs" \
  -c "$example_dir/counter_transpile.toml" \
  -o "$scratch_dir/counter_gen.rs"

if ! cmp -s "$scratch_dir/counter_gen.rs" "$example_dir/counter_gen.rs"; then
  diff -u "$example_dir/counter_gen.rs" "$scratch_dir/counter_gen.rs" || true
  echo "README quickstart output is stale; regenerate examples/quickstart/counter_gen.rs" >&2
  exit 1
fi

if grep -Eq 'assume\s*\(|admit\s*\(|external_body' "$example_dir/counter_gen.rs"; then
  echo "README quickstart must not contain proof shortcuts" >&2
  exit 1
fi

if [[ -n "${VERUS_PATH:-}" ]]; then
  "$VERUS_PATH" --compile "$example_dir/main.rs" -o "$scratch_dir/counter"
  actual_output=$("$scratch_dir/counter")
  if [[ "$actual_output" != "Counter: 0 -> 1" ]]; then
    echo "unexpected README quickstart output: $actual_output" >&2
    exit 1
  fi
fi
