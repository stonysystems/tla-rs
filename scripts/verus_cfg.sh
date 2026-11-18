#!/usr/bin/env bash
# Print the `--cfg` flags this repository needs for a given Verus.
#
# Usage: scripts/verus_cfg.sh /path/to/verus
#
# vstd_hash_wf: the vstd tracks hash-table well-formedness (hash_map_wf /
#   hash_set_wf, verus-lang/verus#3494). Older vstd releases do not have these
#   predicates, so code that names them must be compiled conditionally; see
#   src/common/collections/hash_wf.rs.
set -euo pipefail
verus="${1:?usage: verus_cfg.sh /path/to/verus}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
probe_dir="$(mktemp -d)"
trap 'rm -rf "$probe_dir"' EXIT
if "$verus" "$root/scripts/probes/vstd_hash_wf.rs" --crate-type=lib --no-verify \
    -o "$probe_dir/probe.rlib" >/dev/null 2>&1; then
    echo "--cfg vstd_hash_wf"
fi
