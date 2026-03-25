#!/usr/bin/env bash
# Regenerate the entire tla-rs corpus from TLA+ sources.
#
# This script translates all 20 TLA+ cases from tests/tla/ into tests/tla-rs/
# using the repo's real transpiler (verus-transpile translate-tla).
#
# Usage:
#   ./scripts/regenerate_corpus.sh              # from the DPOR workfolder
#   ./scripts/regenerate_corpus.sh --verbose    # show per-case output
#
# The script:
# 1. Builds the transpiler if needed
# 2. For each case in tests/tla/, finds the main .tla entry file
# 3. Translates it to tests/tla-rs/<case_id>/
# 4. Records success/failure per case
# 5. Prints a summary

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORKFOLDER="$(cd "$SCRIPT_DIR/.." && pwd)"
REPO_ROOT="$(cd "$WORKFOLDER/../.." && pwd)"
TRANSPILER_DIR="$REPO_ROOT/transpiler"
TLA_DIR="$WORKFOLDER/tests/tla"
TLARS_DIR="$WORKFOLDER/tests/tla-rs"
MANIFEST="$WORKFOLDER/tests/manifest.toml"

VERBOSE=false
if [[ "${1:-}" == "--verbose" ]]; then
    VERBOSE=true
fi

# Build the transpiler
echo "Building transpiler..."
cargo build --manifest-path "$TRANSPILER_DIR/Cargo.toml" --bin verus-transpile 2>/dev/null
TRANSPILER="$TRANSPILER_DIR/target/debug/verus-transpile"

if [[ ! -x "$TRANSPILER" ]]; then
    echo "Error: transpiler binary not found at $TRANSPILER" >&2
    exit 1
fi

# Clean and recreate output directory
rm -rf "$TLARS_DIR"
mkdir -p "$TLARS_DIR"

# Counters
TOTAL=0
SUCCESS=0
FAILED=0
SKIPPED=0

# Process each case directory
for case_dir in "$TLA_DIR"/*/; do
    case_id="$(basename "$case_dir")"
    TOTAL=$((TOTAL + 1))

    # Read tla_entry from manifest.toml for this case
    # Simple grep-based extraction (not a full TOML parser)
    tla_entry=""
    in_case=false
    while IFS= read -r line; do
        if [[ "$line" == *"id = \"$case_id\""* ]]; then
            in_case=true
        elif $in_case && [[ "$line" == "[[case]]"* ]]; then
            break
        elif $in_case && [[ "$line" == tla_entry* ]]; then
            tla_entry="$(echo "$line" | sed 's/tla_entry = "\(.*\)"/\1/')"
        fi
    done < "$MANIFEST"

    if [[ -z "$tla_entry" ]]; then
        echo "  [$case_id] SKIP: no tla_entry in manifest"
        SKIPPED=$((SKIPPED + 1))
        continue
    fi

    input_file="$case_dir/$tla_entry"
    if [[ ! -f "$input_file" ]]; then
        echo "  [$case_id] SKIP: $tla_entry not found"
        SKIPPED=$((SKIPPED + 1))
        continue
    fi

    # Create output directory mirroring the case structure
    output_dir="$TLARS_DIR/$case_id"
    mkdir -p "$output_dir"

    # Derive output filename: TLA+ module name → .rs
    output_file="$output_dir/${tla_entry%.tla}.rs"

    # Translate
    if $VERBOSE; then
        echo "  [$case_id] Translating $tla_entry..."
    fi

    if "$TRANSPILER" translate-tla \
        --input "$input_file" \
        --output "$output_file" \
        --gen-modes 2>/tmp/dpor_translate_err_${case_id}.txt; then
        echo "  [$case_id] OK: $tla_entry -> $(basename "$output_file")"
        SUCCESS=$((SUCCESS + 1))

        # Also translate auxiliary modules if they exist
        for aux_file in "$case_dir"/*.tla; do
            aux_name="$(basename "$aux_file")"
            if [[ "$aux_name" != "$tla_entry" ]]; then
                aux_output="$output_dir/${aux_name%.tla}.rs"
                if "$TRANSPILER" translate-tla \
                    --input "$aux_file" \
                    --output "$aux_output" \
                    --gen-modes 2>/dev/null; then
                    if $VERBOSE; then
                        echo "    + $aux_name -> $(basename "$aux_output")"
                    fi
                else
                    if $VERBOSE; then
                        echo "    ! $aux_name: translation failed (auxiliary)"
                    fi
                fi
            fi
        done
    else
        err_msg="$(cat /tmp/dpor_translate_err_${case_id}.txt 2>/dev/null | tail -1)"
        echo "  [$case_id] FAIL: $tla_entry ($err_msg)"
        FAILED=$((FAILED + 1))
        # Record failure marker
        echo "translation_failed" > "$output_dir/TRANSLATION_FAILED"
    fi

    # Clean up temp error file
    rm -f /tmp/dpor_translate_err_${case_id}.txt
done

echo ""
echo "========================================"
echo "Corpus Regeneration Summary"
echo "========================================"
echo "  Total cases: $TOTAL"
echo "  Success:     $SUCCESS"
echo "  Failed:      $FAILED"
echo "  Skipped:     $SKIPPED"
echo "========================================"

if [[ $FAILED -gt 0 ]]; then
    echo "WARNING: $FAILED cases failed translation. Check tests/tla-rs/*/TRANSLATION_FAILED"
fi
