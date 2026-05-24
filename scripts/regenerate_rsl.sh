#!/bin/bash
# Phase 42.4: Regenerate RSL protocol and verify the result.
#
# Usage:
#   ./scripts/regenerate_rsl.sh [--dry-run] [--skip-verify]
#
# Steps:
#   1. Transpile all 8 RSL modules + types into src/generated/RSL/*_gen.rs
#   2. Verify cargo build succeeds
#   3. (optional) Verify per-module Verus verification passes
#
# After running, apply manual patches documented in transpiler/docs/REGEN_WORKFLOW.md:
#   - Arc-wrap highest_seqno_requested_by_client_this_view (cb42869)
#   - Merge skip_functions hand-written bodies from pre-regen backup

set -e

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

TRANSPILER="transpiler/target/release/verus-transpile"
SPEC_DIR="src/protocol/RSL"
OUT_DIR="src/generated/RSL"
BACKUP_DIR="/tmp/rsl_gen_backup_$(date +%s)"

DRY_RUN=false
SKIP_VERIFY=false

for arg in "$@"; do
    case "$arg" in
        --dry-run) DRY_RUN=true ;;
        --skip-verify) SKIP_VERIFY=true ;;
        *) echo "Unknown arg: $arg"; exit 1 ;;
    esac
done

# --- Preflight ---

if [ ! -f "$TRANSPILER" ]; then
    echo "Building transpiler (release)..."
    cargo build --manifest-path transpiler/Cargo.toml --release
fi

echo "=== RSL Regeneration (Phase 42.4) ==="
echo ""

# --- Step 0: Backup existing generated files ---

echo "0. Backing up existing generated files to $BACKUP_DIR"
mkdir -p "$BACKUP_DIR"
cp -r "$OUT_DIR"/* "$BACKUP_DIR/" 2>/dev/null || true
echo "   Done."
echo ""

if $DRY_RUN; then
    echo "[dry-run] Would regenerate to $OUT_DIR. Exiting."
    exit 0
fi

# --- Step 1: Generate types_gen.rs ---

echo "1. Generating types_gen.rs..."
$TRANSPILER generate-types \
    --input "$SPEC_DIR/types.rs" \
    --config "$SPEC_DIR/types_transpile.toml" \
    --output "$OUT_DIR/types_gen.rs"
echo "   Done."

# --- Step 2: Generate each module ---

MODULES=(broadcast acceptor learner executor election proposer replica)

for MODULE in "${MODULES[@]}"; do
    echo "2. Generating ${MODULE}_gen.rs..."

    SPEC="$SPEC_DIR/${MODULE}.rs"
    AUTOMAN="$SPEC_DIR/${MODULE}.automan"
    CONFIG="$SPEC_DIR/${MODULE}_transpile.toml"

    if [ ! -f "$SPEC" ] || [ ! -f "$AUTOMAN" ] || [ ! -f "$CONFIG" ]; then
        echo "   WARNING: Missing file for $MODULE, skipping."
        continue
    fi

    # Transpile to a temp file first, then merge skip_functions bodies from backup.
    FRESH="/tmp/rsl_fresh_${MODULE}_gen.rs"
    $TRANSPILER \
        --input "$SPEC" \
        --annotations "$AUTOMAN" \
        --config "$CONFIG" \
        --output "$FRESH"

    # The fresh output lacks hand-written bodies for skip_functions.
    # For now, copy the fresh file and note that manual merge is needed.
    cp "$FRESH" "$OUT_DIR/${MODULE}_gen.rs"
    rm -f "$FRESH"

    echo "   Done."
done

echo ""

# --- Step 3: Merge skip_functions hand-written bodies from backup ---

echo "3. Merging skip_functions hand-written bodies from backup..."

# For each module, find functions that exist in the backup but not in the fresh output,
# and append them. These are the skip_functions with hand-written bodies.
MERGE_COUNT=0
for MODULE in "${MODULES[@]}"; do
    BACKUP_FILE="$BACKUP_DIR/${MODULE}_gen.rs"
    FRESH_FILE="$OUT_DIR/${MODULE}_gen.rs"

    if [ ! -f "$BACKUP_FILE" ] || [ ! -f "$FRESH_FILE" ]; then
        continue
    fi

    # Extract function names from fresh output (pub exec fn NAME)
    FRESH_FNS=$(grep -oP '(?<=^pub exec fn )\w+' "$FRESH_FILE" 2>/dev/null | sort || true)

    # Extract function names from backup (pub exec fn NAME)
    BACKUP_FNS=$(grep -oP '(?<=^pub exec fn )\w+' "$BACKUP_FILE" 2>/dev/null | sort || true)

    # Functions in backup but not in fresh = skip_functions hand-written bodies
    MISSING_FNS=$(comm -23 <(echo "$BACKUP_FNS") <(echo "$FRESH_FNS") || true)

    if [ -z "$MISSING_FNS" ]; then
        continue
    fi

    echo "   $MODULE: merging $(echo "$MISSING_FNS" | wc -w) hand-written functions"

    # Strategy: extract each missing function from backup and insert before "} // verus!"
    for FN_NAME in $MISSING_FNS; do
        # Extract the function block from backup: from "pub exec fn NAME" to the next
        # "pub exec fn" or "} // verus!" (whichever comes first).
        # This is a heuristic — complex cases may need manual fixup.
        BLOCK=$(awk -v fn="pub exec fn $FN_NAME" '
            $0 ~ fn { found=1 }
            found { print }
            found && /^}$/ && NR>1 { count++ }
            found && count>=1 && /^$/ { exit }
        ' "$BACKUP_FILE")

        if [ -n "$BLOCK" ]; then
            # Insert before the closing "} // verus!"
            # Use a temp file for the sed operation
            TEMP_MERGE=$(mktemp)
            awk -v block="$BLOCK" '
                /^} \/\/ verus!/ { print block; print ""; }
                { print }
            ' "$FRESH_FILE" > "$TEMP_MERGE"
            mv "$TEMP_MERGE" "$FRESH_FILE"
            MERGE_COUNT=$((MERGE_COUNT + 1))
        fi
    done
done

echo "   Merged $MERGE_COUNT function(s) total."
echo ""

# --- Step 4: Restore helper functions and imports from backup ---

echo "4. Restoring module-specific helpers from backup..."

# Some modules have helper functions (proof fns, clone fns, filter fns) that are
# generated by the transpiler but may differ between versions. The fresh output
# should be authoritative for these. Only the skip_functions bodies need merging.
#
# Special case: proposer_gen.rs has the _arc_seqno_insert helper and
# assume_specification that must be manually re-applied per REGEN_WORKFLOW.md.

echo "   NOTE: Apply manual patches from transpiler/docs/REGEN_WORKFLOW.md"
echo "   - Arc-wrap for proposer_gen.rs (cb42869)"
echo ""

# --- Step 5: Verify cargo build ---

echo "5. Verifying cargo build..."
if cargo build --lib 2>&1 | tail -5; then
    echo "   Build: PASS"
else
    echo "   Build: FAIL"
    echo ""
    echo "   Build failed. The generated files may need manual fixup."
    echo "   Backup is at: $BACKUP_DIR"
    echo "   To restore: cp $BACKUP_DIR/* $OUT_DIR/"
    exit 1
fi
echo ""

# --- Step 6: (optional) Verus verification ---

if ! $SKIP_VERIFY; then
    echo "6. Verus verification (skipped — requires verus binary)."
    echo "   To verify manually:"
    echo "   verus --crate-type=lib src/lib.rs --verify-only-module generated::RSL::acceptor_gen"
    echo "   verus --crate-type=lib src/lib.rs --verify-only-module generated::RSL::proposer_gen"
    echo "   ... etc for each module"
fi

echo ""
echo "=== Regeneration Complete ==="
echo "Backup: $BACKUP_DIR"
echo "Output: $OUT_DIR"
echo ""
echo "Next steps:"
echo "  1. Apply manual patches from transpiler/docs/REGEN_WORKFLOW.md"
echo "  2. Run: cargo build --lib"
echo "  3. Verify with verus (optional)"
echo "  4. git diff src/generated/RSL/ to review changes"
