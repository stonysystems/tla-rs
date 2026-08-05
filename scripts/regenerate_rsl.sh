#!/bin/bash
# Phase 42.4: Regenerate RSL protocol and validate the result.
#
# Usage:
#   ./scripts/regenerate_rsl.sh [--dry-run] [--validate-only]
#
# Modes:
#   (default)        Regenerate all 8 RSL modules, preserving skip_functions
#                    bodies from the existing files.  After regen, apply manual
#                    patches documented in transpiler/docs/REGEN_WORKFLOW.md.
#   --validate-only  Compare fresh transpiler output against existing generated
#                    files.  Report parity (no files modified).
#   --dry-run        Show what would be done, then exit.
#
# The transpiler cannot auto-generate bodies for skip_functions (quantified
# map filtering, existential witnesses, complex I/O dispatch).  This script
# preserves those hand-written bodies by copying them from the pre-regen backup.
# For details, see transpiler/docs/REGEN_WORKFLOW.md.

set -e

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

TRANSPILER="transpiler/target/release/verus-transpile"
SPEC_DIR="src/protocol/RSL"
OUT_DIR="src/generated/RSL"

DRY_RUN=false
VALIDATE_ONLY=false

for arg in "$@"; do
    case "$arg" in
        --dry-run) DRY_RUN=true ;;
        --validate-only) VALIDATE_ONLY=true ;;
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

if $DRY_RUN; then
    echo "[dry-run] Would regenerate to $OUT_DIR. Exiting."
    exit 0
fi

# --- Step 1: Generate fresh transpiler output to a temp directory ---

FRESH_DIR=$(mktemp -d /tmp/rsl_fresh_XXXXXX)
trap "rm -rf $FRESH_DIR" EXIT

echo "1. Generating fresh transpiler output to $FRESH_DIR..."

# Types
$TRANSPILER generate-types \
    --input "$SPEC_DIR/types.rs" \
    --config "$SPEC_DIR/types_transpile.toml" \
    --output "$FRESH_DIR/types_gen.rs"
# Phase 42.7: rustfmt the emitted types so the output is byte-comparable with
# the checked-in file. Without this the two differ only in `use` ordering and
# line wrapping, which reads as a large diff and hides whether anything real
# changed -- that is what made regeneration look lossy.
if command -v rustfmt >/dev/null 2>&1; then
    rustfmt --edition 2021 "$FRESH_DIR/types_gen.rs" || true
fi
echo "   types_gen.rs: done"

# Modules
MODULES=(broadcast acceptor learner executor election proposer replica)

for MODULE in "${MODULES[@]}"; do
    SPEC="$SPEC_DIR/${MODULE}.rs"
    AUTOMAN="$SPEC_DIR/${MODULE}.automan"
    CONFIG="$SPEC_DIR/${MODULE}_transpile.toml"

    if [ ! -f "$SPEC" ] || [ ! -f "$AUTOMAN" ] || [ ! -f "$CONFIG" ]; then
        echo "   WARNING: Missing file for $MODULE, skipping."
        continue
    fi

    $TRANSPILER \
        --input "$SPEC" \
        --annotations "$AUTOMAN" \
        --config "$CONFIG" \
        --output "$FRESH_DIR/${MODULE}_gen.rs"

    echo "   ${MODULE}_gen.rs: done"
done
echo ""

# --- Step 2: Compare fresh output against existing generated files ---

echo "2. Comparing fresh output against existing generated files..."
echo ""

PARITY_OK=true

for MODULE in types broadcast acceptor learner executor election proposer replica; do
    FRESH_FILE="$FRESH_DIR/${MODULE}_gen.rs"
    EXISTING_FILE="$OUT_DIR/${MODULE}_gen.rs"

    if [ ! -f "$EXISTING_FILE" ]; then
        echo "   $MODULE: MISSING (no existing file)"
        PARITY_OK=false
        continue
    fi

    # Extract "pub exec fn NAME" from both files
    FRESH_FNS=$(grep -oP '(?<=^pub exec fn )\w+' "$FRESH_FILE" 2>/dev/null | sort || true)
    EXISTING_FNS=$(grep -oP '(?<=^pub exec fn )\w+' "$EXISTING_FILE" 2>/dev/null | sort || true)

    # Functions in fresh but not in existing = unexpected new functions
    ONLY_FRESH=$(comm -23 <(echo "$FRESH_FNS") <(echo "$EXISTING_FNS") || true)
    # Functions in existing but not in fresh = skip_functions (expected)
    ONLY_EXISTING=$(comm -13 <(echo "$FRESH_FNS") <(echo "$EXISTING_FNS") || true)

    if [ -z "$ONLY_FRESH" ] && [ -z "$ONLY_EXISTING" ]; then
        echo "   $MODULE: PARITY ($(echo "$FRESH_FNS" | wc -w) functions)"
    else
        if [ -n "$ONLY_EXISTING" ]; then
            COUNT=$(echo "$ONLY_EXISTING" | wc -w)
            echo "   $MODULE: $COUNT skip_functions in existing only: $(echo $ONLY_EXISTING | tr '\n' ' ')"
        fi
        if [ -n "$ONLY_FRESH" ]; then
            COUNT=$(echo "$ONLY_FRESH" | wc -w)
            echo "   $MODULE: WARNING: $COUNT functions in fresh only: $(echo $ONLY_FRESH | tr '\n' ' ')"
            PARITY_OK=false
        fi
    fi
done

echo ""

if $VALIDATE_ONLY; then
    if $PARITY_OK; then
        echo "=== Validation PASSED ==="
        echo "All transpiler-emitted functions match existing generated files."
        echo "skip_functions hand-written bodies are preserved in existing files."
    else
        echo "=== Validation FAILED ==="
        echo "Unexpected function differences found (see above)."
        exit 1
    fi
    exit 0
fi

# --- Step 3: Regenerate (replace transpiler-emitted code, preserve skip_functions) ---

echo "3. Backing up existing generated files..."
BACKUP_DIR="/tmp/rsl_gen_backup_$(date +%s)"
mkdir -p "$BACKUP_DIR"
cp -r "$OUT_DIR"/* "$BACKUP_DIR/" 2>/dev/null || true
echo "   Backup: $BACKUP_DIR"
echo ""

echo "4. Installing fresh transpiler output..."
for MODULE in types broadcast acceptor learner executor election proposer replica; do
    FRESH_FILE="$FRESH_DIR/${MODULE}_gen.rs"
    EXISTING_FILE="$OUT_DIR/${MODULE}_gen.rs"

    if [ ! -f "$FRESH_FILE" ]; then
        continue
    fi

    # For types and broadcast (no skip_functions), just copy fresh output
    EXISTING_FNS=$(grep -oP '(?<=^pub exec fn )\w+' "$EXISTING_FILE" 2>/dev/null | sort || true)
    FRESH_FNS=$(grep -oP '(?<=^pub exec fn )\w+' "$FRESH_FILE" 2>/dev/null | sort || true)
    ONLY_EXISTING=$(comm -13 <(echo "$FRESH_FNS") <(echo "$EXISTING_FNS") || true)

    if [ -z "$ONLY_EXISTING" ]; then
        # No skip_functions — safe to replace entirely
        cp "$FRESH_FILE" "$EXISTING_FILE"
        echo "   $MODULE: replaced (no skip_functions)"
    else
        # Has skip_functions — keep existing file (it has the hand-written bodies)
        # Just report what would need manual review
        echo "   $MODULE: KEPT EXISTING (has $(echo $ONLY_EXISTING | wc -w) skip_functions)"
        echo "     To update: diff $FRESH_FILE $EXISTING_FILE"
        echo "     skip_functions: $(echo $ONLY_EXISTING | tr '\n' ' ')"
    fi
done
echo ""

echo "=== Regeneration Complete ==="
echo "Backup: $BACKUP_DIR"
echo "Output: $OUT_DIR"
echo ""
echo "Modules with skip_functions were NOT replaced (hand-written bodies preserved)."
echo "To update transpiler-emitted code in those modules, merge with the tool rather"
echo "than by hand -- it protects helpers the transpiler would otherwise overwrite:"
echo ""
PRESERVE_LIST="$REPO_ROOT/scripts/rsl_merge_preserve.txt"
for MODULE in types broadcast acceptor learner executor election proposer replica; do
    [ -f "$FRESH_DIR/${MODULE}_gen.rs" ] || continue
    FLAGS=""
    if [ -f "$PRESERVE_LIST" ]; then
        while read -r PMOD PFN; do
            case "$PMOD" in ''#''*|"") continue ;; esac
            [ "$PMOD" = "$MODULE" ] && FLAGS="$FLAGS --preserve $PFN"
        done < "$PRESERVE_LIST"
    fi
    echo "  python3 scripts/merge_generated.py \\"
    echo "      $FRESH_DIR/${MODULE}_gen.rs $OUT_DIR/${MODULE}_gen.rs$FLAGS \\"
    echo "      -o $OUT_DIR/${MODULE}_gen.rs && rustfmt --edition 2021 $OUT_DIR/${MODULE}_gen.rs"
done
echo ""
echo "The --preserve flags come from scripts/rsl_merge_preserve.txt. Without them the"
echo "merge silently replaces hand-verified helper bodies with naive transpiler output,"
echo "and the parity check above will not notice: it compares \`pub exec fn\` *names*,"
echo "so a body swap on a private \`fn\` is invisible to it."
echo ""
echo "After any changes, apply manual patches from transpiler/docs/REGEN_WORKFLOW.md:"
echo "  - Arc-wrap for proposer_gen.rs (cb42869)"
echo ""
echo "Verify with verus (requires verus binary):"
echo "  verus --crate-type=lib src/lib.rs --verify-only-module generated::RSL::acceptor_gen"
