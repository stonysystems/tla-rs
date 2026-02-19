#!/bin/bash
# Phase 14.4: Regenerate RSL (Multi-Module Protocol)
# This script regenerates the RSL protocol into src/generated_fresh/RSL/

set -e  # Exit on error

TRANSPILER="transpiler/target/release/verus-transpile"

if [ ! -f "$TRANSPILER" ]; then
    echo "Error: Transpiler not found at $TRANSPILER"
    echo "Please run: cd transpiler && cargo build --release"
    exit 1
fi

SPEC_DIR="src/protocol/RSL"
OUT_DIR="src/generated_fresh/RSL"

echo "Starting Phase 14.4: Regenerating RSL Protocol"
echo "=============================================="
echo ""

# Ensure output directory exists
mkdir -p "$OUT_DIR"

# Step 1: Generate types_gen.rs
echo "1. Generating types_gen.rs..."
$TRANSPILER generate-types \
    --input "$SPEC_DIR/types.rs" \
    --config "$SPEC_DIR/types_transpile.toml" \
    --output "$OUT_DIR/types_gen.rs" || {
    echo "ERROR: Type generation failed"
    exit 1
}
echo "  ✓ types_gen.rs complete"
echo ""

# RSL modules in dependency order
declare -a MODULES=(
    "broadcast"
    "acceptor"
    "learner"
    "executor"
    "election"
    "proposer"
    "replica"
)

# Step 2: Generate each module
for MODULE in "${MODULES[@]}"; do
    echo "2. Generating ${MODULE}_gen.rs..."

    if [ ! -f "$SPEC_DIR/${MODULE}.rs" ]; then
        echo "  WARNING: Spec file not found: $SPEC_DIR/${MODULE}.rs"
        echo "  Skipping $MODULE"
        continue
    fi

    if [ ! -f "$SPEC_DIR/${MODULE}.automan" ]; then
        echo "  WARNING: Annotation file not found: $SPEC_DIR/${MODULE}.automan"
        echo "  Skipping $MODULE"
        continue
    fi

    if [ ! -f "$SPEC_DIR/${MODULE}_transpile.toml" ]; then
        echo "  WARNING: Config not found: $SPEC_DIR/${MODULE}_transpile.toml"
        echo "  Skipping $MODULE"
        continue
    fi

    $TRANSPILER \
        --input "$SPEC_DIR/${MODULE}.rs" \
        --annotations "$SPEC_DIR/${MODULE}.automan" \
        --config "$SPEC_DIR/${MODULE}_transpile.toml" \
        --output "$OUT_DIR/${MODULE}_gen.rs" || {
        echo "  ERROR: Module generation failed for $MODULE"
    }

    echo "  ✓ ${MODULE}_gen.rs complete"
    echo ""
done

# Step 3: Generate marshalable_gen.rs
echo "3. Generating marshalable_gen.rs..."
$TRANSPILER generate-marshalable \
    --config "$SPEC_DIR/types_transpile.toml" \
    --output "$OUT_DIR/marshalable_gen.rs" || {
    echo "ERROR: Marshalable generation failed"
    exit 1
}
echo "  ✓ marshalable_gen.rs complete"
echo ""

# Step 4: Generate mod.rs
echo "4. Generating mod.rs..."
cat > "$OUT_DIR/mod.rs" <<'MOD_EOF'
// Auto-generated RSL types and functions module
// DO NOT EDIT MANUALLY

pub mod acceptor_gen;
pub mod broadcast_gen;
pub mod election_gen;
pub mod executor_gen;
pub mod learner_gen;
pub mod marshalable_gen;
pub mod proposer_gen;
pub mod replica_gen;
pub mod types_gen;
MOD_EOF
echo "  ✓ mod.rs complete"
echo ""

echo "=============================================="
echo "Phase 14.4 Complete!"
echo "Fresh RSL output in: $OUT_DIR"
echo ""
echo "Generated files:"
ls -1 "$OUT_DIR"
