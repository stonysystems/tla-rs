#!/bin/bash
# Regenerate RSL implementation from specs
# This script regenerates all RSL generated code from the spec files.

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TRANSPILER_DIR="$PROJECT_ROOT/transpiler"

echo "=== RSL Code Regeneration ==="
echo "Project root: $PROJECT_ROOT"

# Build the transpiler if needed
echo ""
echo "Building transpiler..."
cd "$TRANSPILER_DIR"
cargo build --release

TRANSPILER="$TRANSPILER_DIR/target/release/verus-transpile"

# Regenerate types
echo ""
echo "Regenerating RSL types..."
$TRANSPILER generate-types \
    --input "$PROJECT_ROOT/src/protocol/RSL/types.rs" \
    --config "$PROJECT_ROOT/src/protocol/RSL/types_transpile.toml" \
    --output "$PROJECT_ROOT/src/generated/RSL/types_gen.rs"

# Regenerate all RSL module functions
for module in acceptor learner executor proposer replica broadcast election; do
    echo ""
    echo "Regenerating $module functions..."
    $TRANSPILER \
        --input "$PROJECT_ROOT/src/protocol/RSL/${module}.rs" \
        --annotations "$PROJECT_ROOT/src/protocol/RSL/${module}.automan" \
        --config "$PROJECT_ROOT/src/protocol/RSL/transpile.toml" \
        --output "$PROJECT_ROOT/src/generated/RSL/${module}_gen.rs"
done

# Format generated code for consistency
echo ""
echo "Formatting generated code..."
cd "$PROJECT_ROOT"
cargo fmt -- src/generated/RSL/*.rs

echo ""
echo "=== Regeneration complete ==="
echo ""
echo "Generated files:"
ls -la "$PROJECT_ROOT/src/generated/RSL/"
