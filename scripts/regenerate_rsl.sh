#!/bin/bash
# Regenerate RSL implementation from specs
# This script regenerates all RSL generated code from the spec files.
#
# NOTE: types_gen.rs is manually maintained (contains re-exports + hand-written
# CScheduler, CClockReading, abstractify functions). It is NOT regenerated here.
#
# NOTE: Generated function files (*_gen.rs) have extensive hand-modifications
# from V3.6-V3.7 (clone fixes, iterator rewrites, assume() additions).
# Regenerating them will lose those fixes. Only regenerate individual files
# when you intend to re-apply those fixes afterward.

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

# types_gen.rs is manually maintained — skip regeneration
echo ""
echo "Skipping types_gen.rs (manually maintained with re-exports + hand-written types)"

# Regenerate all RSL module functions
# WARNING: This will overwrite hand-modifications from V3.6-V3.7!
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
