#!/bin/bash
# Phase 14.3: Regenerate Simple (Single-Module) Protocols
# This script regenerates all simple protocols into src/generated_fresh/

set -e  # Exit on error

TRANSPILER="transpiler/target/release/verus-transpile"

if [ ! -f "$TRANSPILER" ]; then
    echo "Error: Transpiler not found at $TRANSPILER"
    echo "Please run: cd transpiler && cargo build --release"
    exit 1
fi

# Array of simple protocols: (PROTOCOL_DIR MODULE_NAME)
declare -a PROTOCOLS=(
    "TwoPhase:twophase"
    "Paxos:paxos"
    "LeaderElection:election"
    "Raft:raft"
    "ChainReplication:chain"
    "PrimaryBackup:primarybackup"
    "PBFT:pbft"
    "VerticalPaxos:vpaxos"
    "EPaxos:epaxos"
)

echo "Starting Phase 14.3: Regenerating Simple Protocols"
echo "=================================================="
echo ""

for entry in "${PROTOCOLS[@]}"; do
    IFS=':' read -r PROTOCOL MODULE <<< "$entry"

    SPEC_DIR="src/protocol/$PROTOCOL"
    OUT_DIR="src/generated_fresh/$PROTOCOL"

    echo "Processing $PROTOCOL (module: $MODULE)..."

    # Ensure output directory exists
    mkdir -p "$OUT_DIR"

    # Check if spec file exists
    if [ ! -f "$SPEC_DIR/${MODULE}.rs" ]; then
        echo "  WARNING: Spec file not found: $SPEC_DIR/${MODULE}.rs"
        echo "  Skipping $PROTOCOL"
        echo ""
        continue
    fi

    # Check if config exists
    if [ ! -f "$SPEC_DIR/${MODULE}_transpile.toml" ]; then
        echo "  WARNING: Config not found: $SPEC_DIR/${MODULE}_transpile.toml"
        echo "  Skipping $PROTOCOL"
        echo ""
        continue
    fi

    # The sidecar is optional since Phase 55 — the spec carries inline
    # `// @automan` directives, so a missing .automan is not a skip.

    # Generate types (if types.rs exists)
    if [ -f "$SPEC_DIR/types.rs" ]; then
        echo "  Generating types_gen.rs..."
        $TRANSPILER generate-types \
            --input "$SPEC_DIR/types.rs" \
            --config "$SPEC_DIR/${MODULE}_transpile.toml" \
            --output "$OUT_DIR/types_gen.rs" || {
            echo "  ERROR: Type generation failed for $PROTOCOL"
        }
    else
        echo "  No types.rs found, skipping type generation"
    fi

    # Generate module implementation
    echo "  Generating ${MODULE}_gen.rs..."
    annot_args=()
    [ -f "$SPEC_DIR/${MODULE}.automan" ] && annot_args=(--annotations "$SPEC_DIR/${MODULE}.automan")
    $TRANSPILER \
        --input "$SPEC_DIR/${MODULE}.rs" \
        "${annot_args[@]}" \
        --config "$SPEC_DIR/${MODULE}_transpile.toml" \
        --output "$OUT_DIR/${MODULE}_gen.rs" || {
        echo "  ERROR: Module generation failed for $PROTOCOL"
    }

    # Generate message.rs (protocol message serialization)
    echo "  Generating message.rs..."
    $TRANSPILER generate-messages \
        --config "$SPEC_DIR/${MODULE}_transpile.toml" \
        --output "src/implementation/$PROTOCOL/message.rs" || {
        echo "  ERROR: Message generation failed for $PROTOCOL"
    }

    # Generate mod.rs
    echo "  Generating mod.rs..."
    cat > "$OUT_DIR/mod.rs" <<MOD_EOF
// Auto-generated module for $PROTOCOL
// DO NOT EDIT MANUALLY

pub mod types_gen;
pub mod ${MODULE}_gen;
MOD_EOF

    echo "  ✓ Completed $PROTOCOL"
    echo ""
done

echo "=================================================="
echo "Phase 14.3 Complete!"
echo "Fresh output in: src/generated_fresh/"
