#!/bin/bash
# Regenerate ALL protocol implementations from specs
#
# This script regenerates both types and functions for all protocols:
#   - TwoPhase, Paxos, LeaderElection, Raft, ChainReplication, PrimaryBackup, PBFT, VerticalPaxos, EPaxos (simple protocols)
#   - RSL (multi-module protocol with per-module configs)
#
# Usage:
#   ./scripts/regenerate_all.sh          # Regenerate everything
#   ./scripts/regenerate_all.sh RSL      # Regenerate RSL only
#   ./scripts/regenerate_all.sh TwoPhase # Regenerate TwoPhase only

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TRANSPILER_DIR="$PROJECT_ROOT/transpiler"

# Build the transpiler
echo "Building transpiler..."
cd "$TRANSPILER_DIR"
cargo build --release
TRANSPILER="$TRANSPILER_DIR/target/release/verus-transpile"
echo "  Done."

# Helper: regenerate a simple (single-module) protocol
regenerate_simple() {
    local name="$1"      # e.g., TwoPhase
    local module="$2"    # e.g., twophase
    local spec_dir="$PROJECT_ROOT/src/protocol/$name"
    local out_dir="$PROJECT_ROOT/src/generated/$name"

    echo ""
    echo "=== Regenerating $name ==="

    # Types
    echo "  Generating types_gen.rs..."
    $TRANSPILER generate-types \
        -i "$spec_dir/types.rs" \
        -c "$spec_dir/${module}_transpile.toml" \
        -o "$out_dir/types_gen.rs"

    # Functions
    echo "  Generating ${module}_gen.rs..."
    $TRANSPILER \
        --input "$spec_dir/${module}.rs" \
        --annotations "$spec_dir/${module}.automan" \
        --config "$spec_dir/${module}_transpile.toml" \
        --output "$out_dir/${module}_gen.rs"

    echo "  Done."
}

# Helper: regenerate RSL (multi-module protocol)
regenerate_rsl() {
    echo ""
    echo "=== Regenerating RSL ==="

    local spec_dir="$PROJECT_ROOT/src/protocol/RSL"
    local out_dir="$PROJECT_ROOT/src/generated/RSL"

    # Types (multi-input, separate config)
    echo "  Generating types_gen.rs..."
    $TRANSPILER generate-types \
        -i "$spec_dir/types.rs" \
        -i "$spec_dir/parameters.rs" \
        -i "$spec_dir/configuration.rs" \
        -i "$spec_dir/constants.rs" \
        -i "$spec_dir/acceptor.rs" \
        -i "$spec_dir/learner.rs" \
        -i "$spec_dir/election.rs" \
        -i "$spec_dir/executor.rs" \
        -i "$spec_dir/proposer.rs" \
        -i "$spec_dir/replica.rs" \
        -c "$spec_dir/types_transpile.toml" \
        -o "$out_dir/types_gen.rs"
    echo "    NOTE: Helper functions must be appended manually."

    # Per-module functions (each has its own *_transpile.toml)
    for module in acceptor learner executor proposer replica broadcast election; do
        echo "  Generating ${module}_gen.rs..."
        $TRANSPILER \
            --input "$spec_dir/${module}.rs" \
            --annotations "$spec_dir/${module}.automan" \
            --config "$spec_dir/${module}_transpile.toml" \
            --output "$out_dir/${module}_gen.rs"
    done

    echo "  Done."
}

# Main: regenerate requested protocol(s)
TARGET="${1:-all}"

case "$TARGET" in
    TwoPhase)
        regenerate_simple TwoPhase twophase
        ;;
    Paxos)
        regenerate_simple Paxos paxos
        ;;
    LeaderElection)
        regenerate_simple LeaderElection election
        ;;
    Raft)
        regenerate_simple Raft raft
        ;;
    ChainReplication)
        regenerate_simple ChainReplication chain
        ;;
    PrimaryBackup)
        regenerate_simple PrimaryBackup primarybackup
        ;;
    PBFT)
        regenerate_simple PBFT pbft
        ;;
    VerticalPaxos)
        regenerate_simple VerticalPaxos vpaxos
        ;;
    EPaxos)
        regenerate_simple EPaxos epaxos
        ;;
    RSL)
        regenerate_rsl
        ;;
    all)
        regenerate_simple TwoPhase twophase
        regenerate_simple Paxos paxos
        regenerate_simple LeaderElection election
        regenerate_simple Raft raft
        regenerate_simple ChainReplication chain
        regenerate_simple PrimaryBackup primarybackup
        regenerate_simple PBFT pbft
        regenerate_simple VerticalPaxos vpaxos
        regenerate_simple EPaxos epaxos
        regenerate_rsl
        ;;
    *)
        echo "Unknown protocol: $TARGET"
        echo "Usage: $0 [TwoPhase|Paxos|LeaderElection|Raft|ChainReplication|PrimaryBackup|PBFT|VerticalPaxos|EPaxos|RSL|all]"
        exit 1
        ;;
esac

echo ""
echo "=== Regeneration complete ==="
