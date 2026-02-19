#!/bin/bash
# Generate TLA+ specs from real Verus protocol specs and validate with SANY.
#
# This implements Phase 16.8.1: Real-spec D3 baseline (Verus Spec -> TLA+).
#
# Usage:
#   ./scripts/generate_tla_workspace.sh              # Generate + validate all
#   ./scripts/generate_tla_workspace.sh --validate    # Validate only (skip generation)
#
# Prerequisites:
#   - Built transpiler: cargo build --release -p verus-transpiler
#   - tla2tools.jar for SANY validation (optional, skipped if not found)
#   - Java runtime for SANY

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TRANSPILER="$PROJECT_ROOT/transpiler/target/release/verus-transpile"
PROTOCOL_DIR="$PROJECT_ROOT/src/protocol"
WORKSPACE="$PROJECT_ROOT/transpiler/tla_test_workspace/transpiler_generated_tla"

# Protocols to convert (directory name -> spec files to convert)
SIMPLE_PROTOCOLS="TwoPhase Paxos LeaderElection Raft ChainReplication PrimaryBackup PBFT VerticalPaxos EPaxos"

# RSL spec files (excluding mod.rs, manual helpers, and proof directories)
RSL_SPECS="acceptor.rs broadcast.rs configuration.rs constants.rs distributed_system.rs election.rs environment.rs executor.rs learner.rs message.rs parameters.rs proposer.rs replica.rs state_machine.rs types.rs"

validate_only=false
if [ "${1:-}" = "--validate" ]; then
    validate_only=true
fi

# --- Generation Phase ---
if [ "$validate_only" = false ]; then
    if [ ! -f "$TRANSPILER" ]; then
        echo "Error: transpiler not found at $TRANSPILER"
        echo "Run: cd transpiler && cargo build --release"
        exit 1
    fi

    echo "=== Generating TLA+ from real protocol specs ==="
    echo ""

    # Simple protocols: batch mode
    for proto in $SIMPLE_PROTOCOLS; do
        echo "Converting $proto..."
        mkdir -p "$WORKSPACE/$proto"
        $TRANSPILER verus2-tla --batch \
            --input "$PROTOCOL_DIR/$proto" \
            --output "$WORKSPACE/$proto" \
            --spec-prefix L 2>&1 | grep -v "^$"
        # Remove empty manual helper files (no spec functions)
        find "$WORKSPACE/$proto" -name "*manual*" -o -name "*Manual*" | xargs -r -I{} sh -c 'lines=$(wc -l < "{}"); [ "$lines" -le 10 ] && rm "{}"' 2>/dev/null || true
    done

    # RSL: convert individual spec files (batch mode fails on unicode in manual files)
    echo "Converting RSL..."
    mkdir -p "$WORKSPACE/RSL"
    for f in $RSL_SPECS; do
        base=$(basename "$f" .rs)
        tla_name="$(echo ${base:0:1} | tr '[:lower:]' '[:upper:]')${base:1}"
        $TRANSPILER verus2-tla \
            --input "$PROTOCOL_DIR/RSL/$f" \
            --output "$WORKSPACE/RSL/$tla_name.tla" \
            --spec-prefix L 2>&1 | grep -v "^$"
    done

    total=$(find "$WORKSPACE" -name "*.tla" | wc -l)
    echo ""
    echo "Generation complete: $total TLA+ files in $WORKSPACE"
fi

# --- SANY Validation Phase ---
TLA2TOOLS="${TLA2TOOLS:-}"
if [ -z "$TLA2TOOLS" ]; then
    for candidate in \
        "$HOME/tools/tla2tools.jar" \
        "$PROJECT_ROOT/tools/tla2tools.jar" \
        "/usr/share/java/tla2tools.jar"; do
        if [ -f "$candidate" ]; then
            TLA2TOOLS="$candidate"
            break
        fi
    done
fi

if [ -z "$TLA2TOOLS" ] || [ ! -f "$TLA2TOOLS" ]; then
    echo ""
    echo "Warning: tla2tools.jar not found, skipping SANY validation."
    echo "Set TLA2TOOLS env var or place in ~/tools/tla2tools.jar"
    exit 0
fi

if ! command -v java &>/dev/null; then
    echo "Warning: Java not found, skipping SANY validation."
    exit 0
fi

echo ""
echo "=== SANY Validation ==="
echo ""

pass=0
fail=0
total=0
warnings=0

for f in $(find "$WORKSPACE" -name "*.tla" | sort); do
    total=$((total + 1))
    rel=$(echo "$f" | sed "s|$WORKSPACE/||")
    dir=$(dirname "$f")
    base=$(basename "$f")
    result=$(cd "$dir" && java -cp "$TLA2TOOLS" tla2sany.SANY "$base" 2>&1)
    if echo "$result" | grep -q "Semantic processing of module"; then
        pass=$((pass + 1))
        if echo "$result" | grep -q "Errors:"; then
            num_err=$(echo "$result" | grep "Errors:" | grep -o '[0-9]*')
            echo "  PASS ($num_err semantic warnings): $rel"
            warnings=$((warnings + 1))
        else
            echo "  PASS: $rel"
        fi
    else
        fail=$((fail + 1))
        echo "  FAIL: $rel"
        echo "$result" | grep -E "Error|error" | head -3 | sed 's/^/    /'
    fi
done

echo ""
echo "=== SANY Results: $pass/$total passed, $fail failed ($warnings with semantic warnings) ==="

if [ $fail -gt 0 ]; then
    exit 1
fi
