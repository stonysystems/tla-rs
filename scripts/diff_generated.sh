#!/bin/bash
# Phase 14.5: Compare and Diff Generated Code
# This script diffs src/generated/ against src/generated_fresh/ and creates a report

set -e  # Exit on error

DIFF_DIR="diffs"
REPORT="Phase14_Regeneration_Audit_Report.md"

# Create diffs directory
mkdir -p "$DIFF_DIR"

echo "Starting Phase 14.5: Diff Analysis"
echo "===================================="
echo ""

# Get transpiler info
TRANSPILER_COMMIT=$(git rev-parse HEAD)
TRANSPILER_SHORT=$(git log --oneline -1)
VERUS_VERSION=$(grep -o "v[0-9.]*" <<< "$(verus --version 2>/dev/null || echo 'not available')" | head -1 || echo "not available")
RUST_VERSION=$(rustc --version | cut -d' ' -f2)

echo "Transpiler commit: $TRANSPILER_COMMIT"
echo "Verus version: $VERUS_VERSION"
echo "Rust version: $RUST_VERSION"
echo ""

# Initialize report
cat > "$REPORT" <<EOF
# Phase 14: Regeneration Audit Report

**Date**: $(date +%Y-%m-%d)
**Transpiler Commit**: $TRANSPILER_SHORT
**Verus Version**: $VERUS_VERSION
**Rust Toolchain**: $RUST_VERSION

## Executive Summary

This report compares freshly regenerated code (from \`scripts/regenerate_simple_protocols.sh\` and \`scripts/regenerate_rsl.sh\`) against the current \`src/generated/\` directory. Any differences indicate either:
1. Manual edits to generated files (policy violation)
2. Transpiler improvements since last regeneration
3. Configuration changes since last regeneration

---

## Protocol Comparison Summary

| Protocol | Files Compared | Identical | Differences | Notes |
|----------|----------------|-----------|-------------|-------|
EOF

# Array of all protocols
declare -a ALL_PROTOCOLS=(
    "TwoPhase"
    "Paxos"
    "LeaderElection"
    "Raft"
    "ChainReplication"
    "PrimaryBackup"
    "PBFT"
    "VerticalPaxos"
    "EPaxos"
    "RSL"
)

# Track totals
TOTAL_FILES=0
IDENTICAL_FILES=0
DIFFERENT_FILES=0

# Function to count diff lines
count_diff_lines() {
    local file1=$1
    local file2=$2
    if diff -u "$file1" "$file2" > /dev/null 2>&1; then
        echo "0"
    else
        diff -u "$file1" "$file2" 2>/dev/null | grep -E '^\+|^\-' | grep -v '^\+\+\+|^\-\-\-' | wc -l
    fi
}

# Compare each protocol
for PROTOCOL in "${ALL_PROTOCOLS[@]}"; do
    OLD_DIR="src/generated/$PROTOCOL"
    NEW_DIR="src/generated_fresh/$PROTOCOL"

    if [ ! -d "$OLD_DIR" ]; then
        echo "| $PROTOCOL | N/A | N/A | N/A | Not in src/generated/ |" >> "$REPORT"
        continue
    fi

    if [ ! -d "$NEW_DIR" ]; then
        echo "| $PROTOCOL | N/A | N/A | N/A | Not regenerated |" >> "$REPORT"
        continue
    fi

    # Count files
    OLD_FILES=$(ls -1 "$OLD_DIR"/*.rs 2>/dev/null | wc -l)
    NEW_FILES=$(ls -1 "$NEW_DIR"/*.rs 2>/dev/null | wc -l)

    if [ "$OLD_FILES" -ne "$NEW_FILES" ]; then
        echo "| $PROTOCOL | $OLD_FILES vs $NEW_FILES | - | - | File count mismatch |" >> "$REPORT"
        continue
    fi

    # Compare each file
    PROTOCOL_IDENTICAL=0
    PROTOCOL_DIFFERENT=0

    for OLD_FILE in "$OLD_DIR"/*.rs; do
        BASENAME=$(basename "$OLD_FILE")
        NEW_FILE="$NEW_DIR/$BASENAME"

        if [ ! -f "$NEW_FILE" ]; then
            PROTOCOL_DIFFERENT=$((PROTOCOL_DIFFERENT + 1))
            continue
        fi

        TOTAL_FILES=$((TOTAL_FILES + 1))

        # Create diff
        DIFF_FILE="$DIFF_DIR/${PROTOCOL}_${BASENAME}.diff"
        if diff -u "$OLD_FILE" "$NEW_FILE" > "$DIFF_FILE" 2>&1; then
            PROTOCOL_IDENTICAL=$((PROTOCOL_IDENTICAL + 1))
            IDENTICAL_FILES=$((IDENTICAL_FILES + 1))
            rm "$DIFF_FILE"  # Remove empty diff
        else
            PROTOCOL_DIFFERENT=$((PROTOCOL_DIFFERENT + 1))
            DIFFERENT_FILES=$((DIFFERENT_FILES + 1))
            echo "  Created diff: $DIFF_FILE"
        fi
    done

    echo "| $PROTOCOL | $OLD_FILES | $PROTOCOL_IDENTICAL | $PROTOCOL_DIFFERENT | $([ $PROTOCOL_DIFFERENT -eq 0 ] && echo "✅ Identical" || echo "⚠️ Has changes") |" >> "$REPORT"
done

# Add totals
cat >> "$REPORT" <<EOF
| **TOTAL** | **$TOTAL_FILES** | **$IDENTICAL_FILES** | **$DIFFERENT_FILES** | |

---

## Detailed Diff Analysis

EOF

# Add detailed sections for protocols with differences
for PROTOCOL in "${ALL_PROTOCOLS[@]}"; do
    PROTOCOL_DIFFS=$(ls -1 "$DIFF_DIR/${PROTOCOL}_"*.diff 2>/dev/null | wc -l)

    if [ "$PROTOCOL_DIFFS" -gt 0 ]; then
        cat >> "$REPORT" <<EOF
### $PROTOCOL

**Files with differences**: $PROTOCOL_DIFFS

EOF

        for DIFF_FILE in "$DIFF_DIR/${PROTOCOL}_"*.diff; do
            BASENAME=$(basename "$DIFF_FILE" .diff)
            FILE_NAME=${BASENAME#${PROTOCOL}_}
            DIFF_LINES=$(count_diff_lines "src/generated/$PROTOCOL/$FILE_NAME" "src/generated_fresh/$PROTOCOL/$FILE_NAME")

            cat >> "$REPORT" <<EOF
#### \`$FILE_NAME\`

**Changed lines**: $DIFF_LINES

<details>
<summary>Click to expand diff</summary>

\`\`\`diff
$(cat "$DIFF_FILE")
\`\`\`

</details>

EOF
        done
    fi
done

# Add conclusion
cat >> "$REPORT" <<EOF

---

## Conclusions

**Reproducibility Status**: $([ $DIFFERENT_FILES -eq 0 ] && echo "✅ **FULLY REPRODUCIBLE**" || echo "⚠️ **PARTIAL** ($IDENTICAL_FILES/$TOTAL_FILES files identical)")

### Next Steps

EOF

if [ "$DIFFERENT_FILES" -gt 0 ]; then
    cat >> "$REPORT" <<EOF
1. Review diffs in \`$DIFF_DIR/\` to understand changes
2. For each difference, determine:
   - Is it a manual edit? (violates policy → remove manual edit, regenerate)
   - Is it a transpiler improvement? (update \`src/generated/\` with fresh output)
   - Is it a config change? (update configs or regenerate)
3. Re-run this audit after addressing changes

EOF
else
    cat >> "$REPORT" <<EOF
All files are identical! The transpiler is fully reproducible.

EOF
fi

cat >> "$REPORT" <<EOF
### Artifact Locations

- **Fresh output**: \`src/generated_fresh/\`
- **Diffs**: \`$DIFF_DIR/\`
- **This report**: \`$REPORT\`

*Note: Do NOT commit \`src/generated_fresh/\` or \`$DIFF_DIR/\`. Add to .gitignore.*

EOF

echo ""
echo "===================================="
echo "Phase 14.5 Complete!"
echo ""
echo "Results:"
echo "  Total files compared: $TOTAL_FILES"
echo "  Identical: $IDENTICAL_FILES"
echo "  Different: $DIFFERENT_FILES"
echo ""
echo "Report saved to: $REPORT"
echo "Diffs saved to: $DIFF_DIR/"
