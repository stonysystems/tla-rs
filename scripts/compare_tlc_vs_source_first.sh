#!/usr/bin/env bash
# Compare TLC and source-first benchmark results side-by-side.
#
# Reads summary files produced by run_model_check_benchmarks.sh and
# run_tlc_benchmarks.sh, then generates a comparison report.
#
# Usage:
#   ./scripts/compare_tlc_vs_source_first.sh
#   SF_DIR=reports/benchmarks/source_first TLC_DIR=reports/benchmarks/tlc ./scripts/compare_tlc_vs_source_first.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
SF_DIR="${SF_DIR:-$PROJECT_ROOT/reports/benchmarks/source_first}"
TLC_DIR="${TLC_DIR:-$PROJECT_ROOT/reports/benchmarks/tlc}"
OUTPUT="${OUTPUT:-$PROJECT_ROOT/reports/benchmarks/TLC_VS_SOURCE_FIRST_BENCHMARK_COMPARISON.md}"
PROTOCOLS="${PROTOCOLS:-twophase primarybackup leaderelection paxos}"

mkdir -p "$(dirname "$OUTPUT")"

# Check that at least one summary exists
sf_summary="$SF_DIR/SUMMARY.md"
tlc_summary="$TLC_DIR/SUMMARY.md"

has_sf=false
has_tlc=false
[[ -f "$sf_summary" ]] && has_sf=true
[[ -f "$tlc_summary" ]] && has_tlc=true

if ! $has_sf && ! $has_tlc; then
    echo "Error: No benchmark results found." >&2
    echo "Run scripts/run_model_check_benchmarks.sh and/or scripts/run_tlc_benchmarks.sh first." >&2
    exit 1
fi

# Parse a SUMMARY.md table row for a protocol.
# Args: $1=summary_file $2=protocol_name
# Outputs: result|states|distinct|depth|wall_secs
parse_row() {
    local file="$1" proto="$2"
    if [[ ! -f "$file" ]]; then
        echo "n/a|n/a|n/a|n/a|n/a"
        return
    fi
    local row
    row=$(grep "^| *$proto " "$file" 2>/dev/null | head -1 || echo "")
    if [[ -z "$row" ]]; then
        echo "n/a|n/a|n/a|n/a|n/a"
        return
    fi
    # Parse: | proto | result | states | distinct | depth | wall_secs |
    echo "$row" | awk -F'|' '{
        gsub(/^ +| +$/, "", $3);
        gsub(/^ +| +$/, "", $4);
        gsub(/^ +| +$/, "", $5);
        gsub(/^ +| +$/, "", $6);
        gsub(/^ +| +$/, "", $7);
        print $3 "|" $4 "|" $5 "|" $6 "|" $7
    }'
}

{
    echo "# TLC vs Source-first Benchmark Comparison"
    echo ""
    echo "Generated: $(date -u '+%Y-%m-%d %H:%M:%S UTC')"
    echo "Git rev: $(git -C "$PROJECT_ROOT" rev-parse --short HEAD)"
    echo ""

    if $has_sf; then
        sf_date=$(grep "^Generated:" "$sf_summary" 2>/dev/null | head -1 || echo "unknown")
        echo "Source-first run: $sf_date"
    fi
    if $has_tlc; then
        tlc_date=$(grep "^Generated:" "$tlc_summary" 2>/dev/null | head -1 || echo "unknown")
        echo "TLC run: $tlc_date"
    fi
    echo ""

    echo "## Column Meanings"
    echo ""
    echo "- \`States (gen)\`: total states generated before deduplication. For TLC this includes revisits."
    echo "- \`Distinct\`: unique states after the engine's deduplication/fingerprinting step."
    echo "- \`Depth\`: maximum search depth reached in the run."
    echo "- \`Wall (s)\`: wall-clock elapsed time in seconds."
    echo "- For source-first, \`States (gen)\` is currently reported as \`—\` because the checked-in benchmark summaries expose deduplicated explored states, not a separate generated-state counter."
    echo ""
    echo "## Side-by-side Results"
    echo ""
    echo "| Protocol | Engine | Result | States (gen) | Distinct | Depth | Wall (s) |"
    echo "|----------|--------|--------|--------------|----------|-------|----------|"

    for proto in $PROTOCOLS; do
        IFS='|' read -r sf_result sf_states sf_distinct sf_depth sf_wall <<< "$(parse_row "$sf_summary" "$proto")"
        IFS='|' read -r tlc_result tlc_states tlc_distinct tlc_depth tlc_wall <<< "$(parse_row "$tlc_summary" "$proto")"

        echo "| $proto | source-first | $sf_result | — | $sf_distinct | $sf_depth | $sf_wall |"
        echo "| | TLC | $tlc_result | $tlc_states | $tlc_distinct | $tlc_depth | $tlc_wall |"
    done

    echo ""
    echo "## Notes"
    echo ""
    echo "- **State-count semantics differ**: Source-first counts states on the"
    echo "  centralized Verus \`LState\` directly. TLC counts states on the TLA+"
    echo "  wrapper which may include additional message-channel variables."
    echo "- **Paxos and LeaderElection** source-first runs are BLOCKED on"
    echo "  candidate enumeration scalability (see benchmark configs for details)."
    echo "- Configs: \`transpiler/tests/model_check_fixtures/benchmarks_1h/\`"
    echo "- TLC wrappers: \`transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/\`"
} > "$OUTPUT"

echo "Comparison report written to: ${OUTPUT#$PROJECT_ROOT/}"
