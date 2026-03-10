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
SF_CUTOFF_DIR="${SF_CUTOFF_DIR:-$PROJECT_ROOT/reports/benchmarks/source_first_cutoff_120s}"
TLC_CUTOFF_DIR="${TLC_CUTOFF_DIR:-$PROJECT_ROOT/reports/benchmarks/tlc_cutoff_120s}"
CUTOFF_SECONDS="${CUTOFF_SECONDS:-120}"

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

sf_cutoff_summary="$SF_CUTOFF_DIR/SUMMARY.md"
tlc_cutoff_summary="$TLC_CUTOFF_DIR/SUMMARY.md"
has_sf_cutoff=false
has_tlc_cutoff=false
[[ -f "$sf_cutoff_summary" ]] && has_sf_cutoff=true
[[ -f "$tlc_cutoff_summary" ]] && has_tlc_cutoff=true

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

protocol_display() {
    case "$1" in
        twophase) echo "TwoPhase" ;;
        primarybackup) echo "PrimaryBackup" ;;
        leaderelection) echo "LeaderElection" ;;
        paxos) echo "Paxos" ;;
        *) echo "$1" ;;
    esac
}

parse_source_first_artifact_details() {
    local artifact="$1"
    if [[ ! -f "$artifact" ]]; then
        echo "n/a|n/a|n/a|n/a"
        return
    fi
    python3 - "$artifact" <<'PY' 2>/dev/null || echo "n/a|n/a|n/a|n/a"
import json, sys
artifact = sys.argv[1]
try:
    data = json.load(open(artifact))
except Exception:
    print("n/a|n/a|n/a|n/a")
    raise SystemExit(0)
summary = data.get("summary") or {}
stop_reason = data.get("stop_reason", "n/a")
transitions = summary.get("transitions", "n/a")
elapsed_ms = summary.get("elapsed_ms", "n/a")
enum_evals = summary.get("enumeration_candidate_evaluations", "n/a")
print(f"{transitions}|{elapsed_ms}|{enum_evals}|{stop_reason}")
PY
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
    echo ""
    echo "## Same-Model Provenance"
    echo ""
    echo "- Generated base TLA+ (from \`verus-transpile verus2-tla --batch\`):"
    echo "  - \`transpiler/tla_test_workspace/transpiler_generated_tla/TwoPhase/Twophase.tla\`"
    echo "  - \`transpiler/tla_test_workspace/transpiler_generated_tla/PrimaryBackup/Primarybackup.tla\`"
    echo "  - \`transpiler/tla_test_workspace/transpiler_generated_tla/LeaderElection/Election.tla\`"
    echo "  - \`transpiler/tla_test_workspace/transpiler_generated_tla/Paxos/Paxos.tla\`"
    echo "- TLC wrapper/property glue used for model checking:"
    echo "  - \`transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/TwoPhase_Benchmark_MC.tla\` + \`.cfg\`"
    echo "  - \`transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/PrimaryBackup_Benchmark_MC.tla\` + \`.cfg\`"
    echo "  - \`transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/LeaderElection_Benchmark_MC.tla\` + \`.cfg\`"
    echo "  - \`transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/Paxos_Benchmark_MC.tla\` + \`.cfg\`"
    echo "- The benchmark comparison uses generated base modules plus checked-in wrapper/property glue; it does not compare against scratch-written standalone TLA+ specs."

    if $has_sf_cutoff || $has_tlc_cutoff; then
        echo ""
        echo "## Matched-Cutoff Progress (Shared ${CUTOFF_SECONDS}s Budget)"
        echo ""
        echo "This section is generated from dedicated time-bounded raw artifacts (not inferred from full-run totals)."
        echo ""
        echo "- Source-first cutoff artifacts: \`${SF_CUTOFF_DIR#$PROJECT_ROOT/}\`"
        echo "- TLC cutoff artifacts: \`${TLC_CUTOFF_DIR#$PROJECT_ROOT/}\`"
        echo ""
        echo "| Protocol | Engine | Result | States (gen) | Distinct | Depth | Wall (s) | Transitions | Elapsed (ms) | Notes |"
        echo "|----------|--------|--------|--------------|----------|-------|----------|-------------|--------------|-------|"

        for proto in $PROTOCOLS; do
            proto_display="$(protocol_display "$proto")"
            IFS='|' read -r sf_result sf_states sf_distinct sf_depth sf_wall <<< "$(parse_row "$sf_cutoff_summary" "$proto")"
            IFS='|' read -r tlc_result tlc_states tlc_distinct tlc_depth tlc_wall <<< "$(parse_row "$tlc_cutoff_summary" "$proto")"
            IFS='|' read -r sf_transitions sf_elapsed_ms sf_enum_evals sf_stop_reason <<< "$(parse_source_first_artifact_details "$SF_CUTOFF_DIR/${proto}_benchmark.json")"

            sf_notes="bounded progress"
            if [[ "$sf_result" == n/a ]]; then
                sf_notes="no checked-in cutoff artifact"
            elif [[ "$sf_result" == timeout_reached* ]]; then
                sf_notes="time-bounded blocked progress; stop_reason=${sf_stop_reason}; enum_eval=${sf_enum_evals}"
            elif [[ "$sf_result" == *error* ]]; then
                sf_notes="time-bounded blocked progress; error artifact"
            fi

            tlc_notes="bounded progress"
            if [[ "$tlc_result" == n/a ]]; then
                tlc_notes="no checked-in cutoff artifact"
            elif [[ "$tlc_result" == timeout* ]]; then
                tlc_notes="time-bounded progress at cutoff"
            elif [[ "$tlc_result" == pass ]]; then
                tlc_notes="exhausted before cutoff"
            fi

            echo "| $proto_display | source-first | $sf_result | — | $sf_distinct | $sf_depth | $sf_wall | $sf_transitions | $sf_elapsed_ms | $sf_notes |"
            echo "| | TLC | $tlc_result | $tlc_states | $tlc_distinct | $tlc_depth | $tlc_wall | n/a | n/a | $tlc_notes |"
        done
    fi
} > "$OUTPUT"

echo "Comparison report written to: ${OUTPUT#$PROJECT_ROOT/}"
