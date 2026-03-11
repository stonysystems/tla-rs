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
SF_RELEASE_DIR="${SF_RELEASE_DIR:-$PROJECT_ROOT/reports/benchmarks/source_first_release}"
SF_DEBUG_DIR="${SF_DEBUG_DIR:-$PROJECT_ROOT/reports/benchmarks/source_first}"
SF_DIR="${SF_DIR:-$SF_RELEASE_DIR}"
TLC_DIR="${TLC_DIR:-$PROJECT_ROOT/reports/benchmarks/tlc}"
OUTPUT="${OUTPUT:-$PROJECT_ROOT/reports/benchmarks/TLC_VS_SOURCE_FIRST_BENCHMARK_COMPARISON.md}"
PROTOCOLS="${PROTOCOLS:-twophase primarybackup leaderelection paxos}"
SF_CUTOFF_DIR="${SF_CUTOFF_DIR:-$PROJECT_ROOT/reports/benchmarks/source_first_cutoff_120s}"
TLC_CUTOFF_DIR="${TLC_CUTOFF_DIR:-$PROJECT_ROOT/reports/benchmarks/tlc_cutoff_120s}"
CUTOFF_SECONDS="${CUTOFF_SECONDS:-120}"

mkdir -p "$(dirname "$OUTPUT")"

if [[ ! -f "$SF_DIR/SUMMARY.md" && -f "$SF_DEBUG_DIR/SUMMARY.md" ]]; then
    SF_DIR="$SF_DEBUG_DIR"
fi

# Check that at least one summary exists
sf_summary="$SF_DIR/SUMMARY.md"
tlc_summary="$TLC_DIR/SUMMARY.md"
sf_release_summary="$SF_RELEASE_DIR/SUMMARY.md"
sf_debug_summary="$SF_DEBUG_DIR/SUMMARY.md"

has_sf=false
has_tlc=false
[[ -f "$sf_summary" ]] && has_sf=true
[[ -f "$tlc_summary" ]] && has_tlc=true
has_sf_release=false
has_sf_debug=false
[[ -f "$sf_release_summary" ]] && has_sf_release=true
[[ -f "$sf_debug_summary" ]] && has_sf_debug=true

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

parse_source_first_timing_breakdown() {
    local artifact="$1"
    if [[ ! -f "$artifact" ]]; then
        echo "n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a"
        return
    fi
    python3 - "$artifact" <<'PY' 2>/dev/null || echo "n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a"
import json
import sys

artifact = sys.argv[1]
try:
    data = json.load(open(artifact))
except Exception:
    print("n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a")
    raise SystemExit(0)
timing = ((data.get("summary") or {}).get("timing") or {})
fields = [
    "source_ingestion_parsing_ms",
    "model_config_resolution_ms",
    "initial_state_construction_ms",
    "successor_solving_ms",
    "candidate_generation_evaluation_ms",
    "dedup_hashing_normalization_ms",
    "invariant_evaluation_ms",
    "report_serialization_output_ms",
]
print("|".join(str(timing.get(field, "n/a")) for field in fields))
PY
}

parse_small_model_gap_diagnosis() {
    local release_artifact="$1"
    local debug_artifact="$2"
    if [[ ! -f "$release_artifact" ]]; then
        echo "n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a"
        return
    fi
    python3 - "$release_artifact" "$debug_artifact" <<'PY' 2>/dev/null || echo "n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a"
import json
import sys

release_artifact = sys.argv[1]
debug_artifact = sys.argv[2] if len(sys.argv) > 2 else ""


def load_json(path):
    try:
        with open(path, "r", encoding="utf-8") as handle:
            return json.load(handle)
    except Exception:
        return {}


def to_float(value):
    try:
        return float(value)
    except Exception:
        return None


def pct(value, total):
    if value is None or total is None or total <= 0:
        return "n/a"
    return f"{(100.0 * value / total):.2f}%"


release = load_json(release_artifact)
debug = load_json(debug_artifact) if debug_artifact else {}

release_summary = release.get("summary") or {}
release_timing = release_summary.get("timing") or {}
debug_summary = debug.get("summary") or {}

release_wall_ms = to_float(release_summary.get("elapsed_ms"))
debug_wall_ms = to_float(debug_summary.get("elapsed_ms"))
candidate_ms = to_float(release_timing.get("candidate_generation_evaluation_ms"))
source_ingest_ms = to_float(release_timing.get("source_ingestion_parsing_ms"))
model_resolve_ms = to_float(release_timing.get("model_config_resolution_ms"))
init_ms = to_float(release_timing.get("initial_state_construction_ms"))
report_ms = to_float(release_timing.get("report_serialization_output_ms"))
fixed_ms = sum(
    value
    for value in [source_ingest_ms, model_resolve_ms, init_ms, report_ms]
    if value is not None
)
dedup_ms = to_float(release_timing.get("dedup_hashing_normalization_ms"))
invariant_ms = to_float(release_timing.get("invariant_evaluation_ms"))
successor_ms = to_float(release_timing.get("successor_solving_ms"))

candidate_pct = pct(candidate_ms, release_wall_ms)
fixed_pct = pct(fixed_ms, release_wall_ms)
dedup_pct = pct(dedup_ms, release_wall_ms)
invariant_pct = pct(invariant_ms, release_wall_ms)

debug_release_ratio = "n/a"
if release_wall_ms is not None and release_wall_ms > 0 and debug_wall_ms is not None:
    debug_release_ratio = f"{debug_wall_ms / release_wall_ms:.2f}x"

phase_values = {
    "candidate_enumeration": candidate_ms,
    "fixed_startup_parsing": fixed_ms,
    "dedup_hash_normalize": dedup_ms,
    "invariant_eval": invariant_ms,
    "successor_solving": successor_ms,
}
phase_values = {name: value for name, value in phase_values.items() if value is not None}
dominant_phase = max(phase_values, key=phase_values.get) if phase_values else "n/a"

fixed_overhead_dominates = "n/a"
if release_wall_ms is not None and release_wall_ms > 0:
    fixed_overhead_dominates = "yes" if fixed_ms / release_wall_ms >= 0.50 else "no"

dedup_meaningful = "n/a"
if release_wall_ms is not None and release_wall_ms > 0 and dedup_ms is not None:
    dedup_meaningful = "yes" if dedup_ms / release_wall_ms >= 0.10 else "no"

release_material = "n/a"
if debug_release_ratio != "n/a":
    ratio = float(debug_release_ratio[:-1])
    release_material = "yes" if ratio >= 1.50 else "no"

fields = [
    release_summary.get("elapsed_ms", "n/a"),
    release_timing.get("candidate_generation_evaluation_ms", "n/a"),
    candidate_pct,
    int(fixed_ms) if release_wall_ms is not None else "n/a",
    fixed_pct,
    release_timing.get("dedup_hashing_normalization_ms", "n/a"),
    dedup_pct,
    release_timing.get("invariant_evaluation_ms", "n/a"),
    invariant_pct,
    debug_release_ratio,
    dominant_phase,
    fixed_overhead_dominates,
    dedup_meaningful,
    release_material,
]
print("|".join(str(field) for field in fields))
PY
}

parse_source_first_branch_blockers() {
    local artifact="$1"
    local max_rows="${2:-4}"
    if [[ ! -f "$artifact" ]]; then
        return
    fi
    python3 - "$artifact" "$max_rows" <<'PY' 2>/dev/null || true
import json
import sys

artifact = sys.argv[1]
max_rows = int(sys.argv[2])
try:
    data = json.load(open(artifact))
except Exception:
    raise SystemExit(0)

entries = ((data.get("summary") or {}).get("branch_telemetry") or [])
if not isinstance(entries, list):
    raise SystemExit(0)


def n(entry, key):
    value = entry.get(key)
    if isinstance(value, (int, float)):
        return value
    return 0


entries = sorted(
    entries,
    key=lambda entry: (
        n(entry, "cumulative_solve_elapsed_ms"),
        n(entry, "enumeration_fallback_hits"),
        n(entry, "guard_pruned_candidate_evaluations"),
        n(entry, "candidate_state_count"),
    ),
    reverse=True,
)

rows_printed = 0
for entry in entries:
    if rows_printed >= max_rows:
        break
    branch_label = entry.get("branch_label", "n/a")
    print(
        f"{branch_label}|"
        f"{entry.get('existential_assignment_count', 'n/a')}|"
        f"{entry.get('candidate_state_count', 'n/a')}|"
        f"{entry.get('direct_solver_hits', 'n/a')}|"
        f"{entry.get('enumeration_fallback_hits', 'n/a')}|"
        f"{entry.get('guard_pruned_candidate_evaluations', 'n/a')}|"
        f"{entry.get('successful_successors', 'n/a')}|"
        f"{entry.get('cumulative_solve_elapsed_ms', 'n/a')}"
    )
    rows_printed += 1
PY
}

parse_blocker_root_cause() {
    local artifact="$1"
    if [[ ! -f "$artifact" ]]; then
        echo "n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a"
        return
    fi
    python3 - "$artifact" <<'PY' 2>/dev/null || echo "n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a"
import json
import sys

artifact = sys.argv[1]
try:
    data = json.load(open(artifact))
except Exception:
    print("n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a")
    raise SystemExit(0)

summary = data.get("summary") or {}
branch_entries = summary.get("branch_telemetry") or []
if not isinstance(branch_entries, list):
    branch_entries = []


def n(value):
    if isinstance(value, (int, float)):
        return value
    return 0


def entry_n(entry, key):
    return n(entry.get(key))


top_branch = None
if branch_entries:
    top_branch = max(
        branch_entries,
        key=lambda entry: (
            entry_n(entry, "cumulative_solve_elapsed_ms"),
            entry_n(entry, "enumeration_fallback_hits"),
            entry_n(entry, "candidate_state_count"),
        ),
    )

max_existentials = max((entry_n(entry, "existential_assignment_count") for entry in branch_entries), default=0)
max_candidates = max((entry_n(entry, "candidate_state_count") for entry in branch_entries), default=0)

enum_evals = n(summary.get("enumeration_candidate_evaluations"))
enum_fallback_solves = n(summary.get("enumeration_fallback_branch_solves"))
top_branch_enum_hits = entry_n(top_branch or {}, "enumeration_fallback_hits")

blocked_cause = "n/a"
if data.get("stop_reason") == "TimeoutReached":
    if enum_evals > 0 or enum_fallback_solves > 0 or top_branch_enum_hits > 0:
        blocked_cause = "enumeration_fallback_pressure"
    else:
        blocked_cause = "direct_solver_domain_pressure"

fields = [
    data.get("stop_reason", "n/a"),
    summary.get("states", "n/a"),
    summary.get("transitions", "n/a"),
    summary.get("elapsed_ms", "n/a"),
    summary.get("enumeration_candidate_evaluations", "n/a"),
    summary.get("direct_assignment_branch_solves", "n/a"),
    summary.get("enumeration_fallback_branch_solves", "n/a"),
    max_existentials,
    max_candidates,
    (top_branch or {}).get("branch_label", "n/a"),
    entry_n(top_branch or {}, "cumulative_solve_elapsed_ms"),
    top_branch_enum_hits,
    entry_n(top_branch or {}, "direct_solver_hits"),
    blocked_cause,
]
print("|".join(str(field) for field in fields))
PY
}

parse_anti_corner_cutting_status() {
    local release_artifact="$1"
    local debug_artifact="$2"
    if [[ ! -f "$release_artifact" ]]; then
        echo "n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a"
        return
    fi
    python3 - "$release_artifact" "$debug_artifact" <<'PY' 2>/dev/null || echo "n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a|n/a"
import json
import sys

release_artifact = sys.argv[1]
debug_artifact = sys.argv[2] if len(sys.argv) > 2 else ""


def load(path):
    try:
        with open(path, "r", encoding="utf-8") as handle:
            return json.load(handle)
    except Exception:
        return {}


def extract_fields(payload):
    search = payload.get("search") or {}
    evidence = search.get("evidence_mode") or {}
    invariants = payload.get("invariants") or {}
    symmetry_fields = search.get("symmetry_fields")
    if not isinstance(symmetry_fields, list):
        symmetry_fields = []
    lossy_reasons = evidence.get("lossy_reasons")
    if not isinstance(lossy_reasons, list):
        lossy_reasons = []
    return {
        "evidence_class": evidence.get("class", "n/a"),
        "proof_strength": evidence.get("proof_strength", "n/a"),
        "state_dedup": search.get("state_dedup", "n/a"),
        "lossy_reasons": "none" if not lossy_reasons else ",".join(str(reason) for reason in lossy_reasons),
        "symmetry_count": len(symmetry_fields),
        "por_heuristic": search.get("por_heuristic", "n/a"),
        "max_depth": search.get("max_depth", "n/a"),
        "max_states": search.get("max_states", "n/a"),
        "timeout_ms": search.get("timeout_ms", "n/a"),
        "inv_configured": invariants.get("configured_count", "n/a"),
        "inv_resolved": invariants.get("resolved_count", "n/a"),
        "inv_configured_names": tuple(invariants.get("configured") or []),
        "inv_resolved_names": tuple(invariants.get("resolved") or []),
    }


release = extract_fields(load(release_artifact))
debug_payload = load(debug_artifact) if debug_artifact else {}
debug = extract_fields(debug_payload) if debug_payload else None

bounds_match = "n/a"
invariants_match = "n/a"
if debug is not None:
    bounds_match = "yes" if (
        release["max_depth"] == debug["max_depth"]
        and release["max_states"] == debug["max_states"]
        and release["timeout_ms"] == debug["timeout_ms"]
    ) else "no"
    invariants_match = "yes" if (
        release["inv_configured"] == debug["inv_configured"]
        and release["inv_resolved"] == debug["inv_resolved"]
        and release["inv_configured_names"] == debug["inv_configured_names"]
        and release["inv_resolved_names"] == debug["inv_resolved_names"]
    ) else "no"

fields = [
    release["evidence_class"],
    release["proof_strength"],
    release["state_dedup"],
    release["lossy_reasons"],
    release["symmetry_count"],
    release["por_heuristic"],
    release["max_depth"],
    release["max_states"],
    release["timeout_ms"],
    release["inv_resolved"],
    release["inv_configured"],
    bounds_match,
    invariants_match,
]
print("|".join(str(field) for field in fields))
PY
}

summary_field() {
    local file="$1" prefix="$2"
    if [[ ! -f "$file" ]]; then
        echo "n/a"
        return
    fi
    local line
    line=$(grep "^$prefix" "$file" 2>/dev/null | head -1 || true)
    if [[ -z "$line" ]]; then
        echo "n/a"
        return
    fi
    echo "${line#$prefix}"
}

format_ratio_debug_over_release() {
    local debug_wall="$1" release_wall="$2"
    if [[ ! "$debug_wall" =~ ^[0-9]+$ ]] || [[ ! "$release_wall" =~ ^[0-9]+$ ]] || [[ "$release_wall" -eq 0 ]]; then
        echo "n/a"
        return
    fi
    python3 - "$debug_wall" "$release_wall" <<'PY'
import sys
debug_wall = int(sys.argv[1])
release_wall = int(sys.argv[2])
print(f"{debug_wall / release_wall:.2f}x")
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

    if $has_sf_release || $has_sf_debug; then
        echo "## Source-first Build/Environment Parity (Phase 33.4.4.a)"
        echo ""
        if $has_sf_release; then
            echo "- Canonical source-first performance view: **release build** (\`${SF_RELEASE_DIR#$PROJECT_ROOT/}\`)."
        else
            echo "- Canonical source-first performance view: release summary missing; temporarily using debug/fallback results."
        fi
        if $has_sf_debug; then
            echo "- Continuity baseline retained: **debug build** (\`${SF_DEBUG_DIR#$PROJECT_ROOT/}\`)."
        fi
        echo ""
        if $has_sf_release; then
            echo "- Release run context:"
            echo "  - Build profile: $(summary_field "$sf_release_summary" "Build profile: ")"
            echo "  - Threading mode: $(summary_field "$sf_release_summary" "Threading mode: ") (workers=$(summary_field "$sf_release_summary" "Workers: "))"
            echo "  - Timeout override (ms): $(summary_field "$sf_release_summary" "Timeout override (ms): ")"
            echo "  - Machine: $(summary_field "$sf_release_summary" "Machine: ")"
            echo "  - Host: $(summary_field "$sf_release_summary" "Host: ")"
        fi
        if $has_sf_debug; then
            echo "- Debug run context:"
            echo "  - Build profile: $(summary_field "$sf_debug_summary" "Build profile: ")"
            echo "  - Threading mode: $(summary_field "$sf_debug_summary" "Threading mode: ") (workers=$(summary_field "$sf_debug_summary" "Workers: "))"
            echo "  - Timeout override (ms): $(summary_field "$sf_debug_summary" "Timeout override (ms): ")"
            echo "  - Machine: $(summary_field "$sf_debug_summary" "Machine: ")"
            echo "  - Host: $(summary_field "$sf_debug_summary" "Host: ")"
        fi
        echo ""
        echo "| Protocol | Release result | Release wall (s) | Release stop reason | Debug result | Debug wall (s) | Debug stop reason | Debug/Release wall ratio |"
        echo "|----------|----------------|------------------|---------------------|--------------|----------------|-------------------|--------------------------|"
        for proto in $PROTOCOLS; do
            IFS='|' read -r sf_rel_result _ _ _ sf_rel_wall <<< "$(parse_row "$sf_release_summary" "$proto")"
            IFS='|' read -r sf_dbg_result _ _ _ sf_dbg_wall <<< "$(parse_row "$sf_debug_summary" "$proto")"
            IFS='|' read -r _ _ _ sf_rel_stop_reason <<< "$(parse_source_first_artifact_details "$SF_RELEASE_DIR/${proto}_benchmark.json")"
            IFS='|' read -r _ _ _ sf_dbg_stop_reason <<< "$(parse_source_first_artifact_details "$SF_DEBUG_DIR/${proto}_benchmark.json")"
            wall_ratio="$(format_ratio_debug_over_release "$sf_dbg_wall" "$sf_rel_wall")"
            echo "| $(protocol_display "$proto") | $sf_rel_result | $sf_rel_wall | $sf_rel_stop_reason | $sf_dbg_result | $sf_dbg_wall | $sf_dbg_stop_reason | $wall_ratio |"
        done
        echo ""
    fi

    if $has_sf; then
        echo "## Phase-Attributed Source-First Timing Breakdown (ms)"
        echo ""
        echo "Canonical source-first timing values come from \`${SF_DIR#$PROJECT_ROOT/}\` JSON artifacts."
        echo ""
        echo "| Protocol | Source ingest | Model/config | Init construction | Successor solving | Candidate gen/eval | Dedup/hash/normalize | Invariant eval | Report serialize/output |"
        echo "|----------|---------------|--------------|-------------------|-------------------|--------------------|----------------------|----------------|--------------------------|"
        for proto in $PROTOCOLS; do
            IFS='|' read -r t_ingest t_model t_init t_solve t_candidate t_dedup t_invariant t_report <<< "$(parse_source_first_timing_breakdown "$SF_DIR/${proto}_benchmark.json")"
            echo "| $(protocol_display "$proto") | $t_ingest | $t_model | $t_init | $t_solve | $t_candidate | $t_dedup | $t_invariant | $t_report |"
        done
        echo ""
    fi

    if $has_sf_release; then
        echo "## Small-Model Wall-Time Gap Diagnosis (Phase 33.4.4.c)"
        echo ""
        echo "This section is restricted to the two shared small-model protocols that currently finish in exact mode (TwoPhase, PrimaryBackup)."
        echo "The diagnosis is computed from release canonical telemetry plus debug-vs-release elapsed-ms ratios."
        echo ""
        echo "| Protocol | Release wall (ms) | Candidate gen/eval (ms) | Candidate share | Fixed startup+parsing share | Dedup/hash share | Invariant share | Debug/Release (elapsed-ms) | Dominant release phase | Fixed-overhead dominates? | Dedup meaningful? | Release materially changes wall time? |"
        echo "|----------|-------------------|--------------------------|-----------------|-----------------------------|------------------|-----------------|-----------------------------|------------------------|---------------------------|-------------------|----------------------------------------|"
        for proto in twophase primarybackup; do
            IFS='|' read -r release_wall_ms candidate_ms candidate_pct fixed_ms fixed_pct dedup_ms dedup_pct invariant_ms invariant_pct debug_release_ratio dominant_phase fixed_overhead_dominates dedup_meaningful release_material <<< "$(parse_small_model_gap_diagnosis "$SF_RELEASE_DIR/${proto}_benchmark.json" "$SF_DEBUG_DIR/${proto}_benchmark.json")"
            echo "| $(protocol_display "$proto") | $release_wall_ms | $candidate_ms | $candidate_pct | $fixed_pct ($fixed_ms ms) | $dedup_pct ($dedup_ms ms) | $invariant_pct ($invariant_ms ms) | $debug_release_ratio | $dominant_phase | $fixed_overhead_dominates | $dedup_meaningful | $release_material |"
        done
        echo ""
        for proto in twophase primarybackup; do
            IFS='|' read -r _ _ candidate_pct _ fixed_pct _ dedup_pct _ invariant_pct debug_release_ratio dominant_phase fixed_overhead_dominates dedup_meaningful release_material <<< "$(parse_small_model_gap_diagnosis "$SF_RELEASE_DIR/${proto}_benchmark.json" "$SF_DEBUG_DIR/${proto}_benchmark.json")"
            echo "- $(protocol_display "$proto"): dominant release cost is \`$dominant_phase\` (candidate=$candidate_pct, fixed=$fixed_pct, dedup=$dedup_pct, invariant=$invariant_pct). Fixed-overhead dominates: **$fixed_overhead_dominates**. Dedup meaningful: **$dedup_meaningful**. Release materially changes wall time: **$release_material** (debug/release=$debug_release_ratio)."
        done
        echo ""
        echo "- Cross-protocol conclusion: neither small model is currently fixed-overhead dominated; both are dominated by successor solving on current release telemetry. Dedup/hash is now non-negligible on both runs, while invariant checking remains negligible. Release build materially reduces wall time on both protocols without changing the dominant phase."
        echo ""

        echo "## Branch-Level Blocker Telemetry (Phase 33.4.4.d)"
        echo ""
        echo "Branch rows come from release canonical source-first artifacts (${SF_RELEASE_DIR#$PROJECT_ROOT/}), sorted by cumulative branch solve time."
        echo "Tables focus on exact-mode blocker protocols (LeaderElection, Paxos) and keep only top branch families for compact auditability."
        echo ""
        for proto in leaderelection paxos; do
            echo "### $(protocol_display "$proto")"
            echo ""
            echo "| Branch label | Existential assignments | Candidate states | Direct solver hits | Enumeration fallback hits | Guard-pruned evals | Successful successors | Cumulative solve ms |"
            echo "|--------------|-------------------------|------------------|--------------------|---------------------------|--------------------|-----------------------|---------------------|"
            rows_emitted=0
            max_rows=4
            if [[ "$proto" == "paxos" ]]; then
                max_rows=7
            fi
            while IFS='|' read -r branch_label existential_count candidate_count direct_hits enumeration_hits guard_pruned_count successful_successors cumulative_solve_ms; do
                [[ -z "$branch_label" ]] && continue
                echo "| $branch_label | $existential_count | $candidate_count | $direct_hits | $enumeration_hits | $guard_pruned_count | $successful_successors | $cumulative_solve_ms |"
                rows_emitted=$((rows_emitted + 1))
            done < <(parse_source_first_branch_blockers "$SF_RELEASE_DIR/${proto}_benchmark.json" "$max_rows")
            if [[ "$rows_emitted" -eq 0 ]]; then
                echo "| n/a | n/a | n/a | n/a | n/a | n/a | n/a | n/a |"
            fi
            echo ""
        done
        echo "- Phase 33.4.4.f (Paxos blocker reduction): release telemetry now shows direct helper-branch solving with \`enumeration_fallback_hits=0\` and \`enumeration_eval=0\`; prior blocker rows \`branch_0\` and \`branch_2\` no longer fall back to candidate enumeration."
        echo ""
        echo "- Interpretation rule for blocker narratives: prioritize branch families with highest cumulative solve ms and enumeration fallback hits; use existential/candidate counts plus guard-pruned/successor outcomes to distinguish domain blow-up from guard-filtered dead-ends."
        echo ""

        echo "## Explicit Root-Cause Answers (Phase 33.4.4.g)"
        echo ""
        echo "- **Why is source-first currently slower on the protocols that finish?**"
        IFS='|' read -r tp_release_ms _ tp_candidate_pct tp_fixed_ms tp_fixed_pct tp_dedup_ms tp_dedup_pct _ tp_invariant_pct tp_debug_release_ratio tp_dominant_phase tp_fixed_overhead_dominates tp_dedup_meaningful _ <<< "$(parse_small_model_gap_diagnosis "$SF_RELEASE_DIR/twophase_benchmark.json" "$SF_DEBUG_DIR/twophase_benchmark.json")"
        IFS='|' read -r pb_release_ms _ pb_candidate_pct pb_fixed_ms pb_fixed_pct pb_dedup_ms pb_dedup_pct _ pb_invariant_pct pb_debug_release_ratio pb_dominant_phase pb_fixed_overhead_dominates pb_dedup_meaningful _ <<< "$(parse_small_model_gap_diagnosis "$SF_RELEASE_DIR/primarybackup_benchmark.json" "$SF_DEBUG_DIR/primarybackup_benchmark.json")"
        echo "  - **Answer:** release telemetry shows the dominant phase is solver work (\`$tp_dominant_phase\` for TwoPhase and \`$pb_dominant_phase\` for PrimaryBackup), not fixed startup overhead."
        echo "  - TwoPhase evidence: wall=${tp_release_ms}ms, candidate share=${tp_candidate_pct}, fixed share=${tp_fixed_pct} (${tp_fixed_ms}ms, dominates=${tp_fixed_overhead_dominates}), dedup share=${tp_dedup_pct} (${tp_dedup_ms}ms, meaningful=${tp_dedup_meaningful}), invariant share=${tp_invariant_pct}, debug/release=${tp_debug_release_ratio}."
        echo "  - PrimaryBackup evidence: wall=${pb_release_ms}ms, candidate share=${pb_candidate_pct}, fixed share=${pb_fixed_pct} (${pb_fixed_ms}ms, dominates=${pb_fixed_overhead_dominates}), dedup share=${pb_dedup_pct} (${pb_dedup_ms}ms, meaningful=${pb_dedup_meaningful}), invariant share=${pb_invariant_pct}, debug/release=${pb_debug_release_ratio}."
        echo "  - Conclusion: release build materially helps, but the remaining wall-time gap is primarily successor-solving overhead rather than startup or invariant checking."
        echo ""
        echo "- **Why do LeaderElection and Paxos still block under matched benchmarks?**"
        for proto in leaderelection paxos; do
            IFS='|' read -r stop_reason states transitions elapsed_ms enum_evals direct_solves enum_fallback_solves max_existentials max_candidates top_branch_label top_branch_ms top_branch_enum_hits top_branch_direct_hits blocked_cause <<< "$(parse_blocker_root_cause "$SF_RELEASE_DIR/${proto}_benchmark.json")"
            proto_name="$(protocol_display "$proto")"
            if [[ "$blocked_cause" == "enumeration_fallback_pressure" ]]; then
                echo "  - **$proto_name:** stop_reason=$stop_reason with timeout at ${elapsed_ms}ms (states=$states, transitions=$transitions). Blocked mainly by enumeration fallback pressure (enum_eval=$enum_evals, enum_fallback_branch_solves=$enum_fallback_solves, top_branch=$top_branch_label enum_hits=$top_branch_enum_hits)."
            elif [[ "$blocked_cause" == "direct_solver_domain_pressure" ]]; then
                echo "  - **$proto_name:** stop_reason=$stop_reason with timeout at ${elapsed_ms}ms (states=$states, transitions=$transitions). Blocked mainly by large-domain direct solving, not enumeration fallback (enum_eval=$enum_evals, enum_fallback_branch_solves=$enum_fallback_solves, direct_solves=$direct_solves, top_branch=$top_branch_label direct_hits=$top_branch_direct_hits, max_existentials=$max_existentials, max_candidates=$max_candidates, top_branch_solve_ms=$top_branch_ms)."
            else
                echo "  - **$proto_name:** stop_reason=$stop_reason (states=$states, transitions=$transitions, elapsed_ms=$elapsed_ms)."
            fi
        done
        echo "  - Conclusion: the current blocker is timeout under high branch-domain solve cost; further wins require reducing existential/candidate-domain solve pressure in hot branches."
        echo ""

        echo "## Anti-Corner-Cutting Guardrails (Phase 33.4.4.h)"
        echo ""
        echo "- Rule 1: Do not shrink benchmark models or weaken invariants just to make source-first look faster."
        echo "- Rule 2: Do not switch the primary comparison to lossy search modes (\`hash_compaction64\`, symmetry merging, etc.)."
        echo "- Rule 3: Do not compare release TLC against debug source-first and call the result final without also checking release source-first."
        echo "- Rule 4: Do not claim a speedup fix based only on wall time if reachable-state counts or exact-mode semantics changed."
        echo "- Rule 5: Do not stop at aggregate \"states/sec\"; keep phase-attributed timing and branch-level blocker attribution."
        echo ""
        echo "The table below records guardrail evidence from checked-in release artifacts and release-vs-debug parity checks."
        echo ""
        echo "| Protocol | Release evidence class | Proof strength | Dedup mode | Lossy reasons | Symmetry fields | POR heuristic | Max depth | Max states | Timeout (ms) | Invariants (resolved/configured) | Release-vs-debug bounds match | Release-vs-debug invariant set match |"
        echo "|----------|------------------------|----------------|------------|---------------|-----------------|---------------|-----------|------------|--------------|----------------------------------|-------------------------------|--------------------------------------|"
        for proto in $PROTOCOLS; do
            IFS='|' read -r evidence_class proof_strength state_dedup lossy_reasons symmetry_count por_heuristic max_depth max_states timeout_ms inv_resolved inv_configured bounds_match invariants_match <<< "$(parse_anti_corner_cutting_status "$SF_RELEASE_DIR/${proto}_benchmark.json" "$SF_DEBUG_DIR/${proto}_benchmark.json")"
            echo "| $(protocol_display "$proto") | $evidence_class | $proof_strength | $state_dedup | $lossy_reasons | $symmetry_count | $por_heuristic | $max_depth | $max_states | $timeout_ms | $inv_resolved/$inv_configured | $bounds_match | $invariants_match |"
        done
        echo ""
        echo "- Guardrail interpretation: exact evidence requires \`evidence_class=exact_proof_strength\`, proof-strength search, canonical dedup, no lossy reasons, and no symmetry-merging in primary artifacts."
        echo "- Guardrail interpretation: release-vs-debug parity checks above ensure benchmark bounds/invariant sets were not quietly relaxed for release-only comparisons."
        echo ""
    fi

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
    IFS='|' read -r le_result _ _ _ _ <<< "$(parse_row "$sf_summary" "leaderelection")"
    IFS='|' read -r _ _ le_enum_evals le_stop_reason <<< "$(parse_source_first_artifact_details "$SF_DIR/leaderelection_benchmark.json")"
    IFS='|' read -r px_result _ _ _ _ <<< "$(parse_row "$sf_summary" "paxos")"
    IFS='|' read -r _ _ px_enum_evals px_stop_reason <<< "$(parse_source_first_artifact_details "$SF_DIR/paxos_benchmark.json")"
    echo "- LeaderElection source-first status: \`$le_result\` (stop_reason=$le_stop_reason, enumeration_eval=$le_enum_evals)."
    echo "- Paxos source-first status: \`$px_result\` (stop_reason=$px_stop_reason, enumeration_eval=$px_enum_evals)."
    echo "  See branch-level blocker telemetry above for per-branch evidence."
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
