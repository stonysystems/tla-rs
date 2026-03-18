#!/usr/bin/env bash
# Compare fixed "before" baselines vs current checked-in model-check telemetry
# artifacts for Phase 33.4 optimization metrics.
#
# Usage:
#   ./scripts/compare_model_check_telemetry.sh
#   ARTIFACT_DIR=reports/model_check ./scripts/compare_model_check_telemetry.sh
#   OUTPUT_PATH=reports/model_check/OPTIMIZATION_DELTAS.md ./scripts/compare_model_check_telemetry.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
ARTIFACT_DIR="${ARTIFACT_DIR:-$PROJECT_ROOT/reports/model_check}"
OUTPUT_PATH="${OUTPUT_PATH:-}"
STATUS_DOC="${STATUS_DOC:-$PROJECT_ROOT/docs/model_checker_status.md}"

if [[ ! -d "$ARTIFACT_DIR" ]]; then
    echo "Error: artifact directory not found: $ARTIFACT_DIR" >&2
    exit 1
fi
if [[ ! -f "$STATUS_DOC" ]]; then
    echo "Error: status doc not found: $STATUS_DOC" >&2
    exit 1
fi

json_get_int() {
    local json_path="$1"
    local pointer="$2"
    python3 - "$json_path" "$pointer" <<'PY'
import json
import sys

json_path = sys.argv[1]
pointer = sys.argv[2]

with open(json_path, "r", encoding="utf-8") as f:
    data = json.load(f)

node = data
if pointer != "/":
    for part in [p for p in pointer.split("/") if p]:
        if not isinstance(node, dict) or part not in node:
            raise SystemExit(f"missing pointer {pointer} in {json_path}")
        node = node[part]

if not isinstance(node, int):
    raise SystemExit(f"non-integer pointer {pointer} in {json_path}: {node!r}")

print(node)
PY
}

declare -a DELTA_CASES=(
    "33.4.2.a successor memoization|liveness_avoidable_cycle_violated.json|successor_cache_hits|/summary/successor_cache_hits|0|3/5"
    "33.4.2.a successor memoization|liveness_avoidable_cycle_violated.json|successor_cache_misses|/summary/successor_cache_misses|0|3/5"
    "33.4.2.b guard-pruned fallback enumeration|guard_pruned_enumeration.json|enumeration_candidate_evaluations|/summary/enumeration_candidate_evaluations|2|1/0"
    "33.4.2.b guard-pruned fallback enumeration|guard_pruned_enumeration.json|guard_pruned_candidate_evaluations|/summary/guard_pruned_candidate_evaluations|0|1/0"
)

declare -a EXACT_GUARD_CASES=(
    "reports/model_check/paxos_small.json|1/2"
    "reports/model_check/primarybackup_small.json|3/3"
    "reports/model_check/twophase_small.json|3/4"
    "reports/model_check/leaderelection_small.json|4/3"
    "reports/model_check/liveness_avoidable_cycle_violated.json|3/5"
    "reports/model_check/guard_pruned_enumeration.json|1/0"
)

OUTPUT=""
OUTPUT+="# Model-Check Optimization Telemetry Comparison"$'\n'
OUTPUT+=$'\n'
OUTPUT+="| Optimization | Artifact | Metric | Before | After | Delta | Reachable-state guard |"$'\n'
OUTPUT+="| --- | --- | --- | --- | --- | --- | --- |"$'\n'

declare -a GUARD_MISMATCHES=()
declare -a EXACT_POLICY_ERRORS=()

for case_entry in "${DELTA_CASES[@]}"; do
    IFS='|' read -r optimization artifact_file metric metric_pointer before expected_guard <<<"$case_entry"
    artifact_path="$ARTIFACT_DIR/$artifact_file"
    if [[ ! -f "$artifact_path" ]]; then
        echo "Error: missing artifact for telemetry comparison: $artifact_path" >&2
        exit 1
    fi

    after="$(json_get_int "$artifact_path" "$metric_pointer")"
    states="$(json_get_int "$artifact_path" "/summary/states")"
    transitions="$(json_get_int "$artifact_path" "/summary/transitions")"
    observed_guard="${states}/${transitions}"

    delta=$((after - before))
    if ((delta >= 0)); then
        delta_display="+${delta}"
    else
        delta_display="${delta}"
    fi

    if [[ "$observed_guard" != "$expected_guard" ]]; then
        GUARD_MISMATCHES+=(
            "${artifact_file}:${metric}:expected=${expected_guard},observed=${observed_guard}"
        )
    fi

    OUTPUT+="| ${optimization} | \`reports/model_check/${artifact_file}\` | \`${metric}\` | \`${before}\` | \`${after}\` | \`${delta_display}\` | \`${expected_guard} -> ${observed_guard}\` |"$'\n'
done

OUTPUT+=$'\n'
OUTPUT+="## Exact-Mode Reachable-State Guard Policy"$'\n'
OUTPUT+=$'\n'
OUTPUT+="| Artifact | Baseline guard | Observed guard | Policy status |"$'\n'
OUTPUT+="| --- | --- | --- | --- |"$'\n'

for case_entry in "${EXACT_GUARD_CASES[@]}"; do
    IFS='|' read -r artifact_rel expected_guard <<<"$case_entry"
    artifact_path="$PROJECT_ROOT/$artifact_rel"
    if [[ ! -f "$artifact_path" ]]; then
        echo "Error: missing artifact for exact-mode guard policy: $artifact_path" >&2
        exit 1
    fi

    states="$(json_get_int "$artifact_path" "/summary/states")"
    transitions="$(json_get_int "$artifact_path" "/summary/transitions")"
    observed_guard="${states}/${transitions}"

    if [[ "$observed_guard" == "$expected_guard" ]]; then
        OUTPUT+="| \`${artifact_rel}\` | \`${expected_guard}\` | \`${observed_guard}\` | ok |"$'\n'
        continue
    fi

    guard_token="\`${expected_guard} -> ${observed_guard}\`"
    doc_line="$(grep -F "${artifact_rel}" "$STATUS_DOC" | grep -F "$guard_token" | grep -i "correctness bug fix" || true)"
    if [[ -n "$doc_line" ]]; then
        OUTPUT+="| \`${artifact_rel}\` | \`${expected_guard}\` | \`${observed_guard}\` | documented correctness bug fix |"$'\n'
    else
        OUTPUT+="| \`${artifact_rel}\` | \`${expected_guard}\` | \`${observed_guard}\` | rejected: undocumented exactness change |"$'\n'
        EXACT_POLICY_ERRORS+=(
            "${artifact_rel}: expected ${expected_guard}, observed ${observed_guard} (missing correctness bug fix documentation in docs/model_checker_status.md)"
        )
    fi
done

if [[ ${#GUARD_MISMATCHES[@]} -gt 0 ]]; then
    OUTPUT+=$'\n'
    OUTPUT+="Guard mismatches detected:"$'\n'
    for mismatch in "${GUARD_MISMATCHES[@]}"; do
        OUTPUT+="- ${mismatch}"$'\n'
    done
fi
if [[ ${#EXACT_POLICY_ERRORS[@]} -gt 0 ]]; then
    OUTPUT+=$'\n'
    OUTPUT+="Exact-mode policy violations detected:"$'\n'
    for err in "${EXACT_POLICY_ERRORS[@]}"; do
        OUTPUT+="- ${err}"$'\n'
    done
fi

if [[ -n "$OUTPUT_PATH" ]]; then
    mkdir -p "$(dirname "$OUTPUT_PATH")"
    printf "%s" "$OUTPUT" >"$OUTPUT_PATH"
    echo "Wrote telemetry comparison report to ${OUTPUT_PATH#$PROJECT_ROOT/}"
else
    printf "%s" "$OUTPUT"
fi

if [[ ${#GUARD_MISMATCHES[@]} -gt 0 ]]; then
    echo "Error: reachable-state guard mismatch detected in telemetry comparison." >&2
    exit 1
fi
if [[ ${#EXACT_POLICY_ERRORS[@]} -gt 0 ]]; then
    echo "Error: exact-mode reachable-state policy violation detected." >&2
    exit 1
fi
