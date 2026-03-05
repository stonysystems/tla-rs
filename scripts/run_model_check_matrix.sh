#!/usr/bin/env bash
# Run the currently supported source-first model-check matrix and emit JSON
# artifacts under reports/model_check/.
#
# Usage:
#   ./scripts/run_model_check_matrix.sh
#   OUTPUT_DIR=reports/model_check ./scripts/run_model_check_matrix.sh
#   TRANSPILER_BIN=transpiler/target/release/verus-transpile ./scripts/run_model_check_matrix.sh
#   TELEMETRY_DELTA_REPORT=reports/model_check/OPTIMIZATION_DELTAS.md ./scripts/run_model_check_matrix.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
OUTPUT_DIR="${OUTPUT_DIR:-$PROJECT_ROOT/reports/model_check}"
TRANSPILER_BIN="${TRANSPILER_BIN:-$PROJECT_ROOT/transpiler/target/debug/verus-transpile}"
TELEMETRY_DELTA_REPORT="${TELEMETRY_DELTA_REPORT:-$OUTPUT_DIR/OPTIMIZATION_DELTAS.md}"

mkdir -p "$OUTPUT_DIR"

if [[ ! -x "$TRANSPILER_BIN" ]]; then
    echo "Building transpiler binary ($TRANSPILER_BIN)..."
    cargo build --manifest-path "$PROJECT_ROOT/transpiler/Cargo.toml" --bin verus-transpile
fi

declare -a MATRIX_CASES=(
    "twophase_small|src/protocol/TwoPhase/twophase.rs|src/protocol/TwoPhase/types.rs|transpiler/tests/model_check_fixtures/twophase_small.model.toml"
    "primarybackup_small|src/protocol/PrimaryBackup/primarybackup.rs|src/protocol/PrimaryBackup/types.rs|transpiler/tests/model_check_fixtures/primarybackup_small.model.toml"
    "leaderelection_small|src/protocol/LeaderElection/election.rs|src/protocol/LeaderElection/types.rs|transpiler/tests/model_check_fixtures/leaderelection_small.model.toml"
    "paxos_small|src/protocol/Paxos/paxos.rs|src/protocol/Paxos/types.rs|transpiler/tests/model_check_fixtures/paxos_small.model.toml"
    "guard_pruned_enumeration|transpiler/tests/model_check_fixtures/guard_pruned_enumeration.protocol.rs|transpiler/tests/model_check_fixtures/guard_pruned_enumeration.types.rs|transpiler/tests/model_check_fixtures/guard_pruned_enumeration.model.toml"
    "liveness_avoidable_cycle_violated|transpiler/tests/model_check_fixtures/liveness_avoidable_cycle.protocol.rs|transpiler/tests/model_check_fixtures/liveness_avoidable_cycle.types.rs|transpiler/tests/model_check_fixtures/liveness_avoidable_cycle_violated.model.toml"
    "liveness_avoidable_cycle_strong_fairness|transpiler/tests/model_check_fixtures/liveness_avoidable_cycle.protocol.rs|transpiler/tests/model_check_fixtures/liveness_avoidable_cycle.types.rs|transpiler/tests/model_check_fixtures/liveness_avoidable_cycle_strong_fairness.model.toml"
    "liveness_forced_unfair|transpiler/tests/model_check_fixtures/liveness_forced.protocol.rs|transpiler/tests/model_check_fixtures/liveness_forced.types.rs|transpiler/tests/model_check_fixtures/liveness_forced_unfair.model.toml"
    "liveness_forced_strong_fairness|transpiler/tests/model_check_fixtures/liveness_forced.protocol.rs|transpiler/tests/model_check_fixtures/liveness_forced.types.rs|transpiler/tests/model_check_fixtures/liveness_forced_strong_fairness.model.toml"
)

rm -f "$OUTPUT_DIR"/*.json "$OUTPUT_DIR"/MANIFEST.txt

echo "Running source-first model-check matrix..."
for case_entry in "${MATRIX_CASES[@]}"; do
    IFS='|' read -r case_name input_path types_path model_path <<<"$case_entry"
    artifact_path="$OUTPUT_DIR/${case_name}.json"
    echo "  - $case_name -> ${artifact_path#$PROJECT_ROOT/}"
    (
        cd "$PROJECT_ROOT"
        "$TRANSPILER_BIN" model-check \
            --input "$input_path" \
            --types "$types_path" \
            --model "$model_path" \
            --search bfs \
            --json-report
    ) >"$artifact_path"

    if ! grep -q '"result"' "$artifact_path"; then
        echo "Error: missing JSON result field in $artifact_path" >&2
        exit 1
    fi
done

echo "Generating optimization telemetry comparison report..."
(
    cd "$PROJECT_ROOT"
    ARTIFACT_DIR="$OUTPUT_DIR" OUTPUT_PATH="$TELEMETRY_DELTA_REPORT" \
        bash "$PROJECT_ROOT/scripts/compare_model_check_telemetry.sh"
)

{
    echo "source_first_matrix_artifacts:"
    echo "  generated_by: scripts/run_model_check_matrix.sh"
    echo "  git_rev: $(git -C "$PROJECT_ROOT" rev-parse HEAD)"
    echo "  output_dir: ${OUTPUT_DIR#$PROJECT_ROOT/}"
    echo "  artifacts:"
    for case_entry in "${MATRIX_CASES[@]}"; do
        IFS='|' read -r case_name _ <<<"$case_entry"
        echo "    - ${case_name}.json"
    done
    echo "    - $(basename "$TELEMETRY_DELTA_REPORT")"
} >"$OUTPUT_DIR/MANIFEST.txt"

echo "Model-check matrix artifacts written under ${OUTPUT_DIR#$PROJECT_ROOT/}."
