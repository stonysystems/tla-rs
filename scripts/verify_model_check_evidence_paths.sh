#!/usr/bin/env bash
# Verify that all model-check JSON artifact paths referenced by
# docs/model_checker_status.md exist on disk.
#
# Usage:
#   ./scripts/verify_model_check_evidence_paths.sh
#   STATUS_DOC=docs/model_checker_status.md ./scripts/verify_model_check_evidence_paths.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
STATUS_DOC="${STATUS_DOC:-$PROJECT_ROOT/docs/model_checker_status.md}"

if [[ ! -f "$STATUS_DOC" ]]; then
    echo "Error: status doc not found: $STATUS_DOC" >&2
    exit 1
fi

mapfile -t ARTIFACT_PATHS < <(grep -oE 'reports/model_check/[A-Za-z0-9._-]+\.json' "$STATUS_DOC" | sort -u)

if [[ ${#ARTIFACT_PATHS[@]} -eq 0 ]]; then
    echo "Error: no model-check JSON artifact paths found in $STATUS_DOC" >&2
    exit 1
fi

MISSING=()
for rel_path in "${ARTIFACT_PATHS[@]}"; do
    abs_path="$PROJECT_ROOT/$rel_path"
    if [[ ! -f "$abs_path" ]]; then
        MISSING+=("$rel_path")
    fi
done

if [[ ${#MISSING[@]} -gt 0 ]]; then
    echo "Error: missing model-check evidence artifacts referenced in status doc:" >&2
    for rel_path in "${MISSING[@]}"; do
        echo "  - $rel_path" >&2
    done
    echo "Hint: run ./scripts/run_model_check_matrix.sh to regenerate reports/model_check artifacts." >&2
    exit 1
fi

echo "Model-check evidence paths verified (${#ARTIFACT_PATHS[@]} artifacts)."
