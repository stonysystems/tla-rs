#!/bin/bash
# Local reproduction of the GitHub Actions CI workflow.
# Mirrors the 5 jobs in .github/workflows/ci.yml.
#
# Usage:
#   ./scripts/run_ci_local.sh          # Run all jobs
#   ./scripts/run_ci_local.sh format   # Run only format check
#   ./scripts/run_ci_local.sh lint     # Run only lint check
#   ./scripts/run_ci_local.sh test     # Run only test
#   ./scripts/run_ci_local.sh evidence # Run only model-check evidence
#
# Note: The `verify` job requires a specific Verus version and is skipped
# by default. Set VERUS_PATH to enable it.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TRANSPILER_DIR="$REPO_ROOT/transpiler"
SELECTED="${1:-all}"
PASS=0
FAIL=0
SKIP=0

run_job() {
    local name="$1"
    local cmd="$2"
    echo ""
    echo "=== CI / $name ==="
    if eval "$cmd" 2>&1; then
        echo "  PASS"
        PASS=$((PASS + 1))
    else
        echo "  FAIL"
        FAIL=$((FAIL + 1))
    fi
}

skip_job() {
    local name="$1"
    local reason="$2"
    echo ""
    echo "=== CI / $name === SKIPPED ($reason)"
    SKIP=$((SKIP + 1))
}

# Job 1: Format
run_format() {
    run_job "Format (push)" "cd '$TRANSPILER_DIR' && cargo fmt --check"
}

# Job 2: Lint
run_lint() {
    run_job "Lint (push)" "cd '$TRANSPILER_DIR' && cargo clippy --all-targets --all-features -- -D warnings"
}

# Job 3: Test
run_test() {
    run_job "Test (push)" "cd '$TRANSPILER_DIR' && cargo test --all-features"
}

# Job 4: Verus Verification
run_verify() {
    if [ -n "${VERUS_PATH:-}" ] && [ -f "$VERUS_PATH" ]; then
        run_job "Verus Verification (push)" "cd '$REPO_ROOT' && scons --verus-path='$VERUS_PATH' --skip-dotnet"
    else
        skip_job "Verus Verification (push)" "VERUS_PATH not set or not found"
    fi
}

# Job 5: Model-Check Evidence Drift Guard
run_evidence() {
    run_job "Model-Check Evidence Drift Guard (push)" \
        "cd '$REPO_ROOT' && ./scripts/run_model_check_matrix.sh && ./scripts/verify_model_check_evidence_paths.sh"
}

case "$SELECTED" in
    format)   run_format ;;
    lint)     run_lint ;;
    test)     run_test ;;
    verify)   run_verify ;;
    evidence) run_evidence ;;
    all)
        run_format
        run_lint
        run_test
        run_verify
        run_evidence
        ;;
    *)
        echo "Unknown job: $SELECTED"
        echo "Usage: $0 [format|lint|test|verify|evidence|all]"
        exit 2
        ;;
esac

echo ""
echo "========================================"
echo "CI Local Summary: $PASS pass, $FAIL fail, $SKIP skip"
echo "========================================"

if [ "$FAIL" -gt 0 ]; then
    exit 1
fi
