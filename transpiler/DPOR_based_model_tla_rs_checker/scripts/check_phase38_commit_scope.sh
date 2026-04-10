#!/usr/bin/env bash
set -euo pipefail

usage() {
    cat <<'EOF'
check_phase38_commit_scope.sh

Enforces TODO 38.10.3.a commit-scope discipline:
- Keep Phase 38 feature work prototype-local when possible.
- Do not mix incubator changes with mainline modelchecker rewrites in one commit.
- Require explicit justification for standalone mainline modelchecker bug-fix commits.

Default behavior:
- Inspect staged paths from `git diff --cached --name-only`.

Optional explicit paths:
- Pass repeated `--path <repo-relative-path>` arguments.

Override (exception-only):
- Set `PHASE38_ALLOW_MIXED_COMMIT=1` and
  `PHASE38_MIXED_COMMIT_JUSTIFICATION=<non-empty reason>`.

Mainline-only fix requirement (TODO 38.10.3.b):
- If paths include `transpiler/src/modelcheck/**` without prototype paths,
  set `PHASE38_MAINLINE_FIX_JUSTIFICATION=<non-empty reason>`.
EOF
}

paths=()
use_staged_paths=1

while (($# > 0)); do
    case "$1" in
        --path)
            use_staged_paths=0
            shift
            if (($# == 0)); then
                echo "phase38-scope: --path requires a value" >&2
                exit 2
            fi
            paths+=("$1")
            shift
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            echo "phase38-scope: unknown argument: $1" >&2
            usage >&2
            exit 2
            ;;
    esac
done

if (( use_staged_paths == 1 )); then
    if ! git rev-parse --show-toplevel >/dev/null 2>&1; then
        echo "phase38-scope: not in a git repository; pass --path explicitly" >&2
        exit 2
    fi
    mapfile -t paths < <(git diff --cached --name-only --diff-filter=ACMRTUXB)
fi

if ((${#paths[@]} == 0)); then
    echo "phase38-scope: no changed paths to check"
    exit 0
fi

prototype_paths=()
mainline_paths=()

for path in "${paths[@]}"; do
    if [[ "$path" == transpiler/DPOR_based_model_tla_rs_checker/* ]]; then
        prototype_paths+=("$path")
    fi
    if [[ "$path" == transpiler/src/modelcheck/* ]]; then
        mainline_paths+=("$path")
    fi
done

if ((${#prototype_paths[@]} > 0 && ${#mainline_paths[@]} > 0)); then
    if [[ "${PHASE38_ALLOW_MIXED_COMMIT:-0}" == "1" ]]; then
        mixed_justification="${PHASE38_MIXED_COMMIT_JUSTIFICATION:-}"
        if [[ -z "${mixed_justification//[[:space:]]/}" ]]; then
            echo "phase38-scope: override requested but PHASE38_MIXED_COMMIT_JUSTIFICATION is empty" >&2
            exit 1
        fi
        echo "phase38-scope: mixed scope override accepted"
        echo "phase38-scope: justification: ${PHASE38_MIXED_COMMIT_JUSTIFICATION}"
        exit 0
    fi

    echo "phase38-scope: mixed prototype/mainline scope detected" >&2
    echo "phase38-scope: split the change into reviewable commits per TODO 38.10.3.a" >&2
    echo "phase38-scope: prototype paths:" >&2
    for path in "${prototype_paths[@]}"; do
        echo "  - $path" >&2
    done
    echo "phase38-scope: mainline modelcheck paths:" >&2
    for path in "${mainline_paths[@]}"; do
        echo "  - $path" >&2
    done
    echo "phase38-scope: for exceptional cases only:" >&2
    echo "  PHASE38_ALLOW_MIXED_COMMIT=1 PHASE38_MIXED_COMMIT_JUSTIFICATION='reason' $0" >&2
    exit 1
fi

if ((${#prototype_paths[@]} == 0 && ${#mainline_paths[@]} > 0)); then
    mainline_fix_justification="${PHASE38_MAINLINE_FIX_JUSTIFICATION:-}"
    if [[ -z "${mainline_fix_justification//[[:space:]]/}" ]]; then
        echo "phase38-scope: mainline-only modelcheck change requires explicit justification per TODO 38.10.3.b" >&2
        echo "phase38-scope: mainline modelcheck paths:" >&2
        for path in "${mainline_paths[@]}"; do
            echo "  - $path" >&2
        done
        echo "phase38-scope: set PHASE38_MAINLINE_FIX_JUSTIFICATION='reason' when landing a separate mainline bug-fix commit" >&2
        exit 1
    fi
    echo "phase38-scope: mainline-only fix justification accepted"
    echo "phase38-scope: justification: ${PHASE38_MAINLINE_FIX_JUSTIFICATION}"
    exit 0
fi

echo "phase38-scope: OK (prototype_paths=${#prototype_paths[@]}, mainline_paths=${#mainline_paths[@]})"
