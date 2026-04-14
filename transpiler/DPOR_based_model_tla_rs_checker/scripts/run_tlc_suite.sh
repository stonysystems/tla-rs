#!/usr/bin/env bash
# Run TLC model checking on all 20 DPOR checker test cases.
#
# For each case, reads manifest.toml and per-case model configs to generate
# a TLC .cfg file, then runs TLC and records results as JSON.
#
# Usage:
#   ./scripts/run_tlc_suite.sh                         # defaults
#   ./scripts/run_tlc_suite.sh --timeout 600            # 10 min per case
#   ./scripts/run_tlc_suite.sh --workers 8              # 8 TLC workers
#   ./scripts/run_tlc_suite.sh --timeout 600 --workers 8

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORKFOLDER="$(cd "$SCRIPT_DIR/.." && pwd)"
TLA_DIR="$WORKFOLDER/tests/tla"
MODEL_CONFIGS_DIR="$WORKFOLDER/tests/model_configs"
MANIFEST="$WORKFOLDER/tests/manifest.toml"
REPORTS_DIR="$WORKFOLDER/tests/reports"

# Auto-detect Java 11+: prefer local JDK 11 install, then system OpenJDK 11,
# then $JAVA_HOME, then PATH
if [[ -x "$HOME/jdk-11/bin/java" ]]; then
    JAVA="$HOME/jdk-11/bin/java"
elif [[ -x "/usr/lib/jvm/java-11-openjdk-amd64/bin/java" ]]; then
    JAVA="/usr/lib/jvm/java-11-openjdk-amd64/bin/java"
elif [[ -n "${JAVA_HOME:-}" && -x "$JAVA_HOME/bin/java" ]]; then
    JAVA="$JAVA_HOME/bin/java"
elif command -v java &>/dev/null; then
    JAVA="$(command -v java)"
else
    JAVA=""
fi
TLA2TOOLS="$HOME/tla2tools.jar"

TIMEOUT_SEC=1800
WORKERS=4

# Parse arguments
while [[ $# -gt 0 ]]; do
    case "$1" in
        --timeout) TIMEOUT_SEC="${2:-1800}"; shift 2 ;;
        --workers) WORKERS="${2:-4}"; shift 2 ;;
        *) echo "Unknown argument: $1"; exit 1 ;;
    esac
done

# Validate prerequisites
if [[ -z "$JAVA" || ! -x "$JAVA" ]]; then
    echo "ERROR: Java not found. Tried /usr/lib/jvm/java-11-openjdk-amd64/bin/java, \$JAVA_HOME, and PATH."
    echo "       tla2tools.jar requires Java 11+. Install with: apt install openjdk-11-jdk"
    exit 1
fi
# Check Java version (tla2tools.jar requires 11+)
java_version_major="$("$JAVA" -version 2>&1 | head -1 | sed -E 's/.*"([0-9]+)\.?.*/\1/' || echo 0)"
if [[ "$java_version_major" -lt 11 ]]; then
    echo "WARNING: Java version $(\"$JAVA\" -version 2>&1 | head -1) detected."
    echo "         tla2tools.jar requires Java 11+. Results may show UnsupportedClassVersionError."
    echo "         Install with: apt install openjdk-11-jdk"
fi
if [[ ! -f "$TLA2TOOLS" ]]; then
    echo "ERROR: tla2tools.jar not found at $TLA2TOOLS"
    exit 1
fi
if [[ ! -f "$MANIFEST" ]]; then
    echo "ERROR: Manifest not found at $MANIFEST"
    exit 1
fi

mkdir -p "$REPORTS_DIR"

TIMESTAMP="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

# Counters
TOTAL=0
PASS=0
FAIL=0
ERRORS=0
TIMEOUT_COUNT=0
INCOMPATIBLE=0
SKIPPED=0

RESULTS_JSON="["

# ---------------------------------------------------------------------------
# Helper: parse a simple TOML value (handles strings, integers, booleans).
# Usage: parse_toml_value <file> <section> <key>
#   - <section> can be dotted like "constants.assignments"
#   - Returns the raw value (strings unquoted).
# ---------------------------------------------------------------------------
parse_toml_value() {
    local file="$1" section="$2" key="$3"
    python3 -c "
import sys
try:
    # Use tomllib on 3.11+, else tomli, else manual parse
    try:
        import tomllib
    except ImportError:
        import tomli as tomllib
    with open('$file', 'rb') as f:
        data = tomllib.load(f)
    parts = '$section'.split('.')
    d = data
    for p in parts:
        d = d.get(p, {})
    val = d.get('$key', '')
    if isinstance(val, bool):
        print('true' if val else 'false')
    elif isinstance(val, list):
        print(' '.join(str(v) for v in val))
    else:
        print(val)
except Exception as e:
    print('', file=sys.stderr)
" 2>/dev/null || echo ""
}

# ---------------------------------------------------------------------------
# Helper: parse all constant assignments from a TOML config as "Key = Value"
# lines suitable for a TLC .cfg file.
# ---------------------------------------------------------------------------
parse_constants() {
    local file="$1"
    python3 -c "
import sys
try:
    try:
        import tomllib
    except ImportError:
        import tomli as tomllib
    with open('$file', 'rb') as f:
        data = tomllib.load(f)
    assignments = data.get('constants', {}).get('assignments', {})
    for k, v in assignments.items():
        print(f'{k} = {v}')
except Exception:
    pass
" 2>/dev/null || true
}

# ---------------------------------------------------------------------------
# Helper: parse invariant list from a TOML config.
# The DPOR configs use L-prefixed names (e.g., "LMutualExclusion").
# For TLC we need the actual TLA+ operator name.
# Strategy: strip the leading "L" if the TLA+ source defines the unprefixed name.
# ---------------------------------------------------------------------------
parse_invariants() {
    local file="$1"
    python3 -c "
import sys
try:
    try:
        import tomllib
    except ImportError:
        import tomli as tomllib
    with open('$file', 'rb') as f:
        data = tomllib.load(f)
    invs = data.get('properties', {}).get('invariants', [])
    for inv in invs:
        print(inv)
except Exception:
    pass
" 2>/dev/null || true
}

# ---------------------------------------------------------------------------
# Helper: check if Init/Next take explicit parameters (generated TLA+).
# ---------------------------------------------------------------------------
is_parameterized_init_next() {
    local tla_file="$1"
    if grep -qE '^\s*Init\s*\(' "$tla_file" 2>/dev/null; then
        return 0
    fi
    return 1
}

# ---------------------------------------------------------------------------
# Helper: resolve an invariant name for TLC.
# If the TLA+ source has the exact name, use it.
# If the name starts with "L" and stripping it matches, use the stripped name.
# Otherwise return the name as-is (TLC will report an error if it doesn't exist).
# ---------------------------------------------------------------------------
resolve_invariant_name() {
    local inv_name="$1" tla_dir="$2"
    # Check if the exact name exists in any .tla file in the directory
    if grep -rqE "^${inv_name}\s*==" "$tla_dir"/*.tla 2>/dev/null; then
        echo "$inv_name"
        return
    fi
    # Try stripping leading "L"
    if [[ "$inv_name" == L* ]]; then
        local stripped="${inv_name#L}"
        if grep -rqE "^${stripped}\s*==" "$tla_dir"/*.tla 2>/dev/null; then
            echo "$stripped"
            return
        fi
    fi
    # Return as-is
    echo "$inv_name"
}

# ---------------------------------------------------------------------------
# Main loop: process each case
# ---------------------------------------------------------------------------
for case_dir in "$TLA_DIR"/*/; do
    case_id="$(basename "$case_dir")"
    TOTAL=$((TOTAL + 1))

    echo -n "  [$case_id] "

    # ---- Read manifest fields ----
    tla_entry=""
    expected_result=""
    expected_property=""
    requires_deadlock_check="false"
    in_case=false
    while IFS= read -r line; do
        if [[ "$line" == *"id = \"$case_id\""* ]]; then
            in_case=true
        elif $in_case && [[ "$line" == "[[case]]"* ]]; then
            break
        elif $in_case; then
            case "$line" in
                tla_entry*) tla_entry="$(echo "$line" | sed 's/.*tla_entry = "\(.*\)"/\1/')" ;;
                expected_primary_result*) expected_result="$(echo "$line" | sed 's/.*expected_primary_result = "\(.*\)"/\1/')" ;;
                expected_property*) expected_property="$(echo "$line" | sed 's/.*expected_property = "\(.*\)"/\1/')" ;;
                requires_deadlock_check*) requires_deadlock_check="$(echo "$line" | sed 's/.*requires_deadlock_check = \(.*\)/\1/')" ;;
            esac
        fi
    done < "$MANIFEST"

    if [[ -z "$tla_entry" ]]; then
        echo "ERROR: no manifest entry found"
        ERRORS=$((ERRORS + 1))
        result_json="{\"case_id\": \"$case_id\", \"tlc_result\": \"error\", \"error\": \"no_manifest_entry\", \"states\": 0, \"elapsed_s\": 0, \"expected\": \"\"}"
        [[ "$TOTAL" -gt 1 ]] && RESULTS_JSON="$RESULTS_JSON,"
        RESULTS_JSON="$RESULTS_JSON
  $result_json"
        continue
    fi

    tla_file="$case_dir/$tla_entry"
    if [[ ! -f "$tla_file" ]]; then
        echo "ERROR: TLA+ file not found: $tla_file"
        ERRORS=$((ERRORS + 1))
        result_json="{\"case_id\": \"$case_id\", \"tlc_result\": \"error\", \"error\": \"tla_file_missing\", \"states\": 0, \"elapsed_s\": 0, \"expected\": \"$expected_result\"}"
        [[ "$TOTAL" -gt 1 ]] && RESULTS_JSON="$RESULTS_JSON,"
        RESULTS_JSON="$RESULTS_JSON
  $result_json"
        continue
    fi

    # ---- Skip known_unimplemented ----
    if [[ "$expected_result" == "known_unimplemented" ]]; then
        echo "SKIPPED (known_unimplemented)"
        SKIPPED=$((SKIPPED + 1))
        result_json="{\"case_id\": \"$case_id\", \"tlc_result\": \"skipped\", \"reason\": \"known_unimplemented\", \"states\": 0, \"elapsed_s\": 0, \"expected\": \"$expected_result\"}"
        [[ "$TOTAL" -gt 1 ]] && RESULTS_JSON="$RESULTS_JSON,"
        RESULTS_JSON="$RESULTS_JSON
  $result_json"
        continue
    fi

    # ---- Detect parameterized Init(s,c) / Next(s,s_,c) ----
    if is_parameterized_init_next "$tla_file"; then
        echo "TLC_INCOMPATIBLE (parameterized Init/Next)"
        INCOMPATIBLE=$((INCOMPATIBLE + 1))
        result_json="{\"case_id\": \"$case_id\", \"tlc_result\": \"tlc_incompatible\", \"reason\": \"parameterized_init_next\", \"states\": 0, \"elapsed_s\": 0, \"expected\": \"$expected_result\"}"
        [[ "$TOTAL" -gt 1 ]] && RESULTS_JSON="$RESULTS_JSON,"
        RESULTS_JSON="$RESULTS_JSON
  $result_json"
        continue
    fi

    # ---- Read per-case model config ----
    per_case_config="$MODEL_CONFIGS_DIR/${case_id}.toml"
    constants_block=""
    invariants_block=""
    check_deadlock="false"
    resolved_invs=""

    if [[ -f "$per_case_config" ]]; then
        # Parse constants
        constants_lines="$(parse_constants "$per_case_config")"
        if [[ -n "$constants_lines" ]]; then
            constants_block="CONSTANTS
$constants_lines"
        fi

        # Parse invariants from config
        inv_lines="$(parse_invariants "$per_case_config")"
        resolved_invs=""
        while IFS= read -r inv; do
            [[ -z "$inv" ]] && continue
            resolved="$(resolve_invariant_name "$inv" "$case_dir")"
            if [[ -n "$resolved_invs" ]]; then
                resolved_invs="$resolved_invs
$resolved"
            else
                resolved_invs="$resolved"
            fi
        done <<< "$inv_lines"

        # Parse check_deadlock
        check_deadlock="$(parse_toml_value "$per_case_config" "properties" "check_deadlock")"
    fi

    # If no invariants from config, try using the manifest's expected_property
    if [[ -z "$resolved_invs" && -n "$expected_property" ]]; then
        resolved="$(resolve_invariant_name "$expected_property" "$case_dir")"
        resolved_invs="$resolved"
    fi

    # Build INVARIANT block
    if [[ -n "$resolved_invs" ]]; then
        invariants_block="INVARIANT"
        while IFS= read -r inv; do
            [[ -z "$inv" ]] && continue
            invariants_block="$invariants_block
$inv"
        done <<< "$resolved_invs"
    fi

    # ---- Generate CONSTRAINT wrapper if needed ----
    # The DPOR checker bounds integers via [quantifiers] int = { min, max }.
    # TLC has no equivalent — specs with unbounded integer growth (a' = a + 1)
    # will never terminate. We generate a wrapper module <Module>_MC that
    # EXTENDS the original and defines a Bound operator constraining all
    # integer VARIABLE declarations to the DPOR config's int range.
    # The .cfg then uses CONSTRAINT Bound.
    #
    # We only generate the wrapper when the spec has integer variables that
    # could grow unboundedly (heuristic: the spec has '+ 1' or '- 1' patterns
    # suggesting incrementing/decrementing variables).
    module_name="${tla_entry%.tla}"
    wrapper_module=""
    wrapper_file=""
    constraint_line=""

    if [[ -f "$per_case_config" ]]; then
        int_min="$(parse_toml_value "$per_case_config" "quantifiers.int" "min")"
        int_max="$(parse_toml_value "$per_case_config" "quantifiers.int" "max")"
        max_set_len="$(parse_toml_value "$per_case_config" "collections" "max_set_len")"
    else
        int_min="0"
        int_max="5"
        max_set_len=""
    fi

    # Parse VARIABLE declarations from the TLA+ source
    tla_vars="$(grep -E '^VARIABLE[S]?\s' "$tla_file" | sed 's/^VARIABLE[S]\?\s*//' | tr ',' '\n' | sed 's/[[:space:]]//g' | grep -v '^$')"

    # Check if the spec has unbounded integer growth
    has_unbounded_growth=false
    if grep -qE "'\s*=\s*\S+\s*\+\s*1\b|'\s*=\s*\S+\s*-\s*1\b" "$tla_file" 2>/dev/null; then
        has_unbounded_growth=true
    fi

    if [[ "$has_unbounded_growth" == "true" && -n "$int_min" && -n "$int_max" && -n "$tla_vars" ]]; then
        # Generate wrapper module
        wrapper_module="${module_name}_MC"
        wrapper_file="$case_dir/${wrapper_module}.tla"

        # Build the Bound operator using Python to classify each variable.
        # We only constrain variables that are used as integers (appear in
        # arithmetic: + 1, - 1, >= N, <= N). Variables used as strings
        # (compared to "..." literals) or sets ({}, \cup, \subseteq, \in)
        # are skipped — TLC handles those natively with finite domains.
        bound_conjuncts="$(python3 -c "
import re, sys

tla_file = '$tla_file'
int_min, int_max = $int_min, $int_max
with open(tla_file) as f:
    src = f.read()

# Parse VARIABLE declarations
var_line = re.search(r'^VARIABLES?\s+(.*)', src, re.MULTILINE)
if not var_line:
    sys.exit(0)
all_vars = [v.strip() for v in var_line.group(1).split(',') if v.strip()]

conjuncts = []
for var in all_vars:
    # Skip if variable is used with string literals (pc = \"ready\", etc.)
    if re.search(rf'\b{re.escape(var)}\b\s*=\s*\"', src):
        continue
    # Skip if variable is used as a set (var = {}, var \cup, \in var, var \subseteq)
    if re.search(rf'\b{re.escape(var)}\b\s*=\s*\{{', src):
        continue
    if re.search(rf'\b{re.escape(var)}\s*\\\\cup\b', src):
        continue
    if re.search(rf'\\\\in\s+{re.escape(var)}\b', src):
        continue
    if re.search(rf'\b{re.escape(var)}\s*\\\\subseteq\b', src):
        continue
    # Skip if variable is never in arithmetic context
    if not re.search(rf'\b{re.escape(var)}\b\s*[\+\-\*]|\b{re.escape(var)}\b\s*>=|\b{re.escape(var)}\b\s*<=|\b{re.escape(var)}\b\s*>|\b{re.escape(var)}\b\s*<|\b{re.escape(var)}\b\s*\\\\in\s+Nat\b|{re.escape(var)}\s*\x27\s*=\s*\S+\s*[\+\-]', src):
        continue
    conjuncts.append(f'    /\\\\ {var} >= {int_min} /\\\\ {var} <= {int_max}')

print('\n'.join(conjuncts))
" 2>/dev/null)"

        if [[ -n "$bound_conjuncts" ]]; then
            cat > "$wrapper_file" <<WRAPEOF
---- MODULE ${wrapper_module} ----
\* Auto-generated TLC wrapper for DPOR case ${case_id}.
\* Adds a Bound constraint matching DPOR config: int ${int_min}..${int_max}

EXTENDS ${module_name}

Bound ==
${bound_conjuncts}
====
WRAPEOF
            constraint_line="CONSTRAINT Bound"
            # TLC will run the wrapper module instead of the original
            module_name="$wrapper_module"
        else
            # No constrainable variables found — run original directly
            wrapper_file=""
        fi
    fi

    # ---- Generate temporary .cfg file ----
    cfg_file="$(mktemp /tmp/tlc_cfg_${case_id}_XXXXXX.cfg)"

    {
        echo "INIT Init"
        echo "NEXT Next"
        echo ""
        if [[ -n "$constants_block" ]]; then
            echo "$constants_block"
            echo ""
        fi
        if [[ -n "$invariants_block" ]]; then
            echo "$invariants_block"
            echo ""
        fi
        if [[ -n "$constraint_line" ]]; then
            echo "$constraint_line"
            echo ""
        fi
    } > "$cfg_file"

    # ---- Build TLC command ----
    tlc_args=()
    tlc_args+=(-cp "$TLA2TOOLS" tlc2.TLC)
    tlc_args+=(-workers "$WORKERS")
    tlc_args+=(-config "$cfg_file")

    # TLC's -deadlock flag DISABLES deadlock checking.
    # When check_deadlock is true (we want deadlock detection): do NOT pass -deadlock
    # When check_deadlock is false (we don't want deadlock detection): pass -deadlock
    if [[ "$check_deadlock" != "true" && "$requires_deadlock_check" != "true" ]]; then
        tlc_args+=(-deadlock)
    fi

    tlc_args+=("$module_name")

    # ---- Run TLC ----
    tlc_stdout="$(mktemp /tmp/tlc_out_${case_id}_XXXXXX.txt)"
    start_epoch=$(date +%s)

    # Run from the case directory so TLC resolves module references
    (
        cd "$case_dir"
        timeout "${TIMEOUT_SEC}s" "$JAVA" -XX:+UseParallelGC -Xmx2g "${tlc_args[@]}"
    ) > "$tlc_stdout" 2>&1
    tlc_exit=$?

    end_epoch=$(date +%s)
    elapsed_s=$((end_epoch - start_epoch))

    # ---- Parse TLC output ----
    tlc_result="unknown"
    tlc_states=0
    tlc_distinct_states=0
    tlc_error_detail=""
    timed_out="false"

    if [[ $tlc_exit -eq 124 ]]; then
        tlc_result="timeout"
        timed_out="true"
    fi

    # Read output
    tlc_output="$(cat "$tlc_stdout" 2>/dev/null || true)"

    # Check for successful completion
    if echo "$tlc_output" | grep -qE "Model checking completed\. No error (found|has been found)\."; then
        tlc_result="ok"
    fi

    # Check for invariant violation
    if echo "$tlc_output" | grep -qE "Invariant .* is violated"; then
        tlc_result="invariant_violated"
        tlc_error_detail="$(echo "$tlc_output" | grep -oE "Invariant [^ ]+ is violated" | head -1)"
    fi

    # Check for deadlock
    if echo "$tlc_output" | grep -q "Deadlock reached."; then
        tlc_result="deadlock_detected"
    fi

    # Check for TLC errors (e.g., parse errors, constant issues)
    if echo "$tlc_output" | grep -qE "^Error:|TLC threw an unexpected exception|Semantic error|Unknown operator"; then
        if [[ "$tlc_result" == "unknown" ]]; then
            tlc_result="tlc_error"
            tlc_error_detail="$(echo "$tlc_output" | grep -E "^Error:|TLC threw|Semantic error|Unknown operator" | head -3 | tr '\n' '; ')"
        fi
    fi

    # Parse state counts
    # TLC prints: "N states generated, M distinct states found"
    state_line="$(echo "$tlc_output" | grep -oE '[0-9]+ states generated, [0-9]+ distinct states found' | tail -1)"
    if [[ -n "$state_line" ]]; then
        tlc_states="$(echo "$state_line" | grep -oE '^[0-9]+')"
        tlc_distinct_states="$(echo "$state_line" | grep -oE '[0-9]+ distinct' | grep -oE '[0-9]+')"
    fi

    # If still unknown after timeout, mark as timeout
    if [[ "$tlc_result" == "unknown" && "$timed_out" == "true" ]]; then
        tlc_result="timeout"
    fi

    # If still unknown, check exit code
    if [[ "$tlc_result" == "unknown" ]]; then
        if [[ $tlc_exit -ne 0 ]]; then
            tlc_result="tlc_error"
            tlc_error_detail="exit_code=$tlc_exit"
        fi
    fi

    # ---- Determine pass/fail ----
    verdict="UNKNOWN"
    if [[ "$tlc_result" == "timeout" ]]; then
        verdict="TIMEOUT"
        TIMEOUT_COUNT=$((TIMEOUT_COUNT + 1))
    elif [[ "$tlc_result" == "tlc_error" ]]; then
        verdict="ERROR"
        ERRORS=$((ERRORS + 1))
    elif [[ "$expected_result" == "ok" && "$tlc_result" == "ok" ]]; then
        verdict="PASS"
        PASS=$((PASS + 1))
    elif [[ "$expected_result" == "invariant_violation" && "$tlc_result" == "invariant_violated" ]]; then
        verdict="PASS"
        PASS=$((PASS + 1))
    elif [[ "$expected_result" == "deadlock" && "$tlc_result" == "deadlock_detected" ]]; then
        verdict="PASS"
        PASS=$((PASS + 1))
    else
        verdict="FAIL"
        FAIL=$((FAIL + 1))
    fi

    echo "$verdict (tlc=$tlc_result, expected=$expected_result, states=$tlc_distinct_states, ${elapsed_s}s)"

    # ---- Build JSON entry ----
    # Escape error detail for JSON
    safe_error="$(echo "$tlc_error_detail" | sed 's/"/\\"/g' | tr '\n' ' ' | head -c 200)"

    result_json="{\"case_id\": \"$case_id\", \"tlc_result\": \"$tlc_result\", \"verdict\": \"$verdict\", \"states_generated\": $tlc_states, \"distinct_states\": $tlc_distinct_states, \"elapsed_s\": $elapsed_s, \"timed_out\": $timed_out, \"expected\": \"$expected_result\", \"error\": \"$safe_error\"}"

    [[ "$TOTAL" -gt 1 ]] && RESULTS_JSON="$RESULTS_JSON,"
    RESULTS_JSON="$RESULTS_JSON
  $result_json"

    # Clean up temp files
    rm -f "$cfg_file" "$tlc_stdout"
    [[ -n "$wrapper_file" && -f "$wrapper_file" ]] && rm -f "$wrapper_file"
done

RESULTS_JSON="$RESULTS_JSON
]"

# ---- Write JSON report ----
cat > "$REPORTS_DIR/tlc_results.json" <<JSONEOF
{
  "timestamp": "$TIMESTAMP",
  "engine": "tlc",
  "timeout_sec": $TIMEOUT_SEC,
  "workers": $WORKERS,
  "total": $TOTAL,
  "pass": $PASS,
  "fail": $FAIL,
  "errors": $ERRORS,
  "timeouts": $TIMEOUT_COUNT,
  "tlc_incompatible": $INCOMPATIBLE,
  "skipped": $SKIPPED,
  "cases": $RESULTS_JSON
}
JSONEOF

echo ""
echo "========================================"
echo "TLC Suite Summary ($TIMESTAMP)"
echo "========================================"
echo "  Total cases:          $TOTAL"
echo "  Pass:                 $PASS"
echo "  Fail:                 $FAIL"
echo "  Errors:               $ERRORS"
echo "  Timeouts:             $TIMEOUT_COUNT"
echo "  TLC incompatible:     $INCOMPATIBLE"
echo "  Skipped:              $SKIPPED"
echo "========================================"
echo "Results written to: tests/reports/tlc_results.json"
echo ""
echo "NOTE: 'TLC incompatible' cases (14, 15, 16, 19) use parameterized"
echo "      Init(s,c)/Next(s,s_,c) which TLC cannot directly model-check."
