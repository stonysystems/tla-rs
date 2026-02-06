#!/bin/bash
# Validate all generated TLA+ specs with SANY (TLA+ Syntax Analyzer)
#
# Prerequisites:
#   - Java runtime (JDK or JRE)
#   - tla2tools.jar (download from https://github.com/tlaplus/tlaplus/releases)
#
# Usage:
#   ./scripts/validate_tla_specs.sh                           # Validate all specs
#   ./scripts/validate_tla_specs.sh RSL                       # Validate RSL only
#   TLA2TOOLS=/path/to/tla2tools.jar ./scripts/validate_tla_specs.sh  # Custom jar path

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TLA_DIR="$PROJECT_ROOT/src/tla+"

# Find tla2tools.jar
TLA2TOOLS="${TLA2TOOLS:-}"
if [ -z "$TLA2TOOLS" ]; then
    # Try common locations
    for candidate in \
        "$HOME/tools/tla2tools.jar" \
        "$PROJECT_ROOT/tools/tla2tools.jar" \
        "/usr/share/java/tla2tools.jar"; do
        if [ -f "$candidate" ]; then
            TLA2TOOLS="$candidate"
            break
        fi
    done
fi

if [ -z "$TLA2TOOLS" ] || [ ! -f "$TLA2TOOLS" ]; then
    echo "Error: tla2tools.jar not found."
    echo "Set TLA2TOOLS environment variable or place it in ~/tools/tla2tools.jar"
    echo "Download from: https://github.com/tlaplus/tlaplus/releases"
    exit 1
fi

# Check Java
if ! command -v java &>/dev/null; then
    echo "Error: Java not found. Install JDK or JRE."
    exit 1
fi

# Determine which protocols to validate
PROTOCOL="${1:-}"
if [ -n "$PROTOCOL" ]; then
    if [ ! -d "$TLA_DIR/$PROTOCOL" ]; then
        echo "Error: Protocol directory not found: $TLA_DIR/$PROTOCOL"
        exit 1
    fi
    DIRS="$TLA_DIR/$PROTOCOL"
else
    DIRS="$TLA_DIR"
fi

# Validate
total=0
passed=0
failed=0
failed_files=""

for f in $(find "$DIRS" -name "*.tla" | sort); do
    total=$((total + 1))
    relpath="${f#$PROJECT_ROOT/}"

    output=$(java -cp "$TLA2TOOLS" tla2sany.SANY "$f" 2>&1)
    if echo "$output" | grep -q "Semantic processing of module"; then
        echo "  PASS: $relpath"
        passed=$((passed + 1))
    else
        echo "  FAIL: $relpath"
        echo "$output" | sed 's/^/    /'
        failed=$((failed + 1))
        failed_files="$failed_files $relpath"
    fi
done

echo ""
echo "SANY Validation: $passed/$total passed, $failed failed"

if [ $failed -gt 0 ]; then
    echo "Failed files:$failed_files"
    exit 1
fi
