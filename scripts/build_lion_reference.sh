#!/usr/bin/env bash
# Explicit benchmark-only dependency path; never called by native builds.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$ROOT/lion_reference.py" build "$@"
