#!/usr/bin/env bash
# Fixed protocol implementation/batch parameters; vary only client concurrency.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUTPUT_DIR="${OUTPUT_DIR:-$ROOT/bench/vary_clients/$(date -u +%Y%m%dT%H%M%S%N)}"
CLIENT_COUNTS="${CLIENT_COUNTS:-1 2 4 8 16 32 64}"
PROTOCOLS="${PROTOCOLS:-rsl raft primarybackup pbft epaxos}"
DURATION="${DURATION:-30}"
TRIALS="${TRIALS:-3}"
mkdir -p "$OUTPUT_DIR"
if (( $# > 0 )); then
    printf 'Configure with PROTOCOLS, CLIENT_COUNTS, DURATION, TRIALS, TRANSPORT, USE_SSL, CONFIGS, RUNTIMES, OUTPUT_DIR; no source-mutating build flags are supported.\n' >&2
    exit 1
fi
if [[ "${BUILD:-0}" == 1 ]]; then "$ROOT/scripts/build_lion_runtime.sh"; fi
export BUILD=0
for protocol in $PROTOCOLS; do
    for clients in $CLIENT_COUNTS; do
        PROTOCOL="$protocol" CLIENT_THREADS="$clients" DURATION="$DURATION" TRIALS="$TRIALS" \
            OUTPUT_DIR="$OUTPUT_DIR/$protocol-c$clients" \
            "$ROOT/scripts/bench_rsl_runtime.sh"
    done
done
python3 - "$OUTPUT_DIR" <<'PY'
import csv, pathlib, sys
root = pathlib.Path(sys.argv[1])
with (root / 'results.csv').open('w', newline='') as output:
    writer = csv.writer(output)
    header = None
    for path in sorted(root.glob('*/results.csv')):
        with path.open() as source:
            reader = csv.reader(source)
            current = next(reader)
            if header is None:
                header = current
                writer.writerow(header)
            elif current != header:
                raise SystemExit(f'incompatible CSV header: {path}')
            writer.writerows(reader)
    if header is None:
        raise SystemExit('no benchmark runs selected')
print(f'Concurrency sweep results: {root / "results.csv"}')
PY
