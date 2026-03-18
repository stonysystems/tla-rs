# TLC Parity Exports (Phase 36.1.4)

Canonical state exports from TLC for cross-engine parity comparison.
See `docs/cross-engine-state-normalization.md` for the normalization schema.

## Export status

| Protocol | States (projected) | TLC raw distinct | Status | Config |
|----------|-------------------|-----------------|--------|--------|
| TwoPhase | 56 | 64 | Exhausted | `benchmarks_1h/TwoPhase_Benchmark_MC` |
| PrimaryBackup | 54 | 54 | Exhausted | `benchmarks_1h/PrimaryBackup_Benchmark_MC` |
| LeaderElection | 913 | 9,337 | Exhausted | `benchmarks_1h/LeaderElection_Benchmark_MC` |
| Paxos | — | 3,005,604 | Not exported (too large) | `benchmarks_1h/Paxos_Benchmark_MC` |

The "States (projected)" column shows the number of distinct protocol
states after projecting out `msgs` and `constants`. This is the count
that should be compared against source-first exports.

## Regeneration

```bash
TLA2TOOLS=/path/to/tla2tools.jar ./scripts/run_tlc_parity_export.sh
```

## Pipeline

1. `scripts/run_tlc_parity_export.sh` runs TLC with `-dump` flag
2. `scripts/tlc_dump_to_parity_jsonl.py` parses TLC dump format, extracts
   `state` variable, normalizes enum tags, and produces canonical JSONL
