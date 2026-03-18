# Source-First Parity Exports (Phase 36.1.3)

Canonical state exports from the source-first model checker for
cross-engine parity comparison. See `docs/cross-engine-state-normalization.md`
for the normalization schema.

## Export status

| Protocol | States | Status | Config |
|----------|--------|--------|--------|
| TwoPhase | 8 | Exhausted | `benchmarks_1h/twophase_benchmark.model.toml` |
| PrimaryBackup | 60 | Exhausted | `benchmarks_1h/primarybackup_benchmark.model.toml` |
| LeaderElection | 2 | Partial (timeout) | `benchmarks_1h/leaderelection_benchmark.model.toml` |
| Paxos | — | Not generated (initial-state construction timeout) | `benchmarks_1h/paxos_benchmark.model.toml` |

## Regeneration

```bash
cargo run --manifest-path transpiler/Cargo.toml --bin verus-transpile -- \
  model-check \
  --input src/protocol/<Protocol>/<spec>.rs \
  --types src/protocol/<Protocol>/types.rs \
  --model transpiler/tests/model_check_fixtures/benchmarks_1h/<config>.model.toml \
  --export-parity reports/model_check/parity/source_first/<protocol>
```
