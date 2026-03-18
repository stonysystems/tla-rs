# Source-First Parity Exports (Phase 36.1.3, updated 36.3.6)

Canonical state exports from the source-first model checker for
cross-engine parity comparison. See `docs/cross-engine-state-normalization.md`
for the normalization schema.

## Export status (post Phase 36.3.4 optimization)

| Protocol | States | Status | Checked in | Config |
|----------|--------|--------|------------|--------|
| TwoPhase | 37 | Invariant violated at depth 3 | Yes (13K) | `benchmarks_1h/twophase_benchmark.model.toml` |
| PrimaryBackup | 37,213 | Timeout (120s) | No (17MB) | `benchmarks_1h/primarybackup_benchmark.model.toml` |
| LeaderElection | 31 | Timeout (120s) | Yes (13K) | `benchmarks_1h/leaderelection_benchmark.model.toml` |
| Paxos | 16,655 | Timeout (120s) | No (8.7MB) | `benchmarks_1h/paxos_benchmark.model.toml` |

Large exports (PB, Paxos) are not checked in. Regenerate with the command below.

## Parity vs TLC (post Phase 36.3.4)

| Protocol | SF states | TLC projected | Shared | SF-only | TLC-only |
|----------|-----------|--------------|--------|---------|----------|
| TwoPhase | 37 | 56 | 23 | 14 | 33 |
| PrimaryBackup | 37,213 | 42 | 27 | 37,186 | 15 |
| LeaderElection | 31 | 913 | 31 | 0 | 882 |
| Paxos | 16,655 | N/A | N/A | N/A | N/A |

## Regeneration

```bash
cargo run --manifest-path transpiler/Cargo.toml --release --bin verus-transpile -- \
  model-check \
  --input src/protocol/<Protocol>/<spec>.rs \
  --types src/protocol/<Protocol>/types.rs \
  --model transpiler/tests/model_check_fixtures/benchmarks_1h/<config>.model.toml \
  --timeout 120000 \
  --export-parity reports/model_check/parity/source_first/<protocol>
```
