# Benchmark Evidence Manifest

Generated: 2026-03-08
Git rev: a7f5ea5

## Machine & Tool Versions

- Platform: Linux 5.15.0-133-generic (x86_64)
- Transpiler: `transpiler/target/debug/verus-transpile` (debug build)
- TLC: **not yet available** (requires Java 11+; system has Java 1.8)
- Python: 3.x (for result extraction)

## Source-first Benchmark Artifacts

### TwoPhase
- Config: `transpiler/tests/model_check_fixtures/benchmarks_1h/twophase_benchmark.model.toml`
- JSON report: `reports/benchmarks/source_first/twophase_benchmark.json`
- Command: `verus-transpile model-check --input src/protocol/TwoPhase/twophase.rs --types src/protocol/TwoPhase/types.rs --model transpiler/tests/model_check_fixtures/benchmarks_1h/twophase_benchmark.model.toml --search bfs --json-report`
- Result: **ok** (FrontierExhausted) — 8 states, 3 depth, 24 transitions, 79s
- Invariants checked (3/3 pass): `LSafetyNoCommitAbortOverlap`, `LSafetyCommittedSubsetPrepared`, `LSafetyTmCommittedRequiresAllPrepared`

### PrimaryBackup
- Config: `transpiler/tests/model_check_fixtures/benchmarks_1h/primarybackup_benchmark.model.toml`
- JSON report: `reports/benchmarks/source_first/primarybackup_benchmark.json`
- Command: `verus-transpile model-check --input src/protocol/PrimaryBackup/primarybackup.rs --types src/protocol/PrimaryBackup/types.rs --model transpiler/tests/model_check_fixtures/benchmarks_1h/primarybackup_benchmark.model.toml --search bfs --json-report`
- Result: **ok** (FrontierExhausted) — 60 states, 7 depth, 169 transitions, 190s
- Invariants checked (3/3 pass): `LSafetyNoPendingImpliesClearedValue`, `LSafetyUnackedImpliesPending`, `LSafetyInactiveStateIsQuiescent`

### LeaderElection
- Config: `transpiler/tests/model_check_fixtures/benchmarks_1h/leaderelection_benchmark.model.toml`
- JSON report: **not generated** (BLOCKED — candidate enumeration cannot find valid transitions with 3-node model)
- Status: Source-first engine needs constraint-aware successor computation before this protocol can produce meaningful long-run benchmarks.

### Paxos
- Config: `transpiler/tests/model_check_fixtures/benchmarks_1h/paxos_benchmark.model.toml`
- JSON report: **not generated** (BLOCKED — same enumeration scalability issue as LeaderElection)
- Status: Same as LeaderElection.

## TLC Benchmark Artifacts

**Pending**: Requires Java 11+ to run TLC. System currently has Java 1.8.

### Expected artifacts (per protocol):
- TLA+ module: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/*_Benchmark_MC.tla`
- Config: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/*_Benchmark_MC.cfg`
- TLC log: `reports/benchmarks/tlc/*_benchmark.log`
- Command: `timeout 3600 java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -workers auto -config *_Benchmark_MC.cfg *_Benchmark_MC.tla`

## Replay Scripts

- Source-first: `scripts/run_model_check_benchmarks.sh`
- TLC: `scripts/run_tlc_benchmarks.sh`
- Comparison: `scripts/compare_tlc_vs_source_first.sh`
