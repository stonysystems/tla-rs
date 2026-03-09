# Benchmark Evidence Manifest

Generated: 2026-03-08
Git rev: fd8967f

## Machine & Tool Versions

- Platform: Linux 6.2.16-3-pve (x86_64), 64 cores
- Transpiler: `transpiler/target/debug/verus-transpile` (debug build)
- TLC: 2026.03.05.210854 (rev: ec1a488), Java 17.0.18 (OpenJDK Debian 17.0.18+8)
- tla2tools.jar: downloaded from GitHub tlaplus/tlaplus releases v1.8.0

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

### TwoPhase
- TLA+ wrapper: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/TwoPhase_Benchmark_MC.tla`
- Config: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/TwoPhase_Benchmark_MC.cfg`
- TLC log: `reports/benchmarks/tlc/twophase_benchmark.log`
- Command: `timeout 3600 java -XX:+UseParallelGC -Xmx4g -cp ~/tla2tools.jar tlc2.TLC -workers 1 -config TwoPhase_Benchmark_MC.cfg TwoPhase_Benchmark_MC.tla`
- Result: **pass** (exhausted) — 150 generated, 64 distinct, depth 9, 1s

### PrimaryBackup
- TLA+ wrapper: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/PrimaryBackup_Benchmark_MC.tla`
- Config: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/PrimaryBackup_Benchmark_MC.cfg`
- TLC log: `reports/benchmarks/tlc/primarybackup_benchmark.log`
- Command: `timeout 3600 java -XX:+UseParallelGC -Xmx4g -cp ~/tla2tools.jar tlc2.TLC -workers 1 -config PrimaryBackup_Benchmark_MC.cfg PrimaryBackup_Benchmark_MC.tla`
- Result: **pass** (exhausted) — 86 generated, 54 distinct, depth 10, 1s

### LeaderElection
- TLA+ wrapper: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/LeaderElection_Benchmark_MC.tla`
- Config: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/LeaderElection_Benchmark_MC.cfg`
- TLC log: `reports/benchmarks/tlc/leaderelection_benchmark.log`
- Command: `timeout 3600 java -XX:+UseParallelGC -Xmx4g -cp ~/tla2tools.jar tlc2.TLC -workers 1 -config LeaderElection_Benchmark_MC.cfg LeaderElection_Benchmark_MC.tla`
- Result: **pass** (exhausted) — 100,636 generated, 9,337 distinct, depth 13, 2s

### Paxos
- TLA+ wrapper: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/Paxos_Benchmark_MC.tla`
- Config: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/Paxos_Benchmark_MC.cfg`
- TLC log: `reports/benchmarks/tlc/paxos_benchmark.log`
- Command: `timeout 600 java -XX:+UseParallelGC -Xmx4g -cp ~/tla2tools.jar tlc2.TLC -workers 1 -config Paxos_Benchmark_MC.cfg Paxos_Benchmark_MC.tla`
- Result: **pass** (exhausted) — 25,288,515 generated, 3,005,604 distinct, depth 37, 375s

## Replay Scripts

- Source-first: `scripts/run_model_check_benchmarks.sh`
- TLC: `TLA2TOOLS=~/tla2tools.jar scripts/run_tlc_benchmarks.sh`
- Comparison: `scripts/compare_tlc_vs_source_first.sh`
