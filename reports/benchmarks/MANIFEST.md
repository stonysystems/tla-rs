# Benchmark Evidence Manifest

Generated: 2026-03-10
Git rev: ed986eb

## Scope

This manifest records the Phase `33.4.4.a` fairness hardening replay for the 4 shared benchmark protocols (`TwoPhase`, `PrimaryBackup`, `LeaderElection`, `Paxos`).

- Same finite benchmark models/invariants/search mode were used for debug and release source-first runs.
- Source-first canonical performance view is now **release** (`reports/benchmarks/source_first_release`).
- Debug results are retained for continuity (`reports/benchmarks/source_first`).

## Source-first Run Context (Parity)

Common parity settings for both profiles:
- Search: `bfs`
- Timeout override: `240000 ms`
- Hard timeout wrapper: `360 s`
- Threading mode: `single-thread`
- Worker count: `1`
- Machine: `Linux 6.17.4-2-pve x86_64 GNU/Linux` on host `zoo-005`
- CPU: `AMD Ryzen Threadripper 2990WX 32-Core Processor` (`64` logical cores)

Run-level context files:
- Debug: `reports/benchmarks/source_first/metadata/run_context.json`
- Release: `reports/benchmarks/source_first_release/metadata/run_context.json`

## Source-first Per-Run Records

Each per-run metadata file below records the exact command line (`command` field), build profile, timeout/threading settings, machine info, and outcome summary.

| Protocol | Profile | Result | Stop reason | States | Transitions | Depth | Wall (s) | JSON report | Per-run metadata (exact command) |
|----------|---------|--------|-------------|--------|-------------|-------|----------|-------------|----------------------------------|
| TwoPhase | release (canonical) | `ok(FrontierExhausted)` | `FrontierExhausted` | 8 | 24 | 3 | 17 | `reports/benchmarks/source_first_release/twophase_benchmark.json` | `reports/benchmarks/source_first_release/metadata/twophase_benchmark.meta.json` |
| PrimaryBackup | release (canonical) | `ok(FrontierExhausted)` | `FrontierExhausted` | 60 | 169 | 7 | 50 | `reports/benchmarks/source_first_release/primarybackup_benchmark.json` | `reports/benchmarks/source_first_release/metadata/primarybackup_benchmark.meta.json` |
| LeaderElection | release (canonical) | `timeout_reached(TimeoutReached)` | `TimeoutReached` | 1 | 0 | 0 | 241 | `reports/benchmarks/source_first_release/leaderelection_benchmark.json` | `reports/benchmarks/source_first_release/metadata/leaderelection_benchmark.meta.json` |
| Paxos | release (canonical) | `timeout_reached(TimeoutReached)` | `TimeoutReached` | 4 | 4 | 1 | 269 | `reports/benchmarks/source_first_release/paxos_benchmark.json` | `reports/benchmarks/source_first_release/metadata/paxos_benchmark.meta.json` |
| TwoPhase | debug (continuity) | `ok(FrontierExhausted)` | `FrontierExhausted` | 8 | 24 | 3 | 73 | `reports/benchmarks/source_first/twophase_benchmark.json` | `reports/benchmarks/source_first/metadata/twophase_benchmark.meta.json` |
| PrimaryBackup | debug (continuity) | `ok(FrontierExhausted)` | `FrontierExhausted` | 60 | 169 | 7 | 174 | `reports/benchmarks/source_first/primarybackup_benchmark.json` | `reports/benchmarks/source_first/metadata/primarybackup_benchmark.meta.json` |
| LeaderElection | debug (continuity) | `timeout_reached(TimeoutReached)` | `TimeoutReached` | 1 | 0 | 0 | 241 | `reports/benchmarks/source_first/leaderelection_benchmark.json` | `reports/benchmarks/source_first/metadata/leaderelection_benchmark.meta.json` |
| Paxos | debug (continuity) | `timeout_reached(TimeoutReached)` | `TimeoutReached` | 2 | 1 | 1 | 302 | `reports/benchmarks/source_first/paxos_benchmark.json` | `reports/benchmarks/source_first/metadata/paxos_benchmark.meta.json` |

## TLC Benchmark Artifacts (Comparison Side)

TLC artifacts remain in:
- Logs + summary: `reports/benchmarks/tlc/`
- Wrapper/config inputs: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/`

Most recent checked-in comparison report:
- `reports/benchmarks/TLC_VS_SOURCE_FIRST_BENCHMARK_COMPARISON.md`

## Replay Scripts

- Source-first: `scripts/run_model_check_benchmarks.sh`
- TLC: `TLA2TOOLS=~/tla2tools.jar scripts/run_tlc_benchmarks.sh`
- Comparison: `scripts/compare_tlc_vs_source_first.sh`
