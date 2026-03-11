# Source-first Benchmark Results

Generated: 2026-03-11 02:53:32 UTC
Git rev: d93c9ab
Build profile: release
Transpiler binary: /home/shuai/workspace/tla-rs/transpiler/target/release/verus-transpile
Threading mode: single-thread
Workers: 1
Timeout override (ms): 240000
Hard timeout wrapper (s): 360
Machine: Linux 6.17.4-2-pve x86_64 GNU/Linux
Host: zoo-005
CPU count: 64
CPU model: AMD Ryzen Threadripper 2990WX 32-Core Processor

| Protocol | Result | States | Distinct | Depth | Wall time (s) |
|----------|--------|--------|----------|-------|---------------|
| twophase | ok(FrontierExhausted) | 8 | 8 | 3 | 1 |
| primarybackup | ok(FrontierExhausted) | 60 | 60 | 7 | 2 |
| leaderelection | timeout_reached(TimeoutReached) | 280 | 280 | 3 | 241 |
| paxos | timeout_reached(TimeoutReached) | 75 | 75 | 2 | 274 |

Benchmark configs: `transpiler/tests/model_check_fixtures/benchmarks_1h/`
Run context metadata: `reports/benchmarks/source_first_release/metadata/run_context.json`
Per-run metadata: `reports/benchmarks/source_first_release/metadata/*_benchmark.meta.json`
