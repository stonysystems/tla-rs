# Source-first Benchmark Results

Generated: 2026-03-11 01:42:57 UTC
Git rev: 875a221
Build profile: debug
Transpiler binary: /home/shuai/workspace/tla-rs/transpiler/target/debug/verus-transpile
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
| twophase | ok(FrontierExhausted) | 8 | 8 | 3 | 21 |
| primarybackup | ok(FrontierExhausted) | 60 | 60 | 7 | 40 |
| leaderelection | timeout_reached(TimeoutReached) | 116 | 116 | 2 | 242 |
| paxos | timeout_reached(TimeoutReached) | 2 | 2 | 1 | 308 |

Benchmark configs: `transpiler/tests/model_check_fixtures/benchmarks_1h/`
Run context metadata: `reports/benchmarks/source_first/metadata/run_context.json`
Per-run metadata: `reports/benchmarks/source_first/metadata/*_benchmark.meta.json`
