# TLC Benchmark Results

Generated: 2026-03-10 22:25:57 UTC
Git rev: c202e3b
Java: 21, Workers: 1

| Protocol | Result | States | Distinct | Depth | Wall time (s) |
|----------|--------|--------|----------|-------|---------------|
| twophase | pass | 150 | 64 | 9 | 1 |
| primarybackup | pass | 86 | 54 | 10 | 1 |
| leaderelection | pass | 100636 | 9337 | 13 | 2 |
| paxos | timeout | 5312208 | 876750 | ? | 120 |

TLC wrappers: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/`
