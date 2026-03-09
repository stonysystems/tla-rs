# TLC Benchmark Results

Generated: 2026-03-08 16:25:00 UTC
Git rev: fd8967f
Java: 17, Workers: 1
TLC version: 2026.03.05.210854 (rev: ec1a488)

| Protocol | Result | States | Distinct | Depth | Wall time (s) |
|----------|--------|--------|----------|-------|---------------|
| twophase | pass | 150 | 64 | 9 | 1 |
| primarybackup | pass | 86 | 54 | 10 | 1 |
| leaderelection | pass | 100636 | 9337 | 13 | 2 |
| paxos | pass | 25288515 | 3005604 | 37 | 375 |

TLC wrappers: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/`
