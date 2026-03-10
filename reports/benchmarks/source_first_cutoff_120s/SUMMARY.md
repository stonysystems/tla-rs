# Source-first Benchmark Results

Generated: 2026-03-10 22:14:23 UTC
Git rev: c202e3b

| Protocol | Result | States | Distinct | Depth | Wall time (s) |
|----------|--------|--------|----------|-------|---------------|
| twophase | ok(FrontierExhausted) | 8 | 8 | 3 | 74 |
| primarybackup | timeout_reached(TimeoutReached) | 52 | 52 | 5 | 120 |
| leaderelection | timeout_reached(TimeoutReached) | 1 | 1 | 0 | 120 |
| paxos | timeout_reached(TimeoutReached) | 1 | 1 | 0 | 182 |

Benchmark configs: `transpiler/tests/model_check_fixtures/benchmarks_1h/`
