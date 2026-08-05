# Model-Check Optimization Telemetry Comparison

| Optimization | Artifact | Metric | Before | After | Delta | Reachable-state guard |
| --- | --- | --- | --- | --- | --- | --- |
| 33.4.2.a successor memoization | `reports/model_check/liveness_avoidable_cycle_violated.json` | `successor_cache_hits` | `0` | `3` | `+3` | `3/5 -> 3/5` |
| 33.4.2.a successor memoization | `reports/model_check/liveness_avoidable_cycle_violated.json` | `successor_cache_misses` | `0` | `3` | `+3` | `3/5 -> 3/5` |
| 33.4.2.b guard-pruned fallback enumeration | `reports/model_check/guard_pruned_enumeration.json` | `enumeration_candidate_evaluations` | `2` | `0` | `-2` | `1/0 -> 1/0` |
| 33.4.2.b guard-pruned fallback enumeration | `reports/model_check/guard_pruned_enumeration.json` | `guard_pruned_candidate_evaluations` | `0` | `2` | `+2` | `1/0 -> 1/0` |

## Exact-Mode Reachable-State Guard Policy

| Artifact | Baseline guard | Observed guard | Policy status |
| --- | --- | --- | --- |
| `reports/model_check/paxos_small.json` | `1/2` | `1/2` | ok |
| `reports/model_check/primarybackup_small.json` | `2/2` | `2/2` | ok |
| `reports/model_check/twophase_small.json` | `3/4` | `3/4` | ok |
| `reports/model_check/leaderelection_small.json` | `4/3` | `4/3` | ok |
| `reports/model_check/liveness_avoidable_cycle_violated.json` | `3/5` | `3/5` | ok |
| `reports/model_check/guard_pruned_enumeration.json` | `1/0` | `1/0` | ok |
