# Architecture Comparison: Traditional TLC vs tla-rs Source-First

## Comparison Method
This document compares the reviewed traditional TLC path and the current tla-rs source-first implementation.
For Phase 35.1.5, this file intentionally uses the same table schema and concern-row order as
`artifacts/engine-crosswalk.csv` so the two artifacts can be kept in lockstep.

## Side-by-Side Matrix
| Concern | Traditional TLA+ / TLC | tla-rs source-first | Same / Similar / Different | Why this difference matters | Evidence status | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| `input_representation` | TBD | TBD | TBD | TBD | scaffold_only | Row/schema aligned with `engine-crosswalk.csv`; fill in Phase 35.6. |
| `front_end_validation` | TBD | TBD | TBD | TBD | scaffold_only | Row/schema aligned with `engine-crosswalk.csv`; fill in Phase 35.6. |
| `model_config_role` | TBD | TBD | TBD | TBD | scaffold_only | Row/schema aligned with `engine-crosswalk.csv`; fill in Phase 35.6. |
| `initial_state_generation` | TBD | TBD | TBD | TBD | scaffold_only | Row/schema aligned with `engine-crosswalk.csv`; fill in Phase 35.6. |
| `successor_generation` | TBD | TBD | TBD | TBD | scaffold_only | Row/schema aligned with `engine-crosswalk.csv`; fill in Phase 35.6. |
| `helper_operator_evaluation` | TBD | TBD | TBD | TBD | scaffold_only | Row/schema aligned with `engine-crosswalk.csv`; fill in Phase 35.6. |
| `state_representation` | TBD | TBD | TBD | TBD | scaffold_only | Row/schema aligned with `engine-crosswalk.csv`; fill in Phase 35.6. |
| `state_deduplication` | TBD | TBD | TBD | TBD | scaffold_only | Row/schema aligned with `engine-crosswalk.csv`; fill in Phase 35.6. |
| `invariant_checking` | TBD | TBD | TBD | TBD | scaffold_only | Row/schema aligned with `engine-crosswalk.csv`; fill in Phase 35.6. |
| `deadlock_semantics` | TBD | TBD | TBD | TBD | scaffold_only | Row/schema aligned with `engine-crosswalk.csv`; fill in Phase 35.6. |
| `liveness_fairness_handling` | TBD | TBD | TBD | TBD | scaffold_only | Row/schema aligned with `engine-crosswalk.csv`; fill in Phase 35.6. |
| `counterexample_report_output` | TBD | TBD | TBD | TBD | scaffold_only | Row/schema aligned with `engine-crosswalk.csv`; fill in Phase 35.6. |
| `performance_bottlenecks` | TBD | TBD | TBD | TBD | scaffold_only | Row/schema aligned with `engine-crosswalk.csv`; fill in Phase 35.6. |
| `exactness_vs_lossy_acceleration` | TBD | TBD | TBD | TBD | scaffold_only | Row/schema aligned with `engine-crosswalk.csv`; fill in Phase 35.6. |
| `extension_points` | TBD | TBD | TBD | TBD | scaffold_only | Row/schema aligned with `engine-crosswalk.csv`; fill in Phase 35.6. |

## Similarities
This section will capture shared explicit-state model-checking fundamentals in Phase 35.6.

## Differences and Consequences
This section will classify differences and explain impacts on performance, trust, coverage, and UX in Phase 35.6.

## Synthesis
This section will answer what is fundamentally same vs implementation vs semantic difference in Phase 35.6.
