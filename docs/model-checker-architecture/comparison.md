# Architecture Comparison: Traditional TLC vs tla-rs Source-First

## Comparison Method
This document compares the reviewed traditional TLC path and the current tla-rs source-first implementation.
Baseline discipline for Phase 35.8.6: this is a comparison against the inspected traditional model-checking path (primarily TLC), not against an idealized notion of the TLA+ language.
If another tool is mentioned, it is labeled as side context and kept separate from the TLC-baseline comparison rows.
For Phase 35.1.5, this file intentionally uses the same table schema and concern-row order as
`artifacts/engine-crosswalk.csv` so the two artifacts can be kept in lockstep.

## Side-by-Side Matrix
Minimum required columns for Phase 35.6.1 are present (`Concern`, `Traditional TLA+ / TLC`, `tla-rs source-first`, `Same / Similar / Different`, `Why this difference matters`). This matrix also keeps `Evidence status` and `Notes` so it stays synchronized with `artifacts/engine-crosswalk.csv`.
Phase 35.6.2 required comparison concerns are present as explicit row keys (`input_representation` through `extension_points`) so required coverage does not depend on prose interpretation.

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
Major differences and their consequences are explicit below. Consequence tags are restricted to
`performance`, `feature coverage`, `trust/exactness`, `usability`, and `implementation complexity`.

| Major Difference | Consequence Type(s) | Why This Consequence Matters | Supporting Anchors |
| --- | --- | --- | --- |
| Traditional flow starts from TLA+ module + TLC model/config, while current tla-rs flow starts from Rust/Verus spec sources + `model.toml`. | `usability`, `implementation complexity` | Users and contributors must learn different artifact surfaces and debugging entry points; implementation work is split across parser/model-checker codepaths instead of one checker front-end stack. | `docs/model-checker-architecture/traditional-tla-model-checking.md` (`Beginner Toolchain Primer`, `End-to-End TLC Path (Ordered)`); `docs/model-checker-architecture/tlars-source-first-model-checking.md` (steps `1-3`) |
| Front-end validation anchors differ (`SANY` in traditional flow vs source-first parser/entrypoint/config validation in tla-rs). | `feature coverage`, `implementation complexity` | Validation responsibilities land in different code modules and maturity levels, which affects what malformed or edge-case inputs are caught early and where that behavior is maintained. | `docs/model-checker-architecture/traditional-tla-model-checking.md` (step `2`); `docs/model-checker-architecture/tlars-source-first-model-checking.md` (steps `1-4`); `transpiler/src/main.rs` (`run_model_check_command`) |
| Source-first successor construction has a direct-solver path and a predicate-enumeration fallback with telemetry, while benchmark evidence calls out blocked protocols where this cost dominates. | `performance`, `feature coverage` | Fallback-heavy branches can inflate runtime/exploration cost and currently block full coverage on shared benchmark models that TLC exhausts in the checked-in comparison. | `docs/model-checker-architecture/tlars-source-first-model-checking.md` (`Current Technique Path (Plain Language)` item `3`, `Main Known Limits` item `3`); `reports/benchmarks/TLC_VS_SOURCE_FIRST_BENCHMARK_COMPARISON.md` |
| Source-first explicitly exposes exact bounded mode vs intentionally lossy accelerations (hash compaction/symmetry) and labels evidence mode in reports. | `trust/exactness`, `usability` | Readers can distinguish proof-strength bounded evidence from faster bug-finding runs, reducing accidental over-interpretation of lossy runs while preserving practical tuning knobs. | `docs/model-checker-architecture/tlars-source-first-model-checking.md` (`Current Technique Path (Plain Language)` item `4`, step `10`); `transpiler/src/main.rs` (`classify_search_evidence_mode`) |
| Liveness/fairness handling in source-first is branch-label validated and SCC-based over explored graphs, while traditional TLC framing is fairness-constrained cycle analysis in the TLC execution path. | `feature coverage`, `implementation complexity`, `trust/exactness` | Semantically similar goals (fairness-aware liveness) still depend on engine-specific machinery and validation rules, so claim strength must stay evidence-scoped per engine implementation. | `docs/model-checker-architecture/traditional-tla-model-checking.md` (steps `7-8`); `docs/model-checker-architecture/tlars-source-first-model-checking.md` (steps `9-10`); `docs/model-checker-architecture/sources-and-evidence.md` (`Cross-Engine Claim Confidence Register`) |
| Output surfaces differ: TLC-side evidence in this repo is log/wrapper oriented, while source-first emits JSON + telemetry suitable for automated post-processing. | `usability`, `performance` | Machine-readable outputs lower automation/reporting friction (scripts/comparisons), while log-first outputs are more manual to aggregate in tooling pipelines. | `docs/model-checker-architecture/walkthrough.md` (`What output/report the user gets`, `Parallel Track A`, `Parallel Track B`); `reports/benchmarks/TLC_VS_SOURCE_FIRST_BENCHMARK_COMPARISON.md`; `scripts/compare_model_check_telemetry.sh` |

## Synthesis
The required synthesis questions are answered explicitly below.

| Synthesis Question | Answer | Supporting Anchors |
| --- | --- | --- |
| What is fundamentally the same idea? | Both paths are explicit-state model checking over a finite model instance: derive concrete initial states, repeatedly compute successors from the next-step relation, deduplicate reached states, and check selected safety/liveness properties while exploring. | `docs/model-checker-architecture/traditional-tla-model-checking.md` (`End-to-End TLC Path (Ordered)`); `docs/model-checker-architecture/tlars-source-first-model-checking.md` (`End-to-End Source-First Path (Ordered)`); `docs/model-checker-architecture/walkthrough.md` (`Step-by-Step Trace (Ordered)`) |
| What is an implementation detail difference? | Input and front-end tooling are different: traditional flow is TLA+ module + model/config through SANY/TLC, while tla-rs source-first flow parses local Rust/Verus spec plus `model.toml` in this repo. This changes integration surface and artifact layout, not the high-level model-checking intent. | `docs/model-checker-architecture/traditional-tla-model-checking.md` (`Beginner Toolchain Primer`, `End-to-End TLC Path (Ordered)`); `docs/model-checker-architecture/tlars-source-first-model-checking.md` (steps `1-3`) |
| What is a semantics/algorithm difference? | The current tla-rs engine documents an explicit split between exact bounded search and intentionally lossy accelerations (for example hash compaction and symmetry merging) with evidence-mode labeling; it also drives fairness/liveness checks from validated branch labels. This phase does not claim full algorithmic parity between TLC internals and tla-rs internals, and any stronger cross-engine parity/absence claim remains confidence-labeled in the evidence register. | `docs/model-checker-architecture/tlars-source-first-model-checking.md` (`Current Technique Path (Plain Language)` items `4` and `5`); `docs/model-checker-architecture/sources-and-evidence.md` (`Cross-Engine Claim Confidence Register`, `TLC Absence-Claim Wording Rule`) |
| What is a tooling UX/reporting difference? | TLC-facing outputs in this repo are log/wrapper oriented, while source-first outputs are JSON/telemetry oriented; the checked-in benchmark comparison normalizes both surfaces side by side. This affects operator workflow (manual log reading vs machine-consumable reports) and automation ergonomics. | `docs/model-checker-architecture/walkthrough.md` (`What output/report the user gets`, `Parallel Track A`, `Parallel Track B`); `reports/benchmarks/TLC_VS_SOURCE_FIRST_BENCHMARK_COMPARISON.md`; `docs/model-checker-architecture/tlars-source-first-model-checking.md` (step `10`) |
