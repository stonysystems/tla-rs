# Sources and Evidence Log

## Purpose
Track the exact sources reviewed for:
- traditional TLA+ / TLC architecture claims,
- tla-rs source-first architecture claims,
- and cross-engine comparison/optimization claims.

## Source Recording Schema
Each source entry records:
- `source kind` (`official docs`, `book`, `source code`, `repo doc`, `benchmark artifact`, `test`, `secondary background`),
- `date checked`,
- `inspected depth`,
- and `supports claims`.

## Source Ledger
| ID | Track | Source | Source kind | Date checked | Inspected depth | Supports claims |
| --- | --- | --- | --- | --- | --- | --- |
| T1 | `traditional_tla_tlc` | Leslie Lamport, *Specifying Systems* (`book-01-11-10.pdf`, Lamport site) | book | 2026-03-10 | doc deep read (selected model-checking chapters/sections) | Baseline TLA+ semantics and what a model/config means in TLC-style workflows. |
| T2 | `traditional_tla_tlc` | Yu, Manolios, Lamport, *Model Checking TLA+ Specifications* (`yuanyu-model-checking.pdf`) | secondary background | 2026-03-10 | doc deep read | Supplemental TLC architecture framing: explicit-state approach, finite-state model assumptions, and "How TLC Works". |
| T3 | `traditional_tla_tlc` | `https://github.com/tlaplus/tlaplus` README (`java -cp ... tla2sany.SANY`, `tlc2.TLC`) | official docs | 2026-03-10 | doc deep read | Toolchain role split (SANY parser/analyzer vs TLC model checker CLI entrypoints). |
| T4 | `traditional_tla_tlc` | `https://github.com/tlaplus/tlaplus/tree/master/tlatools/org.lamport.tlatools/src/tlc2` | source code | 2026-03-10 | source read (directory-level + entry files) | Implementation anchor for TLC-side architecture claims and terminology checks. |
| T5 | `traditional_tla_tlc` | `https://github.com/tlaplus/tlaplus/tree/master/tlatools/org.lamport.tlatools/src/tla2sany` | source code | 2026-03-10 | source skim | Implementation anchor for SANY-side front-end parsing/analyzer claims. |
| T6 | `traditional_tla_tlc` | `https://lamport.azurewebsites.net/tla/toolbox.html` | official docs | 2026-03-10 | doc skim | Toolbox operational role and TLC usage context in traditional TLA+ workflows. |
| R1 | `tlars_source_first` | `docs/model_checker_status.md` | repo doc | 2026-03-10 | doc deep read | Canonical capability/blocker/evidence status for source-first model checking in this repo. |
| R2 | `tlars_source_first` | `docs/model-checking-source-first.md` | repo doc | 2026-03-10 | doc deep read | User-facing source-first execution path, config knobs, and known limits. |
| R3 | `tlars_source_first` | `docs/conversion-testing-guide.md` | repo doc | 2026-03-10 | doc skim | Where source-first model-checking sits within the repo's conversion/testing workflow. |
| R4 | `tlars_source_first` | `transpiler/src/main.rs` (`Commands::ModelCheck`, `execute_model_check`, `classify_search_evidence_mode`) | source code | 2026-03-10 | source read | CLI orchestration, model-check execution pipeline, and evidence-mode labeling. |
| R5 | `tlars_source_first` | `transpiler/src/modelcheck/config.rs` | source code | 2026-03-10 | source read | Model config parsing/validation/override semantics. |
| R6 | `tlars_source_first` | `transpiler/src/modelcheck/{init,ir,evaluator,domain,solver,explorer,graph,liveness,invariant,por}.rs` | source code | 2026-03-10 | source read | Stage-by-stage architecture anchors for init/IR/eval/domain/solve/search/liveness/reduction claims. |
| R7 | `tlars_source_first` | `docs/model-checker-architecture/artifacts/code-anchor-map.md` | repo doc | 2026-03-10 | doc deep read | Claim-to-anchor index used by Phase 35 architecture/tutorial docs. |
| C1 | `comparison_optimization` | `reports/benchmarks/TLC_VS_SOURCE_FIRST_BENCHMARK_COMPARISON.md` | benchmark artifact | 2026-03-10 | artifact inspection | Checked-in TLC vs source-first benchmark outcomes and stated blockers. |
| C2 | `comparison_optimization` | `reports/model_check/OPTIMIZATION_DELTAS.md` | benchmark artifact | 2026-03-10 | artifact inspection | Before/after optimization deltas for source-first telemetry metrics. |
| C3 | `comparison_optimization` | `scripts/run_model_check_matrix.sh` | source code | 2026-03-10 | source read | Artifact regeneration workflow for supported source-first matrix evidence. |
| C4 | `comparison_optimization` | `scripts/compare_model_check_telemetry.sh` | source code | 2026-03-10 | source read | Automated delta computation and exact-mode guard checks for telemetry claims. |
| C5 | `comparison_optimization` | `transpiler/tests/integration.rs` (model-check evidence guards) | test | 2026-03-10 | source read | Test-enforced evidence discipline for status docs/artifacts/row-order contracts. |

## Coverage by Track
- `traditional_tla_tlc`: T1-T6
- `tlars_source_first`: R1-R7
- `comparison_optimization`: C1-C5

## Traditional TLC Primary-Source Preference
Traditional TLA+/TLC claims follow this precedence:
1. official docs and canonical book material;
2. TLC/SANY source code when a claim depends on implementation details;
3. secondary background only as supplemental context, never as sole evidence.

| Traditional claim area | Primary source IDs | Secondary/supporting IDs | Notes |
| --- | --- | --- | --- |
| TLA+ semantics, spec meaning, and model/config interpretation | `T1`, `T3` | `T2` | `T1`/`T3` are the primary basis; `T2` is only cross-check context. |
| Toolchain role split (`SANY` front-end vs `TLC` model checker) | `T3`, `T5`, `T6` | `T2` | Prefer official docs and implementation anchors; keep paper framing supplemental. |
| TLC implementation-dependent behavior and architecture wording | `T4`, `T5` | `T2` | Claims that depend on internals must anchor to TLC/SANY source tree. |
| Explicit-state/finiteness framing in this tutorial | `T1`, `T3`, `T4` | `T2` | Use canonical/official text first, with `T2` as background only. |

## TLC Internals Evidence Exclusions
For TLC internals/implementation claims:
- blogs and random discussion threads are not accepted as primary evidence when official/canonical sources exist;
- any non-canonical source can only be supplemental background and must not be the main support for internals wording;
- primary support must remain anchored to official docs, canonical book material, or TLC/SANY source code.

Current ledger status:
- no `traditional_tla_tlc` entry uses blog/discussion-thread sources as primary internals evidence;
- internals wording is anchored to `T4`/`T5` and backed by canonical sources in the primary-source table above.

## Claim Confidence Labels
Cross-engine claims are labeled as:
- `directly evidenced`
- `inference from sources`
- `uncertain`
