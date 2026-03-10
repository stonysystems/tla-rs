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

## tla-rs Local Artifact Anchor Rule
For substantive `tla-rs` architecture/mechanism claims:
- each claim must point to a local repo artifact (`docs/`, `transpiler/`, `scripts/`, `reports/`, or another checked-in path), not memory;
- acceptable anchor forms are concrete doc paths, source files, tests, scripts, reports, and function/module anchors inside those files;
- web links are not sufficient for `tla-rs` mechanism claims because this phase requires repo-grounded evidence.

Current `tlars_source_first` compliance:
- `R1`-`R3`: local docs (`docs/...`) for status/workflow claims.
- `R4`-`R6`: local model-checker implementation files (`transpiler/src/...`) with function/module anchors.
- `R7`: local claim-to-anchor map (`docs/model-checker-architecture/artifacts/code-anchor-map.md`).

## Claim Confidence Labels
Cross-engine claims are labeled as:
- `directly evidenced`
- `inference from sources`
- `uncertain / not confirmed`

## Cross-Engine Claim Confidence Register
| Claim ID | Claim statement | Confidence label | Evidence source IDs | Notes |
| --- | --- | --- | --- | --- |
| X1 | On current checked-in benchmark models, TLC fully exhausts all 4 compared protocols while source-first fully exhausts TwoPhase and PrimaryBackup and is currently blocked on LeaderElection and Paxos. | directly evidenced | `C1` | Directly reported in the benchmark comparison artifact. |
| X2 | Current evidence suggests successor-solving/candidate-enumeration overhead is the dominant source-first bottleneck on the blocked shared models. | inference from sources | `C1`, `R6` | Inference from benchmark blocker text plus model-checker implementation structure. |
| X3 | No equivalent mechanism was found in the reviewed TLC sources for every tla-rs reduction/telemetry surface currently discussed in this phase. | uncertain / not confirmed | `T3`, `T4`, `T5`, `C2`, `C4` | Absence-style comparison; treated as uncertain until exhaustively confirmed. |
| X4 | Cross-engine state-count comparisons require provenance-aware interpretation because wrapper/modeling artifacts can affect state semantics. | directly evidenced | `C1`, `R7` | Comparison artifact and claim-anchor map both call out provenance requirements. |
| X5 | Source-first optimization deltas in this repo are grounded in checked-in artifacts/scripts rather than narrative-only claims. | directly evidenced | `C2`, `C3`, `C4`, `C5` | Reproducible via checked-in telemetry delta artifacts and test guards. |
| X6 | Any broad statement about feature parity between TLC and tla-rs remains provisional unless backed by direct TLC-source inspection for that specific mechanism. | inference from sources | `T4`, `T5`, `R7` | Methodology inference from source-discipline and anchor requirements. |

## TLC Absence-Claim Wording Rule
For claims about TLC not having an equivalent mechanism:
- do not use strong wording like `TLC does not use X` unless reviewed TLC sources directly support that negative claim;
- if evidence is incomplete, use the weaker form `No equivalent mechanism was found in the reviewed TLC sources`;
- always include the exact reviewed source IDs alongside that weaker claim (for this phase, typically `T3`, `T4`, `T5`).

Current status:
- this document uses the weaker form in `X3` and records explicit reviewed source IDs (`T3`, `T4`, `T5`, with comparison context sources).
