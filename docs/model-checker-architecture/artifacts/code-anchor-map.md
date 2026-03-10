# Code Anchor Map

## Purpose
Map major tla-rs model-checker architecture claims to concrete local repository anchors that a reader can inspect directly.

## Claim-to-Anchor Map
| Claim ID | Architecture Claim | Primary Local Anchor(s) | Evidence Kind | Notes |
| --- | --- | --- | --- | --- |
| C1 | The model-check command orchestration lives in the CLI entrypoint and drives the source-first pipeline. | `transpiler/src/main.rs` (`Commands::ModelCheck`, `execute_model_check`) | code | Main integration point for config, schema loading, exploration, and reporting. |
| C2 | `model.toml` parsing, validation, and CLI override merge are first-class pipeline stages. | `transpiler/src/modelcheck/config.rs` (`parse_model_config_file`, `apply_model_config_overrides`, `validate_model_config`) | code | Supports the "model/config role" story in the tutorial. |
| C3 | Initial-state construction is computed from `LInit` over bounded candidate states/constants. | `transpiler/src/modelcheck/init.rs` (`construct_initial_states`) | code | Confirms initial-state generation is explicit and executable. |
| C4 | `LNext` is normalized into branch IR with branch constraints and existential extraction. | `transpiler/src/modelcheck/ir.rs` (`build_transition_ir`, `discover_lnext_branches`) | code | Anchor for branch-level solver/explorer discussion. |
| C5 | Expression semantics are implemented by a runtime evaluator over bounded runtime values. | `transpiler/src/modelcheck/evaluator.rs` (`eval_expr`, `eval_quantifier`, `eval_match_expr`) | code | Includes quantifiers, match, and struct-update evaluation paths. |
| C6 | Finite-domain expansion for types and branch existentials is explicit and bounded. | `transpiler/src/modelcheck/domain.rs` (`expand_branch_existentials`, `expand_type_domain`) | code | Anchor for state-explosion and domain-limit discussions. |
| C7 | Successor solving combines direct assignment solving with candidate-enumeration fallback and telemetry. | `transpiler/src/modelcheck/solver.rs` (`solve_branch_successors_with_candidates_and_telemetry`, `solve_transition_successors_with_semantics`) | code | Core anchor for "direct solve vs enumeration fallback" claims. |
| C8 | BFS/DFS exploration, dedup modes, traces, timeout, and stop reasons are implemented in the explorer layer. | `transpiler/src/modelcheck/explorer.rs` (`explore_state_space_with_traces_and_dedup`, `ExplorationStopReason`) | code | Covers search algorithm and stop semantics claims. |
| C9 | Liveness analysis relies on explored-graph indexing and SCC/cycle analysis. | `transpiler/src/modelcheck/graph.rs` (`build_explored_graph_index`, `detect_cyclic_sccs_with_witness`) | code | Structural graph anchor used by liveness checks. |
| C10 | `leads_to` checks and branch-label fairness filtering are implemented in a dedicated liveness module. | `transpiler/src/modelcheck/liveness.rs` (`resolve_leads_to_obligations`, `check_leads_to_violations`) | code | Anchor for fairness/liveness mechanism claims. |
| C11 | Invariant selection and first-violation detection are explicit pipeline stages. | `transpiler/src/modelcheck/invariant.rs` (`resolve_selected_invariants`, `first_invariant_violation`) | code | Anchor for invariant-check semantics. |
| C12 | POR support is implemented as an invisible-branch heuristic with static footprint inference. | `transpiler/src/modelcheck/por.rs` (`infer_invisible_branch_pruning`, `branch_footprint`) | code | Supports reduction discussion without overclaiming completeness. |
| C13 | Exact-vs-lossy evidence labeling is surfaced from search settings into reports. | `transpiler/src/main.rs` (`classify_search_evidence_mode`) | code | Anchor for "proof-strength vs bug-finding mode" claims. |
| C14 | Canonical status of supported features, blockers, and evidence contracts is maintained in one repo doc. | `docs/model_checker_status.md` (sections 1-4) | repo doc | Canonical status source synchronized with tests/TODO. |
| C15 | User-facing source-first run workflow and limits are documented separately from implementation status. | `docs/model-checking-source-first.md` (sections 1-10) | repo doc | Tutorial-facing operational guidance. |
| C16 | Cross-direction conversion and testing workflow context is documented for reproducibility. | `docs/conversion-testing-guide.md` (overview, quick validation, direction sections) | repo doc | Supports "where source-first fits in broader toolchain" claims. |
| C17 | Checked-in TLC vs source-first benchmark evidence exists with explicit result/bottleneck framing. | `reports/benchmarks/TLC_VS_SOURCE_FIRST_BENCHMARK_COMPARISON.md` | benchmark artifact | Anchor for comparison claims and performance caveats. |
| C18 | Source-first matrix replay and artifact generation are automated in one script. | `scripts/run_model_check_matrix.sh` (`MATRIX_CASES`, artifact generation loop) | script | Evidence-regeneration anchor. |
| C19 | Telemetry delta comparison and exact-mode guard policy checks are automated in one script. | `scripts/compare_model_check_telemetry.sh` (`DELTA_CASES`, exact guard checks) | script | Anchor for performance evidence discipline claims. |

## Required-Anchor Coverage Matrix
| Required Anchor | Referenced By Claim ID(s) |
| --- | --- |
| `docs/model_checker_status.md` | C14 |
| `docs/model-checking-source-first.md` | C15 |
| `docs/conversion-testing-guide.md` | C16 |
| `reports/benchmarks/TLC_VS_SOURCE_FIRST_BENCHMARK_COMPARISON.md` | C17 |
| `transpiler/src/main.rs` | C1, C13 |
| `transpiler/src/modelcheck/config.rs` | C2 |
| `transpiler/src/modelcheck/init.rs` | C3 |
| `transpiler/src/modelcheck/ir.rs` | C4 |
| `transpiler/src/modelcheck/evaluator.rs` | C5 |
| `transpiler/src/modelcheck/domain.rs` | C6 |
| `transpiler/src/modelcheck/solver.rs` | C7 |
| `transpiler/src/modelcheck/explorer.rs` | C8 |
| `transpiler/src/modelcheck/graph.rs` | C9 |
| `transpiler/src/modelcheck/liveness.rs` | C10 |
| `transpiler/src/modelcheck/invariant.rs` | C11 |
| `transpiler/src/modelcheck/por.rs` | C12 |
| `scripts/run_model_check_matrix.sh` | C18 |
| `scripts/compare_model_check_telemetry.sh` | C19 |
