# tla-rs Model Checker Status (Source-First)

Last reviewed: 2026-03-05 (UTC)

This is the canonical status page for `verus-transpile model-check`. Keep this synchronized with `TODO.md` Phase 33 whenever capabilities, blockers, coverage, or performance claims change.

## 1. What the current engine can do

### 1.1 Implemented source-first pipeline

- Ingest protocol spec + types sources and resolve entrypoints (`LInit`, `LNext`) from Rust/Verus input.
- Entrypoint validation is role-based (state/state' type agreement + `LConstants` parameter presence), so protocol-local parameter names/order and 2-arg `LNext(state, state_)` forms are accepted.
- Parse/validate `model.toml`, apply CLI overrides, and resolve selected invariants.
- Build normalized branch IR from `LNext` (disjunction flattening, branch labels, branch-level existential extraction).
- Construct initial states by evaluating `LInit` over finite candidate states and resolved constants.
- Explore state space with BFS/DFS, dedup, invariants, deadlock checks, and counterexample traces with action labels + state diffs.
- Enforce wall-clock exploration timeout via `search.timeout_ms` with concrete stop reason `TimeoutReached`.
- Run bounded liveness checks for configured `leads_to` obligations on fully explored graphs, with branch-label weak/strong fairness filtering.
- Reuse per-run successor memoization during liveness graph indexing (avoids recomputing branch solving for already explored states) and report cache telemetry in JSON/CLI summaries (`successor_cache_hits`, `successor_cache_misses`).
- Reject unknown fairness labels at model-check preflight by validating `properties.fairness.{weak,strong}` against actual `LNext` branch labels.
- Evaluate finite-domain quantifiers (`forall` and expression-level `exists`), including multi-variable binders via bounded nested expansion, when quantifier domains are concretely enumerable from model configuration.
- Evaluate `match` expressions with ordered arm selection, pattern bindings, and guard checks.
- Evaluate struct-update expressions (`Type { updated_field: ..., ..base }`) for struct/enum values.
- Evaluate map-domain builtin method calls (`map.dom()`) for finite map values.
- Track solver fallback telemetry in run summaries/JSON (`direct_assignment_branch_solves`, `enumeration_fallback_branch_solves`, `enumeration_candidate_evaluations`, `guard_pruned_candidate_evaluations`) and enforce a per-state/branch candidate-enumeration guardrail.
- Emit JSON reports including search settings, reduction telemetry, explicit exact-vs-lossy evidence classification (`search.evidence_mode.*`), stop reason, and violation payloads.

### 1.2 Reduction/analysis knobs currently implemented

- `search.state_dedup = "canonical"` (exact dedup; report class `exact_proof_strength`).
- `search.state_dedup = "hash_compaction64"` (lossy dedup; collision-prone by design; report class `lossy_bug_finding_accelerator`).
- `search.symmetry_fields = [...]` (field-level symmetry normalization before dedup; treated as lossy evidence mode).
- `search.por_heuristic = "invisible_branch"` (syntactic branch-pruning heuristic).
- `properties.successor_semantics = "deadlock" | "stuttering"`.

### 1.3 Capability anchors in source

- CLI/model-check execution: `transpiler/src/main.rs` (`execute_model_check`, `Commands::ModelCheck`).
- Explorer and traces: `transpiler/src/modelcheck/explorer.rs`.
- Liveness/fairness SCC checks: `transpiler/src/modelcheck/liveness.rs`.
- Branch IR normalization: `transpiler/src/modelcheck/ir.rs`.
- Runtime evaluator: `transpiler/src/modelcheck/evaluator.rs`.
- Finite-domain expansion: `transpiler/src/modelcheck/domain.rs`.
- Solver: `transpiler/src/modelcheck/solver.rs`.

## 2. What it cannot do yet (implementation-backed)

### 2.1 Unsupported evaluator constructs

`transpiler/src/modelcheck/evaluator.rs` still rejects:

- quantifier bindings must be identifiers (non-identifier quantifier patterns are rejected).
- quantifier evaluation requires a domain resolver; evaluator-level quantifiers without this hook are rejected.
- struct update base must evaluate to struct/enum values (non-struct/enum bases are rejected).
- bitwise/shift operators
- non-identifier `let` patterns
- casts beyond `int` / `nat` / `bool`

### 2.2 Domain/solver/constants limitations

- `transpiler/src/modelcheck/domain.rs` only expands generics for concrete built-ins (`Seq`, `Set`, `Map`) and rejects broader generic forms.
- `transpiler/src/modelcheck/domain.rs` fails unresolved named-type domains with `Missing domain for named type ...` until `quantifiers.types.<TypeName>` is provided.
- `transpiler/src/main.rs` now explores all resolved `LConstants` valuations; model-check preflight still fails on zero matching `LConstants` valuations after applying assignments/domains.
- `transpiler/src/modelcheck/solver.rs` now supports a predicate-only direct-solver hook path (used by source-first model check for direct helper-call branches such as `LStep(s, s_, c)`), and otherwise falls back to candidate-state enumeration for unresolved predicate-only/helper branches; fallback runs are bounded by a hard guardrail (`candidate_evaluation_guardrail_per_state_branch = 10000`) and expose telemetry in JSON/CLI summaries. Enumeration fallback also performs static-guard pruning before candidate loops and reports skipped work as `guard_pruned_candidate_evaluations`.
- `transpiler/src/modelcheck/solver.rs` rejects predicate-only branches without candidate states using `no direct next-state equality constraints` errors.
- `transpiler/src/main.rs` helper-call execution still errors when it could not resolve helper call names or when helper-call recursion exceeded depth limit.

### 2.3 Temporal/fairness/timeout limitations

- Liveness checks are only performed when exploration is complete (`stop_reason = FrontierExhausted`); otherwise `liveness.skipped_reason = "incomplete_exploration"`.
- Fairness labels must match actual `LNext` branch labels exactly; unknown fairness branch labels are rejected at preflight.

### 2.4 Required implementation audit anchors

This section is synchronized against these implementation files via
`test_model_check_status_doc_tracks_implementation_unsupported_surface`:

- `transpiler/src/modelcheck/evaluator.rs`
- `transpiler/src/modelcheck/domain.rs`
- `transpiler/src/modelcheck/solver.rs`
- `transpiler/src/main.rs`

### 2.5 Real-protocol blocker triage priority

Blocker-fix ordering is driven by real protocol specs (not theoretical completeness-only gaps),
using the Phase 33.5 protocol priority:

1. `RSL`
2. `Raft`
3. `Paxos`
4. `VerticalPaxos`
5. `EPaxos`
6. `PBFT`
7. `ChainReplication`
8. `PrimaryBackup`
9. `TwoPhase`
10. `LeaderElection`

Enforced by:

- Every `Result = unsupported` matrix row must reference real protocol source paths under `src/protocol/...`.
- Unsupported rows must remain ordered by the priority list above (filtered to currently unsupported protocols).
  - `test_model_check_unsupported_protocol_rows_prioritize_real_protocol_blockers`
- The full Phase 33.5 priority order stays canonical across:
  - `TODO.md` priority list and
  - `§4` protocol coverage matrix row order.
  - `test_model_check_phase33_5_priority_order_is_canonical_across_todo_and_status_matrix`

## 3. Checked-in model-checking evidence (currently passing)

Status below is based on checked-in automated integration tests under `transpiler/tests/integration.rs`.

### 3.1 Bounded protocol safety runs (all pass)

| Case | Input spec | Types spec | Model config | Automated test | JSON artifact path | Exact replay command |
| --- | --- | --- | --- | --- | --- | --- |
| TwoPhase small bounded run | `src/protocol/TwoPhase/twophase.rs` | `src/protocol/TwoPhase/types.rs` | `transpiler/tests/model_check_fixtures/twophase_small.model.toml` | `test_model_check_twophase_bounded_run` | `reports/model_check/twophase_small.json` | `§5.2 TwoPhase` |
| TwoPhase safety-invariant bounded run | `src/protocol/TwoPhase/twophase.rs` | `src/protocol/TwoPhase/types.rs` | `transpiler/tests/model_check_fixtures/twophase_safety_invariants.model.toml` | `test_model_check_twophase_real_safety_invariants_bounded_run` | `reports/model_check/twophase_safety_invariants.json` | `§5.2 TwoPhase safety invariants` |
| PrimaryBackup small bounded run | `src/protocol/PrimaryBackup/primarybackup.rs` | `src/protocol/PrimaryBackup/types.rs` | `transpiler/tests/model_check_fixtures/primarybackup_small.model.toml` | `test_model_check_primarybackup_helper_call_branches_bounded_run` | `reports/model_check/primarybackup_small.json` | `§5.2 PrimaryBackup` |
| PrimaryBackup safety-invariant bounded run | `src/protocol/PrimaryBackup/primarybackup.rs` | `src/protocol/PrimaryBackup/types.rs` | `transpiler/tests/model_check_fixtures/primarybackup_safety_invariants.model.toml` | `test_model_check_primarybackup_real_safety_invariants_bounded_run` | `reports/model_check/primarybackup_safety_invariants.json` | `§5.2 PrimaryBackup safety invariants` |
| LeaderElection small bounded run | `src/protocol/LeaderElection/election.rs` | `src/protocol/LeaderElection/types.rs` | `transpiler/tests/model_check_fixtures/leaderelection_small.model.toml` | `test_model_check_leader_election_bounded_run` | `reports/model_check/leaderelection_small.json` | `§5.2 LeaderElection` |
| Paxos small bounded run | `src/protocol/Paxos/paxos.rs` | `src/protocol/Paxos/types.rs` | `transpiler/tests/model_check_fixtures/paxos_small.model.toml` | `test_model_check_paxos_bounded_run` | `reports/model_check/paxos_small.json` | `§5.2 Paxos` |
| Paxos safety-invariant bounded run | `src/protocol/Paxos/paxos.rs` | `src/protocol/Paxos/types.rs` | `transpiler/tests/model_check_fixtures/paxos_safety_invariants.model.toml` | `test_model_check_paxos_real_safety_invariants_bounded_run` | `reports/model_check/paxos_safety_invariants.json` | `§5.2 Paxos safety invariants` |

Pass condition used by tests: command success + valid JSON + `summary.states > 0` + `summary.transitions > 0`.
Paxos additionally enforces artifact parity for stable fields (`result`, `search.state_dedup`, `summary.states`, `summary.transitions`, `summary.depth`) against `reports/model_check/paxos_small.json`.
TwoPhase safety-invariant run additionally enforces: three configured/resolved in-source safety predicates and `invariant_violation = null`, with parity checks against `reports/model_check/twophase_safety_invariants.json`.
PrimaryBackup safety-invariant run additionally enforces: three configured/resolved in-source safety predicates and `invariant_violation = null`, with parity checks against `reports/model_check/primarybackup_safety_invariants.json`.
Paxos safety-invariant run additionally enforces: three configured/resolved in-source safety predicates and `invariant_violation = null`, with parity checks against `reports/model_check/paxos_safety_invariants.json`.

### 3.2 Liveness/fairness fixtures (all pass expected outcomes)

| Case | Input spec | Types spec | Model config | Expected result | Automated test | JSON artifact path | Exact replay command |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Avoidable cycle (no fairness) | `transpiler/tests/model_check_fixtures/liveness_avoidable_cycle.protocol.rs` | `transpiler/tests/model_check_fixtures/liveness_avoidable_cycle.types.rs` | `transpiler/tests/model_check_fixtures/liveness_avoidable_cycle_violated.model.toml` | `leads_to_violated` | `test_model_check_liveness_fixtures_cover_fairness_and_non_fairness_outcomes` | `reports/model_check/liveness_avoidable_cycle_violated.json` | `§5.3 Avoidable cycle (no fairness)` |
| Avoidable cycle + strong fairness | same as above | same as above | `transpiler/tests/model_check_fixtures/liveness_avoidable_cycle_strong_fairness.model.toml` | `ok` | same | `reports/model_check/liveness_avoidable_cycle_strong_fairness.json` | `§5.3 Avoidable cycle + strong fairness` |
| Forced progress (no fairness) | `transpiler/tests/model_check_fixtures/liveness_forced.protocol.rs` | `transpiler/tests/model_check_fixtures/liveness_forced.types.rs` | `transpiler/tests/model_check_fixtures/liveness_forced_unfair.model.toml` | `ok` | same | `reports/model_check/liveness_forced_unfair.json` | `§5.3 Forced progress (no fairness)` |
| Forced progress + strong fairness | same as above | same as above | `transpiler/tests/model_check_fixtures/liveness_forced_strong_fairness.model.toml` | `ok` | same | `reports/model_check/liveness_forced_strong_fairness.json` | `§5.3 Forced progress + strong fairness` |

### 3.3 Differential source-first vs wrapper outcomes

- `test_model_check_differential_vs_tlc_wrapper_outcomes_shared_small_models` checks qualitative agreement for shared small models (TwoPhase, LeaderElection, PrimaryBackup, Paxos) and now enforces all three evidence anchors per case:
  - TLC qualitative outcome row in `docs/conversion-testing-guide.md` (`PASS`/`PARTIAL`)
  - checked-in wrapper fixtures in `transpiler/tests/mc_wrapper_fixtures/` (`*.golden.tla` + `*.golden.cfg`) with module/source-module structure checks
  - checked-in source-first artifact parity against `reports/model_check/{twophase,leaderelection,primarybackup,paxos}_small.json` for stable fields (`result`, `search.state_dedup`, `summary.states/transitions/depth`)

### 3.4 Timeout semantics coverage

- `transpiler/src/modelcheck/explorer.rs`:
  - `test_explore_state_space_bfs_stops_on_timeout`
  - `test_explore_state_space_dfs_stops_on_timeout`
- `transpiler/src/main.rs`:
  - `test_model_check_command_timeout_override_changes_execution_behavior`
  - `test_execute_model_check_marks_liveness_skipped_on_timeout`
  - `test_model_check_command_accepts_fairness_configuration`
  - `test_model_check_command_rejects_unknown_fairness_branch_labels`
  - `test_execute_model_check_reports_enumeration_fallback_telemetry`
  - `test_execute_model_check_candidate_enumeration_guardrail_triggers_clean_error`
- `transpiler/src/modelcheck/solver.rs`:
  - `test_solve_branch_successors_with_candidates_reports_enumeration_telemetry`
  - `test_solve_branch_successors_with_candidates_enforces_enumeration_guardrail`

### 3.5 Protocol coverage regressions

- `transpiler/tests/integration.rs`:
  - `test_model_check_rsl_blocker_missing_constants_domain_is_reproducible` (checked-in RSL blocker model reproduces missing `quantifiers.types.LConstants` domain requirement)
  - `test_model_check_verticalpaxos_blocker_existential_expansion_limit_is_reproducible` (checked-in VerticalPaxos blocker model reproduces bounded existential-assignment expansion overflow and enforces fixture intent/minimality)
  - `test_model_check_epaxos_blocker_constants_expansion_limit_is_reproducible` (checked-in EPaxos blocker model reproduces bounded candidate expansion overflow for `LConstants` and enforces fixture intent/minimality)
  - `test_model_check_pbft_bounded_run` (checked-in PBFT bounded source-first run stays green and aligned with checked-in artifact)
  - `test_model_check_chainreplication_blocker_existential_expansion_limit_is_reproducible` (checked-in ChainReplication blocker model reproduces bounded branch existential-domain expansion overflow)
  - `test_model_check_raft_blocker_missing_u64_domain_is_reproducible` (checked-in Raft blocker model reproduces missing `quantifiers.types.u64` domain requirement and enforces that the fixture intentionally omits that domain while staying minimal/bounded)

### 3.6 Supported protocol evidence discipline guard

- `transpiler/tests/integration.rs`:
  - `test_model_check_supported_protocol_rows_require_automated_evidence` enforces that every protocol row marked `Result = ok` in the coverage matrix references existing integration test evidence and checked-in `reports/model_check/*.json` artifacts.

### 3.7 Unsupported protocol blocker discipline guard

- `transpiler/tests/integration.rs`:
  - `test_model_check_unsupported_protocol_rows_require_blocker_regressions` enforces that every protocol row marked `Result = unsupported` in the coverage matrix has:
    - a checked-in model file path that exists,
    - a non-empty first-blocker description,
    - and referenced blocker regression test(s) that exist in `integration.rs`.
  - `test_model_check_unsupported_protocol_rows_record_exact_smallest_blockers` enforces that each unsupported protocol row maps to a specific checked-in minimal blocker model and exact blocker signature, and that blocker fixtures stay intentionally small (`max_depth = 1`, `max_states = 200`).

### 3.8 Quantifier semantic-closure fixture

- `transpiler/tests/integration.rs`:
  - `test_model_check_quantifier_forall_exists_bounded_run` verifies model-check execution succeeds on a checked-in fixture that uses finite-domain single/multi-variable `forall` and expression-level `exists` in `LInit` (`transpiler/tests/model_check_fixtures/quantifier_forall_exists.*`).

### 3.9 Match-expression semantic-closure fixture

- `transpiler/tests/integration.rs`:
  - `test_model_check_match_expression_bounded_run` verifies model-check execution succeeds on a checked-in fixture that uses `match` with guard evaluation in `LInit` (`transpiler/tests/model_check_fixtures/match_expression.*`).

### 3.10 Struct-update semantic-closure fixture

- `transpiler/tests/integration.rs`:
  - `test_model_check_struct_update_bounded_run` verifies model-check execution succeeds on a checked-in fixture that uses struct-update syntax in `LInit` (`transpiler/tests/model_check_fixtures/struct_update.*`).

### 3.11 Map-domain builtin semantic-closure fixture

- `transpiler/tests/integration.rs`:
  - `test_model_check_map_dom_method_bounded_run` verifies model-check execution succeeds on a checked-in fixture that uses `map.dom().contains(...)` in `LInit` (`transpiler/tests/model_check_fixtures/map_dom_method.*`).

### 3.12 Multi-constants valuation semantic-closure fixture

- `transpiler/tests/integration.rs`:
  - `test_model_check_constants_multi_valuation_bounded_run` verifies model-check execution explores multiple resolved `LConstants` valuations in one run and reports aggregated summary counts (`transpiler/tests/model_check_fixtures/constants_multi_valuation.*`).

### 3.13 Predicate-only helper direct-solver fixture

- `transpiler/tests/integration.rs`:
  - `test_model_check_helper_branch_direct_solver_bounded_run` verifies model-check execution can solve direct helper-call branches without candidate enumeration fallback when helper transition constraints are directly solvable (`transpiler/tests/model_check_fixtures/helper_branch_direct_solver.*`).

### 3.14 Semantic-closure evidence discipline guard

- `transpiler/tests/integration.rs`:
  - `test_model_check_semantic_closure_features_require_unit_integration_and_status_doc_evidence` enforces that each Phase 33.3 semantic-closure feature keeps all three evidence anchors:
    - unit regression(s) in evaluator/main/solver sources
    - integration regression in `transpiler/tests/integration.rs`
    - status-doc evidence section + test references in this file

### 3.15 Liveness successor-memoization optimization guard

- `transpiler/tests/integration.rs`:
  - `test_model_check_liveness_fixtures_cover_fairness_and_non_fairness_outcomes` now also verifies `summary.successor_cache_hits > 0` and `summary.successor_cache_misses > 0` for completed liveness runs, locking in the run-scoped successor-cache reuse path.

### 3.16 Guard-pruned enumeration optimization guard

- `transpiler/src/modelcheck/solver.rs`:
  - `test_solve_branch_successors_with_candidates_prunes_static_guard` verifies candidate-enumeration fallback short-circuits when candidate-independent guards are unsatisfied and reports `guard_pruned_candidate_evaluations > 0`.
- `transpiler/src/main.rs`:
  - `test_execute_model_check_reports_guard_pruned_enumeration_telemetry` verifies command-level summary telemetry propagates the optimization (`guard_pruned_candidate_evaluations == 2`) while keeping exact fallback semantics.
- `transpiler/tests/integration.rs`:
  - `test_model_check_guard_pruned_enumeration_bounded_run` replays a checked-in fixture and verifies report telemetry (`enumeration_candidate_evaluations == 0`, `guard_pruned_candidate_evaluations == 2`) through the CLI/JSON surface.

### 3.17 Exact-vs-lossy evidence classification guard

- `transpiler/src/main.rs`:
  - `test_classify_search_evidence_mode_marks_canonical_as_exact_proof_strength`
  - `test_classify_search_evidence_mode_marks_hash_compaction_as_lossy_bug_finding`
  - `test_classify_search_evidence_mode_marks_symmetry_merging_as_lossy_bug_finding`
- `transpiler/tests/integration.rs`:
  - `test_model_check_report_classifies_exact_vs_lossy_search_evidence_mode` verifies JSON report field `search.evidence_mode` is:
    - `class = "exact_proof_strength"` for canonical dedup fixture
    - `class = "lossy_bug_finding_accelerator"` with explicit lossy reason `hash_compaction64_collision_risk` for hash-compaction fixture

### 3.18 Before/after telemetry comparison automation guard

- `scripts/compare_model_check_telemetry.sh` computes fixed Phase 33.4.2 before/after/delta comparisons directly from checked-in `reports/model_check/*.json` artifacts and fails on reachable-state guard drift.
- `scripts/run_model_check_matrix.sh` now regenerates `reports/model_check/OPTIMIZATION_DELTAS.md` on every matrix run.
- `transpiler/tests/integration.rs`:
  - `test_model_check_telemetry_comparison_script_reports_expected_deltas` verifies the script output contains the required metric rows/deltas and that matrix automation is wired to produce the delta report.
  - The same regression also locks the exact-mode reachable-state policy section (`§4.3`) so exactness-changing optimizations require explicit correctness bug-fix documentation.

## 4. Protocol coverage matrix (source-first, checked-in evidence)

Metrics shown for supported entries come from the latest JSON artifacts under `reports/model_check/` (generated via `./scripts/run_model_check_matrix.sh`; exact `elapsed_ms` may vary by machine/load).

| Protocol | Exact source files used | Checked-in model file | Search mode / exactness | Result | States / transitions / depth / elapsed_ms | First blocker (if unsupported) | Automated evidence |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `RSL` | `src/protocol/RSL/distributed_system.rs` | `transpiler/tests/model_check_fixtures/rsl_missing_constants_domain.model.toml` | `bfs`, exact intent (`state_dedup=canonical`; preflight fails before exploration) | `unsupported` | N/A | Configuration error: missing domain for named type `LConstants` (`quantifiers.types.LConstants`). | `test_model_check_rsl_blocker_missing_constants_domain_is_reproducible` |
| `Raft` | `src/protocol/Raft/raft.rs`, `src/protocol/Raft/types.rs` | `transpiler/tests/model_check_fixtures/raft_missing_u64_domain.model.toml` | `bfs`, exact intent (`state_dedup=canonical`; preflight fails before exploration) | `unsupported` | N/A | Configuration error: missing domain for named type `u64` (`quantifiers.types.u64`). | `test_model_check_raft_blocker_missing_u64_domain_is_reproducible` |
| `Paxos` | `src/protocol/Paxos/paxos.rs`, `src/protocol/Paxos/types.rs` | `transpiler/tests/model_check_fixtures/paxos_small.model.toml` | `bfs`, exact (`state_dedup=canonical`) | `ok` | `1 / 2 / 0 / 12` | N/A | `test_model_check_paxos_bounded_run`, `test_model_check_paxos_real_safety_invariants_bounded_run`, `reports/model_check/paxos_small.json`, `reports/model_check/paxos_safety_invariants.json` |
| `VerticalPaxos` | `src/protocol/VerticalPaxos/vpaxos.rs`, `src/protocol/VerticalPaxos/types.rs` | `transpiler/tests/model_check_fixtures/verticalpaxos_state_expansion_limit.model.toml` | `bfs`, exact intent (`state_dedup=canonical`; pre-exploration branch-assignment expansion fails) | `unsupported` | N/A | Configuration error: existential domain expansion exceeded limit (200 assignments) during bounded branch existential enumeration. | `test_model_check_verticalpaxos_blocker_existential_expansion_limit_is_reproducible` |
| `EPaxos` | `src/protocol/EPaxos/epaxos.rs`, `src/protocol/EPaxos/types.rs` | `transpiler/tests/model_check_fixtures/epaxos_state_expansion_limit.model.toml` | `bfs`, exact intent (`state_dedup=canonical`; preflight fails before exploration) | `unsupported` | N/A | Candidate expansion overflow: struct `LConstants` exceeds `search.max_states` limit (200) during finite-domain construction. | `test_model_check_epaxos_blocker_constants_expansion_limit_is_reproducible` |
| `PBFT` | `src/protocol/PBFT/pbft.rs`, `src/protocol/PBFT/types.rs` | `transpiler/tests/model_check_fixtures/pbft_state_expansion_limit.model.toml` | `bfs`, exact (`state_dedup=canonical`) | `ok` | `1 / 0 / 0 / 20` | N/A | `test_model_check_pbft_bounded_run`, `reports/model_check/pbft_small.json` |
| `ChainReplication` | `src/protocol/ChainReplication/chain.rs`, `src/protocol/ChainReplication/types.rs` | `transpiler/tests/model_check_fixtures/chainreplication_state_expansion_limit.model.toml` | `bfs`, exact intent (`state_dedup=canonical`; pre-exploration branch-assignment expansion fails) | `unsupported` | N/A | Configuration error: existential domain expansion exceeded limit (200 assignments) during bounded branch existential enumeration. | `test_model_check_chainreplication_blocker_existential_expansion_limit_is_reproducible` |
| `PrimaryBackup` | `src/protocol/PrimaryBackup/primarybackup.rs`, `src/protocol/PrimaryBackup/types.rs` | `transpiler/tests/model_check_fixtures/primarybackup_small.model.toml` | `bfs`, exact (`state_dedup=canonical`) | `ok` | `2 / 2 / 1 / 67` | N/A | `test_model_check_primarybackup_helper_call_branches_bounded_run`, `test_model_check_primarybackup_real_safety_invariants_bounded_run`, `reports/model_check/primarybackup_small.json`, `reports/model_check/primarybackup_safety_invariants.json` |
| `TwoPhase` | `src/protocol/TwoPhase/twophase.rs`, `src/protocol/TwoPhase/types.rs` | `transpiler/tests/model_check_fixtures/twophase_small.model.toml` | `bfs`, exact (`state_dedup=canonical`) | `ok` | `3 / 4 / 1 / 3268` | N/A | `test_model_check_twophase_bounded_run`, `test_model_check_twophase_real_safety_invariants_bounded_run`, `reports/model_check/twophase_small.json`, `reports/model_check/twophase_safety_invariants.json` |
| `LeaderElection` | `src/protocol/LeaderElection/election.rs`, `src/protocol/LeaderElection/types.rs` | `transpiler/tests/model_check_fixtures/leaderelection_small.model.toml` | `bfs`, exact (`state_dedup=canonical`) | `ok` | `4 / 3 / 1 / 77` | N/A | `test_model_check_leader_election_bounded_run`, `reports/model_check/leaderelection_small.json` |

### 4.1 Exact-mode performance baseline snapshot (Phase 33.4)

Baseline source: checked-in matrix artifacts generated by `./scripts/run_model_check_matrix.sh`.
This table is the pre-optimization reference point for exact-mode performance work; update it only when the checked-in artifact set intentionally changes.

| Protocol | Artifact | `states` | `transitions` | `depth` | `elapsed_ms` | `pruned_by_por` | `symmetry_collapses` | `hash_compaction_collisions` |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `Paxos` | `reports/model_check/paxos_small.json` | `1` | `2` | `0` | `12` | `0` | `0` | `0` |
| `PrimaryBackup` | `reports/model_check/primarybackup_small.json` | `2` | `2` | `1` | `67` | `0` | `0` | `0` |
| `TwoPhase` | `reports/model_check/twophase_small.json` | `3` | `4` | `1` | `3268` | `0` | `0` | `0` |
| `LeaderElection` | `reports/model_check/leaderelection_small.json` | `4` | `3` | `1` | `77` | `0` | `0` | `0` |

### 4.2 Exact-mode optimization delta snapshot (Phase 33.4.2)

The table below locks explicit before/after telemetry deltas for the two exact-mode optimizations landed in Phase 33.4.2. "Before" values are the pre-optimization baselines; "After" values come from checked-in replayable JSON artifacts generated by `./scripts/run_model_check_matrix.sh`.

| Optimization | Baseline artifact | Metric | Before | After | Delta | Reachable-state guard |
| --- | --- | --- | --- | --- | --- | --- |
| 33.4.2.a successor memoization | `reports/model_check/liveness_avoidable_cycle_violated.json` | `successor_cache_hits` | `0` | `3` | `+3` | `3/5 -> 3/5` |
| 33.4.2.a successor memoization | `reports/model_check/liveness_avoidable_cycle_violated.json` | `successor_cache_misses` | `0` | `3` | `+3` | `3/5 -> 3/5` |
| 33.4.2.b guard-pruned fallback enumeration | `reports/model_check/guard_pruned_enumeration.json` | `enumeration_candidate_evaluations` | `2` | `0` | `-2` | `1/0 -> 1/0` |
| 33.4.2.b guard-pruned fallback enumeration | `reports/model_check/guard_pruned_enumeration.json` | `guard_pruned_candidate_evaluations` | `0` | `2` | `+2` | `1/0 -> 1/0` |

### 4.3 Exact-mode reachable-state change policy (Phase 33.4)

Any optimization that changes exact-mode reachable-state counts (`states/transitions`) is rejected unless both are true:

1. The change is due to a correctness bug fix (not a performance-only tweak).
2. The status doc records the change explicitly with old/new guard and rationale.

Automation enforcement:

- `scripts/compare_model_check_telemetry.sh` validates a fixed exact-mode baseline guard set and fails on undocumented drift.
- If an exactness-changing correctness fix is intentional, add an exception row below that includes:
  - artifact path
  - guard change token formatted as `` `old -> new` ``
  - phrase `correctness bug fix` in the rationale text

Exception rows (approved exactness-changing fixes):

| Artifact | Guard change | Rationale |
| --- | --- | --- |
| _None_ | _N/A_ | _No approved exactness-changing correctness bug fixes currently._ |

## 5. Exact reproduction commands

Run from repo root.

### 5.1 Build binary

```bash
cargo build --manifest-path transpiler/Cargo.toml --bin verus-transpile
```

### 5.2 Run each passing protocol model-check

TwoPhase:

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/TwoPhase/twophase.rs \
  --types src/protocol/TwoPhase/types.rs \
  --model transpiler/tests/model_check_fixtures/twophase_small.model.toml \
  --search bfs \
  --json-report
```

TwoPhase safety invariants:

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/TwoPhase/twophase.rs \
  --types src/protocol/TwoPhase/types.rs \
  --model transpiler/tests/model_check_fixtures/twophase_safety_invariants.model.toml \
  --search bfs \
  --json-report
```

Expected result: command succeeds with `result = "ok"`, `invariant_violation = null`, and resolved invariants including:
`LSafetyNoCommitAbortOverlap`, `LSafetyCommittedSubsetPrepared`, `LSafetyTmCommittedRequiresAllPrepared`.

PrimaryBackup:

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/PrimaryBackup/primarybackup.rs \
  --types src/protocol/PrimaryBackup/types.rs \
  --model transpiler/tests/model_check_fixtures/primarybackup_small.model.toml \
  --search bfs \
  --json-report
```

PrimaryBackup safety invariants:

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/PrimaryBackup/primarybackup.rs \
  --types src/protocol/PrimaryBackup/types.rs \
  --model transpiler/tests/model_check_fixtures/primarybackup_safety_invariants.model.toml \
  --search bfs \
  --json-report
```

Expected result: command succeeds with `result = "ok"`, `invariant_violation = null`, and resolved invariants including:
`LSafetyNoPendingImpliesClearedValue`, `LSafetyUnackedImpliesPending`, `LSafetyInactiveStateIsQuiescent`.

LeaderElection:

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/LeaderElection/election.rs \
  --types src/protocol/LeaderElection/types.rs \
  --model transpiler/tests/model_check_fixtures/leaderelection_small.model.toml \
  --search bfs \
  --json-report
```

Paxos:

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/Paxos/paxos.rs \
  --types src/protocol/Paxos/types.rs \
  --model transpiler/tests/model_check_fixtures/paxos_small.model.toml \
  --search bfs \
  --json-report
```

Paxos safety invariants:

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/Paxos/paxos.rs \
  --types src/protocol/Paxos/types.rs \
  --model transpiler/tests/model_check_fixtures/paxos_safety_invariants.model.toml \
  --search bfs \
  --json-report
```

Expected result: command succeeds with `result = "ok"`, `invariant_violation = null`, and resolved invariants including:
`LSafetyAcceptedBallotBoundedByPromise`, `LSafetyDecidedRequiresQuorum`, `LSafetyDecidedMatchesProposedValue`.

### 5.3 Run liveness/fairness fixtures

Avoidable cycle (no fairness):

```bash
transpiler/target/debug/verus-transpile model-check \
  --input transpiler/tests/model_check_fixtures/liveness_avoidable_cycle.protocol.rs \
  --types transpiler/tests/model_check_fixtures/liveness_avoidable_cycle.types.rs \
  --model transpiler/tests/model_check_fixtures/liveness_avoidable_cycle_violated.model.toml \
  --search bfs \
  --json-report
```

Avoidable cycle + strong fairness:

```bash
transpiler/target/debug/verus-transpile model-check \
  --input transpiler/tests/model_check_fixtures/liveness_avoidable_cycle.protocol.rs \
  --types transpiler/tests/model_check_fixtures/liveness_avoidable_cycle.types.rs \
  --model transpiler/tests/model_check_fixtures/liveness_avoidable_cycle_strong_fairness.model.toml \
  --search bfs \
  --json-report
```

Forced progress (no fairness):

```bash
transpiler/target/debug/verus-transpile model-check \
  --input transpiler/tests/model_check_fixtures/liveness_forced.protocol.rs \
  --types transpiler/tests/model_check_fixtures/liveness_forced.types.rs \
  --model transpiler/tests/model_check_fixtures/liveness_forced_unfair.model.toml \
  --search bfs \
  --json-report
```

Forced progress + strong fairness:

```bash
transpiler/target/debug/verus-transpile model-check \
  --input transpiler/tests/model_check_fixtures/liveness_forced.protocol.rs \
  --types transpiler/tests/model_check_fixtures/liveness_forced.types.rs \
  --model transpiler/tests/model_check_fixtures/liveness_forced_strong_fairness.model.toml \
  --search bfs \
  --json-report
```

### 5.4 Replay currently checked-in unsupported blocker (RSL)

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/RSL/distributed_system.rs \
  --init RslInit \
  --next RslNext \
  --model transpiler/tests/model_check_fixtures/rsl_missing_constants_domain.model.toml \
  --search bfs
```

Expected result: command fails with `Configuration error: Missing domain for named type \`LConstants\`` and a hint to provide `quantifiers.types.LConstants`.

### 5.5 Replay currently checked-in unsupported blocker (Raft)

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/Raft/raft.rs \
  --types src/protocol/Raft/types.rs \
  --model transpiler/tests/model_check_fixtures/raft_missing_u64_domain.model.toml \
  --search bfs
```

Expected result: command fails with `Configuration error: Missing domain for named type \`u64\`` and a hint to provide `quantifiers.types.u64`.

### 5.6 Replay currently checked-in unsupported blocker (VerticalPaxos)

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/VerticalPaxos/vpaxos.rs \
  --types src/protocol/VerticalPaxos/types.rs \
  --model transpiler/tests/model_check_fixtures/verticalpaxos_state_expansion_limit.model.toml \
  --search bfs
```

Expected result: command fails with `Configuration error: Existential domain expansion exceeded limit (200 assignments).`

### 5.7 Replay currently checked-in unsupported blocker (EPaxos)

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/EPaxos/epaxos.rs \
  --types src/protocol/EPaxos/types.rs \
  --model transpiler/tests/model_check_fixtures/epaxos_state_expansion_limit.model.toml \
  --search bfs
```

Expected result: command fails with `Model-check candidate expansion for struct \`LConstants\` exceeded limit (200).`

### 5.8 Replay checked-in bounded PBFT run

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/PBFT/pbft.rs \
  --types src/protocol/PBFT/types.rs \
  --model transpiler/tests/model_check_fixtures/pbft_state_expansion_limit.model.toml \
  --search bfs
```

Expected result: command succeeds with `result: ok` and summary `states=1`, `transitions=0`, `depth=0` (bounded exact run).

### 5.9 Replay currently checked-in unsupported blocker (ChainReplication)

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/ChainReplication/chain.rs \
  --types src/protocol/ChainReplication/types.rs \
  --model transpiler/tests/model_check_fixtures/chainreplication_state_expansion_limit.model.toml \
  --search bfs
```

Expected result: command fails with `Configuration error: Existential domain expansion exceeded limit (200 assignments).`

### 5.10 Re-run automated evidence directly

```bash
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_primarybackup_helper_call_branches_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_primarybackup_real_safety_invariants_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_twophase_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_twophase_real_safety_invariants_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_leader_election_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_paxos_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_quantifier_forall_exists_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_match_expression_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_struct_update_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_map_dom_method_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_constants_multi_valuation_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_helper_branch_direct_solver_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_semantic_closure_features_require_unit_integration_and_status_doc_evidence -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_supported_protocol_rows_require_automated_evidence -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_unsupported_protocol_rows_require_blocker_regressions -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_unsupported_protocol_rows_prioritize_real_protocol_blockers -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_unsupported_protocol_rows_record_exact_smallest_blockers -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_status_doc_tracks_implementation_unsupported_surface -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_rsl_blocker_missing_constants_domain_is_reproducible -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_verticalpaxos_blocker_existential_expansion_limit_is_reproducible -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_epaxos_blocker_constants_expansion_limit_is_reproducible -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_pbft_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_chainreplication_blocker_existential_expansion_limit_is_reproducible -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_raft_blocker_missing_u64_domain_is_reproducible -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_liveness_fixtures_cover_fairness_and_non_fairness_outcomes -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_differential_vs_tlc_wrapper_outcomes_shared_small_models -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_paxos_real_safety_invariants_bounded_run -- --nocapture
```

### 5.11 Generate checked-in JSON artifact bundle

```bash
./scripts/run_model_check_matrix.sh
```

Generated outputs are written to `reports/model_check/` and include one JSON report per matrix case, `OPTIMIZATION_DELTAS.md`, and `MANIFEST.txt`.

### 5.12 Verify status-doc evidence references

```bash
./scripts/verify_model_check_evidence_paths.sh
```

This fails if any `reports/model_check/*.json` path referenced in this status doc is missing.

### 5.13 Compare optimization telemetry before/after deltas

```bash
./scripts/compare_model_check_telemetry.sh
```

This prints the Phase 33.4.2 before/after/delta table plus exact-mode policy checks from checked-in artifacts and fails on either:

- reachable-state guard drift in the optimization delta cases, or
- undocumented exact-mode reachable-state changes (missing `correctness bug fix` exception entry in `§4.3`).

## 6. Update rules (strict)

- Never mark a protocol as source-first supported without checked-in model + automated evidence.
- Keep exact-mode results and lossy-mode results separate.
- For failures, record the first blocker and the next concrete code task.
- For every capability change, update both:
  - this status file
  - `TODO.md` Phase 33 checklist
- Do not replace missing evidence with prose claims.
