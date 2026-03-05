# tla-rs Model Checker Status (Source-First)

Last reviewed: 2026-03-05 (UTC)

This is the canonical status page for `verus-transpile model-check`. Keep this synchronized with `TODO.md` Phase 33 whenever capabilities, blockers, coverage, or performance claims change.

## 1. What the current engine can do

### 1.1 Implemented source-first pipeline

- Ingest protocol spec + types sources and resolve entrypoints (`LInit`, `LNext`) from Rust/Verus input.
- Parse/validate `model.toml`, apply CLI overrides, and resolve selected invariants.
- Build normalized branch IR from `LNext` (disjunction flattening, branch labels, branch-level existential extraction).
- Construct initial states by evaluating `LInit` over finite candidate states and resolved constants.
- Explore state space with BFS/DFS, dedup, invariants, deadlock checks, and counterexample traces with action labels + state diffs.
- Enforce wall-clock exploration timeout via `search.timeout_ms` with concrete stop reason `TimeoutReached`.
- Run bounded liveness checks for configured `leads_to` obligations on fully explored graphs, with branch-label weak/strong fairness filtering.
- Reject unknown fairness labels at model-check preflight by validating `properties.fairness.{weak,strong}` against actual `LNext` branch labels.
- Evaluate finite-domain quantifiers (`forall` and expression-level `exists`), including multi-variable binders via bounded nested expansion, when quantifier domains are concretely enumerable from model configuration.
- Track solver fallback telemetry in run summaries/JSON (`direct_assignment_branch_solves`, `enumeration_fallback_branch_solves`, `enumeration_candidate_evaluations`) and enforce a per-state/branch candidate-enumeration guardrail.
- Emit JSON reports including search settings, reduction telemetry, stop reason, and violation payloads.

### 1.2 Reduction/analysis knobs currently implemented

- `search.state_dedup = "canonical"` (exact dedup).
- `search.state_dedup = "hash_compaction64"` (lossy dedup; collision-prone by design).
- `search.symmetry_fields = [...]` (field-level symmetry normalization before dedup).
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
- `match`
- struct update expressions
- bitwise/shift operators
- non-identifier `let` patterns
- casts beyond `int` / `nat` / `bool`

### 2.2 Domain/solver/constants limitations

- `transpiler/src/modelcheck/domain.rs` only expands generics for concrete built-ins (`Seq`, `Set`, `Map`) and rejects broader generic forms.
- `transpiler/src/modelcheck/domain.rs` fails unresolved named-type domains with `Missing domain for named type ...` until `quantifiers.types.<TypeName>` is provided.
- `transpiler/src/main.rs` currently requires exactly one resolved `LConstants` valuation.
- `transpiler/src/modelcheck/solver.rs` still uses candidate-state enumeration fallback for predicate-only/helper branches; runs are now bounded by a hard guardrail (`candidate_evaluation_guardrail_per_state_branch = 10000`) and expose fallback telemetry in JSON/CLI summaries.
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

Enforced by `test_model_check_unsupported_protocol_rows_prioritize_real_protocol_blockers`:

- Every `Result = unsupported` matrix row must reference real protocol source paths under `src/protocol/...`.
- Unsupported rows must remain ordered by the priority list above (filtered to currently unsupported protocols).

## 3. Checked-in model-checking evidence (currently passing)

Status below is based on checked-in automated integration tests under `transpiler/tests/integration.rs`.

### 3.1 Bounded protocol safety runs (all pass)

| Case | Input spec | Types spec | Model config | Automated test | JSON artifact path | Exact replay command |
| --- | --- | --- | --- | --- | --- | --- |
| TwoPhase small bounded run | `src/protocol/TwoPhase/twophase.rs` | `src/protocol/TwoPhase/types.rs` | `transpiler/tests/model_check_fixtures/twophase_small.model.toml` | `test_model_check_twophase_bounded_run` | `reports/model_check/twophase_small.json` | `§5.2 TwoPhase` |
| PrimaryBackup small bounded run | `src/protocol/PrimaryBackup/primarybackup.rs` | `src/protocol/PrimaryBackup/types.rs` | `transpiler/tests/model_check_fixtures/primarybackup_small.model.toml` | `test_model_check_primarybackup_helper_call_branches_bounded_run` | `reports/model_check/primarybackup_small.json` | `§5.2 PrimaryBackup` |
| LeaderElection small bounded run | `src/protocol/LeaderElection/election.rs` | `src/protocol/LeaderElection/types.rs` | `transpiler/tests/model_check_fixtures/leaderelection_small.model.toml` | `test_model_check_leader_election_bounded_run` | `reports/model_check/leaderelection_small.json` | `§5.2 LeaderElection` |
| Paxos small bounded run | `src/protocol/Paxos/paxos.rs` | `src/protocol/Paxos/types.rs` | `transpiler/tests/model_check_fixtures/paxos_small.model.toml` | `test_model_check_paxos_bounded_run` | `reports/model_check/paxos_small.json` | `§5.2 Paxos` |

Pass condition used by tests: command success + valid JSON + `summary.states > 0` + `summary.transitions > 0`.

### 3.2 Liveness/fairness fixtures (all pass expected outcomes)

| Case | Input spec | Types spec | Model config | Expected result | Automated test | JSON artifact path | Exact replay command |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Avoidable cycle (no fairness) | `transpiler/tests/model_check_fixtures/liveness_avoidable_cycle.protocol.rs` | `transpiler/tests/model_check_fixtures/liveness_avoidable_cycle.types.rs` | `transpiler/tests/model_check_fixtures/liveness_avoidable_cycle_violated.model.toml` | `leads_to_violated` | `test_model_check_liveness_fixtures_cover_fairness_and_non_fairness_outcomes` | `reports/model_check/liveness_avoidable_cycle_violated.json` | `§5.3 Avoidable cycle (no fairness)` |
| Avoidable cycle + strong fairness | same as above | same as above | `transpiler/tests/model_check_fixtures/liveness_avoidable_cycle_strong_fairness.model.toml` | `ok` | same | `reports/model_check/liveness_avoidable_cycle_strong_fairness.json` | `§5.3 Avoidable cycle + strong fairness` |
| Forced progress (no fairness) | `transpiler/tests/model_check_fixtures/liveness_forced.protocol.rs` | `transpiler/tests/model_check_fixtures/liveness_forced.types.rs` | `transpiler/tests/model_check_fixtures/liveness_forced_unfair.model.toml` | `ok` | same | `reports/model_check/liveness_forced_unfair.json` | `§5.3 Forced progress (no fairness)` |
| Forced progress + strong fairness | same as above | same as above | `transpiler/tests/model_check_fixtures/liveness_forced_strong_fairness.model.toml` | `ok` | same | `reports/model_check/liveness_forced_strong_fairness.json` | `§5.3 Forced progress + strong fairness` |

### 3.3 Differential source-first vs wrapper outcomes

- `test_model_check_differential_vs_tlc_wrapper_outcomes_shared_small_models` checks qualitative agreement for shared small models (TwoPhase, LeaderElection, PrimaryBackup, Paxos) against the TLC outcomes documented in `docs/conversion-testing-guide.md`.

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

### 3.5 Unsupported protocol blocker regressions

- `transpiler/tests/integration.rs`:
  - `test_model_check_rsl_blocker_incompatible_init_signature_is_reproducible` (checked-in RSL blocker model reproduces current init-signature gate expecting `LState`/`LConstants`)
  - `test_model_check_verticalpaxos_blocker_state_expansion_limit_is_reproducible` (checked-in VerticalPaxos blocker model reproduces bounded candidate expansion overflow for `LState`)
  - `test_model_check_epaxos_blocker_state_expansion_limit_is_reproducible` (checked-in EPaxos blocker model reproduces bounded candidate expansion overflow for `LState`)
  - `test_model_check_pbft_blocker_state_expansion_limit_is_reproducible` (checked-in PBFT blocker model reproduces bounded candidate expansion overflow for `LState`)
  - `test_model_check_chainreplication_blocker_state_expansion_limit_is_reproducible` (checked-in ChainReplication blocker model reproduces bounded candidate expansion overflow for `LState`)
  - `test_model_check_raft_blocker_missing_log_entry_domain_is_reproducible` (checked-in Raft blocker model reproduces missing `quantifiers.types.LLogEntry` domain requirement)

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

## 4. Protocol coverage matrix (source-first, checked-in evidence)

Metrics shown for supported entries come from the latest JSON artifacts under `reports/model_check/` (generated via `./scripts/run_model_check_matrix.sh`; exact `elapsed_ms` may vary by machine/load).

| Protocol | Exact source files used | Checked-in model file | Search mode / exactness | Result | States / transitions / depth / elapsed_ms | First blocker (if unsupported) | Automated evidence |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `RSL` | `src/protocol/RSL/distributed_system.rs` | `transpiler/tests/model_check_fixtures/rsl_incompatible_init_signature.model.toml` | `bfs`, exact intent (`state_dedup=canonical`; preflight fails before exploration) | `unsupported` | N/A | Configuration error: incompatible `RslInit` signature (current source-first gate expects `(s: LState, c: LConstants)`). | `test_model_check_rsl_blocker_incompatible_init_signature_is_reproducible` |
| `Raft` | `src/protocol/Raft/raft.rs`, `src/protocol/Raft/types.rs` | `transpiler/tests/model_check_fixtures/raft_missing_log_entry_domain.model.toml` | `bfs`, exact intent (`state_dedup=canonical`; preflight fails before exploration) | `unsupported` | N/A | Configuration error: missing domain for named type `LLogEntry` (`quantifiers.types.LLogEntry`). | `test_model_check_raft_blocker_missing_log_entry_domain_is_reproducible` |
| `Paxos` | `src/protocol/Paxos/paxos.rs`, `src/protocol/Paxos/types.rs` | `transpiler/tests/model_check_fixtures/paxos_small.model.toml` | `bfs`, exact (`state_dedup=canonical`) | `ok` | `1 / 2 / 0 / 10` | N/A | `test_model_check_paxos_bounded_run`, `reports/model_check/paxos_small.json` |
| `VerticalPaxos` | `src/protocol/VerticalPaxos/vpaxos.rs`, `src/protocol/VerticalPaxos/types.rs` | `transpiler/tests/model_check_fixtures/verticalpaxos_state_expansion_limit.model.toml` | `bfs`, exact intent (`state_dedup=canonical`; preflight fails before exploration) | `unsupported` | N/A | Candidate expansion overflow: struct `LState` exceeds `search.max_states` limit (200) during finite-domain construction. | `test_model_check_verticalpaxos_blocker_state_expansion_limit_is_reproducible` |
| `EPaxos` | `src/protocol/EPaxos/epaxos.rs`, `src/protocol/EPaxos/types.rs` | `transpiler/tests/model_check_fixtures/epaxos_state_expansion_limit.model.toml` | `bfs`, exact intent (`state_dedup=canonical`; preflight fails before exploration) | `unsupported` | N/A | Candidate expansion overflow: struct `LState` exceeds `search.max_states` limit (200) during finite-domain construction. | `test_model_check_epaxos_blocker_state_expansion_limit_is_reproducible` |
| `PBFT` | `src/protocol/PBFT/pbft.rs`, `src/protocol/PBFT/types.rs` | `transpiler/tests/model_check_fixtures/pbft_state_expansion_limit.model.toml` | `bfs`, exact intent (`state_dedup=canonical`; preflight fails before exploration) | `unsupported` | N/A | Candidate expansion overflow: struct `LState` exceeds `search.max_states` limit (200) during finite-domain construction. | `test_model_check_pbft_blocker_state_expansion_limit_is_reproducible` |
| `ChainReplication` | `src/protocol/ChainReplication/chain.rs`, `src/protocol/ChainReplication/types.rs` | `transpiler/tests/model_check_fixtures/chainreplication_state_expansion_limit.model.toml` | `bfs`, exact intent (`state_dedup=canonical`; preflight fails before exploration) | `unsupported` | N/A | Candidate expansion overflow: struct `LState` exceeds `search.max_states` limit (200) during finite-domain construction. | `test_model_check_chainreplication_blocker_state_expansion_limit_is_reproducible` |
| `PrimaryBackup` | `src/protocol/PrimaryBackup/primarybackup.rs`, `src/protocol/PrimaryBackup/types.rs` | `transpiler/tests/model_check_fixtures/primarybackup_small.model.toml` | `bfs`, exact (`state_dedup=canonical`) | `ok` | `2 / 2 / 1 / 64` | N/A | `test_model_check_primarybackup_helper_call_branches_bounded_run`, `reports/model_check/primarybackup_small.json` |
| `TwoPhase` | `src/protocol/TwoPhase/twophase.rs`, `src/protocol/TwoPhase/types.rs` | `transpiler/tests/model_check_fixtures/twophase_small.model.toml` | `bfs`, exact (`state_dedup=canonical`) | `ok` | `3 / 4 / 1 / 3206` | N/A | `test_model_check_twophase_bounded_run`, `reports/model_check/twophase_small.json` |
| `LeaderElection` | `src/protocol/LeaderElection/election.rs`, `src/protocol/LeaderElection/types.rs` | `transpiler/tests/model_check_fixtures/leaderelection_small.model.toml` | `bfs`, exact (`state_dedup=canonical`) | `ok` | `4 / 3 / 1 / 71` | N/A | `test_model_check_leader_election_bounded_run`, `reports/model_check/leaderelection_small.json` |

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

PrimaryBackup:

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/PrimaryBackup/primarybackup.rs \
  --types src/protocol/PrimaryBackup/types.rs \
  --model transpiler/tests/model_check_fixtures/primarybackup_small.model.toml \
  --search bfs \
  --json-report
```

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
  --model transpiler/tests/model_check_fixtures/rsl_incompatible_init_signature.model.toml \
  --search bfs
```

Expected result: command fails with `Configuration error: Incompatible \`RslInit\` signature.` and describes the currently required `(s: LState, c: LConstants)` shape.

### 5.5 Replay currently checked-in unsupported blocker (Raft)

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/Raft/raft.rs \
  --types src/protocol/Raft/types.rs \
  --model transpiler/tests/model_check_fixtures/raft_missing_log_entry_domain.model.toml \
  --search bfs
```

Expected result: command fails with `Configuration error: Missing domain for named type \`LLogEntry\`` and a hint to provide `quantifiers.types.LLogEntry`.

### 5.6 Replay currently checked-in unsupported blocker (VerticalPaxos)

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/VerticalPaxos/vpaxos.rs \
  --types src/protocol/VerticalPaxos/types.rs \
  --model transpiler/tests/model_check_fixtures/verticalpaxos_state_expansion_limit.model.toml \
  --search bfs
```

Expected result: command fails with `Model-check candidate expansion for struct \`LState\` exceeded limit (200).`

### 5.7 Replay currently checked-in unsupported blocker (EPaxos)

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/EPaxos/epaxos.rs \
  --types src/protocol/EPaxos/types.rs \
  --model transpiler/tests/model_check_fixtures/epaxos_state_expansion_limit.model.toml \
  --search bfs
```

Expected result: command fails with `Model-check candidate expansion for struct \`LState\` exceeded limit (200).`

### 5.8 Replay currently checked-in unsupported blocker (PBFT)

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/PBFT/pbft.rs \
  --types src/protocol/PBFT/types.rs \
  --model transpiler/tests/model_check_fixtures/pbft_state_expansion_limit.model.toml \
  --search bfs
```

Expected result: command fails with `Model-check candidate expansion for struct \`LState\` exceeded limit (200).`

### 5.9 Replay currently checked-in unsupported blocker (ChainReplication)

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/ChainReplication/chain.rs \
  --types src/protocol/ChainReplication/types.rs \
  --model transpiler/tests/model_check_fixtures/chainreplication_state_expansion_limit.model.toml \
  --search bfs
```

Expected result: command fails with `Model-check candidate expansion for struct \`LState\` exceeded limit (200).`

### 5.10 Re-run automated evidence directly

```bash
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_primarybackup_helper_call_branches_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_twophase_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_leader_election_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_paxos_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_quantifier_forall_exists_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_supported_protocol_rows_require_automated_evidence -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_unsupported_protocol_rows_require_blocker_regressions -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_unsupported_protocol_rows_prioritize_real_protocol_blockers -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_unsupported_protocol_rows_record_exact_smallest_blockers -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_status_doc_tracks_implementation_unsupported_surface -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_rsl_blocker_incompatible_init_signature_is_reproducible -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_verticalpaxos_blocker_state_expansion_limit_is_reproducible -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_epaxos_blocker_state_expansion_limit_is_reproducible -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_pbft_blocker_state_expansion_limit_is_reproducible -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_chainreplication_blocker_state_expansion_limit_is_reproducible -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_raft_blocker_missing_log_entry_domain_is_reproducible -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_liveness_fixtures_cover_fairness_and_non_fairness_outcomes -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_differential_vs_tlc_wrapper_outcomes_shared_small_models -- --nocapture
```

### 5.11 Generate checked-in JSON artifact bundle

```bash
./scripts/run_model_check_matrix.sh
```

Generated outputs are written to `reports/model_check/` and include one JSON report per matrix case plus `MANIFEST.txt`.

### 5.12 Verify status-doc evidence references

```bash
./scripts/verify_model_check_evidence_paths.sh
```

This fails if any `reports/model_check/*.json` path referenced in this status doc is missing.

## 6. Update rules (strict)

- Never mark a protocol as source-first supported without checked-in model + automated evidence.
- Keep exact-mode results and lossy-mode results separate.
- For failures, record the first blocker and the next concrete code task.
- For every capability change, update both:
  - this status file
  - `TODO.md` Phase 33 checklist
- Do not replace missing evidence with prose claims.
