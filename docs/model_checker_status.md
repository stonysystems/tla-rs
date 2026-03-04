# tla-rs Model Checker Status (Source-First)

Last reviewed: 2026-03-04 (UTC)

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

- `forall` quantifier
- expression-level `exists`
- `match`
- struct update expressions
- bitwise/shift operators
- non-identifier `let` patterns
- casts beyond `int` / `nat` / `bool`

### 2.2 Domain/solver/constants limitations

- `transpiler/src/modelcheck/domain.rs` only expands generics for concrete built-ins (`Seq`, `Set`, `Map`) and rejects broader generic forms.
- `transpiler/src/main.rs` currently requires exactly one resolved `LConstants` valuation.
- `transpiler/src/modelcheck/solver.rs` falls back to full candidate-state enumeration for branches without direct `s_.field == ...` assignments; this can explode badly.

### 2.3 Temporal/fairness/timeout limitations

- Liveness checks are only performed when exploration is complete (`stop_reason = FrontierExhausted`); otherwise `liveness.skipped_reason = "incomplete_exploration"`.
- Fairness labels are validated for non-empty/duplicate format, but not currently rejected when they do not match any real branch label (typos can silently become ineffective constraints).

## 3. Checked-in model-checking evidence (currently passing)

Status below is based on checked-in automated integration tests under `transpiler/tests/integration.rs`.

### 3.1 Bounded protocol safety runs (all pass)

| Case | Input spec | Types spec | Model config | Automated test |
| --- | --- | --- | --- | --- |
| TwoPhase small bounded run | `src/protocol/TwoPhase/twophase.rs` | `src/protocol/TwoPhase/types.rs` | `transpiler/tests/model_check_fixtures/twophase_small.model.toml` | `test_model_check_twophase_bounded_run` |
| PrimaryBackup small bounded run | `src/protocol/PrimaryBackup/primarybackup.rs` | `src/protocol/PrimaryBackup/types.rs` | `transpiler/tests/model_check_fixtures/primarybackup_small.model.toml` | `test_model_check_primarybackup_helper_call_branches_bounded_run` |
| LeaderElection small bounded run | `src/protocol/LeaderElection/election.rs` | `src/protocol/LeaderElection/types.rs` | `transpiler/tests/model_check_fixtures/leaderelection_small.model.toml` | `test_model_check_leader_election_bounded_run` |
| Paxos small bounded run | `src/protocol/Paxos/paxos.rs` | `src/protocol/Paxos/types.rs` | `transpiler/tests/model_check_fixtures/paxos_small.model.toml` | `test_model_check_paxos_bounded_run` |

Pass condition used by tests: command success + valid JSON + `summary.states > 0` + `summary.transitions > 0`.

### 3.2 Liveness/fairness fixtures (all pass expected outcomes)

| Case | Input spec | Types spec | Model config | Expected result | Automated test |
| --- | --- | --- | --- | --- | --- |
| Avoidable cycle (no fairness) | `transpiler/tests/model_check_fixtures/liveness_avoidable_cycle.protocol.rs` | `transpiler/tests/model_check_fixtures/liveness_avoidable_cycle.types.rs` | `transpiler/tests/model_check_fixtures/liveness_avoidable_cycle_violated.model.toml` | `leads_to_violated` | `test_model_check_liveness_fixtures_cover_fairness_and_non_fairness_outcomes` |
| Avoidable cycle + strong fairness | same as above | same as above | `transpiler/tests/model_check_fixtures/liveness_avoidable_cycle_strong_fairness.model.toml` | `ok` | same |
| Forced progress (no fairness) | `transpiler/tests/model_check_fixtures/liveness_forced.protocol.rs` | `transpiler/tests/model_check_fixtures/liveness_forced.types.rs` | `transpiler/tests/model_check_fixtures/liveness_forced_unfair.model.toml` | `ok` | same |
| Forced progress + strong fairness | same as above | same as above | `transpiler/tests/model_check_fixtures/liveness_forced_strong_fairness.model.toml` | `ok` | same |

### 3.3 Differential source-first vs wrapper outcomes

- `test_model_check_differential_vs_tlc_wrapper_outcomes_shared_small_models` checks qualitative agreement for shared small models (TwoPhase, LeaderElection, PrimaryBackup, Paxos) against the TLC outcomes documented in `docs/conversion-testing-guide.md`.

### 3.4 Timeout semantics coverage

- `transpiler/src/modelcheck/explorer.rs`:
  - `test_explore_state_space_bfs_stops_on_timeout`
  - `test_explore_state_space_dfs_stops_on_timeout`
- `transpiler/src/main.rs`:
  - `test_model_check_command_timeout_override_changes_execution_behavior`
  - `test_execute_model_check_marks_liveness_skipped_on_timeout`

## 4. Protocol coverage matrix (source-first, checked-in evidence)

| Protocol | Source-first status | Checked-in model + automation | Notes |
| --- | --- | --- | --- |
| `RSL` | Not yet covered | No | Highest-value missing consensus protocol. |
| `Raft` | Not yet covered | No | Needs source-first model-check evidence separate from refinement proofs. |
| `Paxos` | Bounded small-model pass | Yes | Fixture-backed integration test exists. |
| `VerticalPaxos` | Not yet covered | No | Needs checked-in source-first model/check. |
| `EPaxos` | Not yet covered | No | Needs checked-in source-first model/check. |
| `PBFT` | Not yet covered | No | Needs checked-in source-first model/check. |
| `ChainReplication` | Not yet covered | No | Needs checked-in source-first model/check. |
| `PrimaryBackup` | Bounded small-model pass | Yes | Fixture-backed integration test exists. |
| `TwoPhase` | Bounded small-model pass | Yes | Fixture-backed integration test exists. |
| `LeaderElection` | Bounded small-model pass | Yes | Fixture-backed integration test exists. |

## 5. Exact reproduction commands

Run from repo root.

### 5.1 Build binary

```bash
cargo build --manifest-path transpiler/Cargo.toml --bin verus-transpile
```

### 5.2 Run each passing protocol model-check

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/TwoPhase/twophase.rs \
  --types src/protocol/TwoPhase/types.rs \
  --model transpiler/tests/model_check_fixtures/twophase_small.model.toml \
  --search bfs \
  --json-report
```

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/PrimaryBackup/primarybackup.rs \
  --types src/protocol/PrimaryBackup/types.rs \
  --model transpiler/tests/model_check_fixtures/primarybackup_small.model.toml \
  --search bfs \
  --json-report
```

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/LeaderElection/election.rs \
  --types src/protocol/LeaderElection/types.rs \
  --model transpiler/tests/model_check_fixtures/leaderelection_small.model.toml \
  --search bfs \
  --json-report
```

```bash
transpiler/target/debug/verus-transpile model-check \
  --input src/protocol/Paxos/paxos.rs \
  --types src/protocol/Paxos/types.rs \
  --model transpiler/tests/model_check_fixtures/paxos_small.model.toml \
  --search bfs \
  --json-report
```

### 5.3 Run liveness/fairness fixtures

```bash
transpiler/target/debug/verus-transpile model-check \
  --input transpiler/tests/model_check_fixtures/liveness_avoidable_cycle.protocol.rs \
  --types transpiler/tests/model_check_fixtures/liveness_avoidable_cycle.types.rs \
  --model transpiler/tests/model_check_fixtures/liveness_avoidable_cycle_violated.model.toml \
  --search bfs \
  --json-report
```

```bash
transpiler/target/debug/verus-transpile model-check \
  --input transpiler/tests/model_check_fixtures/liveness_avoidable_cycle.protocol.rs \
  --types transpiler/tests/model_check_fixtures/liveness_avoidable_cycle.types.rs \
  --model transpiler/tests/model_check_fixtures/liveness_avoidable_cycle_strong_fairness.model.toml \
  --search bfs \
  --json-report
```

```bash
transpiler/target/debug/verus-transpile model-check \
  --input transpiler/tests/model_check_fixtures/liveness_forced.protocol.rs \
  --types transpiler/tests/model_check_fixtures/liveness_forced.types.rs \
  --model transpiler/tests/model_check_fixtures/liveness_forced_unfair.model.toml \
  --search bfs \
  --json-report
```

```bash
transpiler/target/debug/verus-transpile model-check \
  --input transpiler/tests/model_check_fixtures/liveness_forced.protocol.rs \
  --types transpiler/tests/model_check_fixtures/liveness_forced.types.rs \
  --model transpiler/tests/model_check_fixtures/liveness_forced_strong_fairness.model.toml \
  --search bfs \
  --json-report
```

### 5.4 Re-run automated evidence directly

```bash
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_primarybackup_helper_call_branches_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_twophase_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_leader_election_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_paxos_bounded_run -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_liveness_fixtures_cover_fairness_and_non_fairness_outcomes -- --nocapture
cargo test --manifest-path transpiler/Cargo.toml --test integration test_model_check_differential_vs_tlc_wrapper_outcomes_shared_small_models -- --nocapture
```

## 6. Update rules (strict)

- Never mark a protocol as source-first supported without checked-in model + automated evidence.
- Keep exact-mode results and lossy-mode results separate.
- For failures, record the first blocker and the next concrete code task.
- For every capability change, update both:
  - this status file
  - `TODO.md` Phase 33 checklist
- Do not replace missing evidence with prose claims.
