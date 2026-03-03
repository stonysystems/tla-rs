# tla-rs Model Checker Status

Last reviewed: 2026-03-03

This is the canonical status page for the source-first `verus-transpile model-check` engine. Keep this file synchronized with `TODO.md` Phase 33 whenever capability, protocol coverage, blockers, or performance claims change.

## Current baseline

Implemented today:

- Source-first ingestion of tla-rs specs from `LInit` / `LNext`
- BFS and DFS exploration
- invariant checking, deadlock checking, and counterexample traces
- TLC-wrapper generation for relational specs when needed
- reduction knobs: canonical dedup, `hash_compaction64`, `symmetry_fields`, and `por_heuristic = "invisible_branch"`
- bounded `leads_to` checking plus branch-label fairness filtering on fully explored graphs

Checked-in automated source-first evidence today:

- `TwoPhase`: bounded run passes
- `PrimaryBackup`: bounded run passes
- `LeaderElection`: bounded run passes
- `Paxos`: bounded run passes
- Tiny liveness/fairness fixtures also pass and exercise `leads_to` reporting

Checked-in test entry points:

- `transpiler/tests/integration.rs:test_model_check_primarybackup_helper_call_branches_bounded_run`
- `transpiler/tests/integration.rs:test_model_check_twophase_bounded_run`
- `transpiler/tests/integration.rs:test_model_check_leader_election_bounded_run`
- `transpiler/tests/integration.rs:test_model_check_paxos_bounded_run`
- `transpiler/tests/integration.rs:test_model_check_liveness_fixtures_cover_fairness_and_non_fairness_outcomes`
- `transpiler/tests/integration.rs:test_model_check_differential_vs_tlc_wrapper_outcomes_shared_small_models`

## Protocol matrix

| Protocol | Checked-in source-first evidence | Current status | Notes |
| --- | --- | --- | --- |
| `RSL` | No | Untracked for source-first | Highest-value missing consensus protocol. Needs checked-in source-first model and blocker audit. |
| `Raft` | No | Untracked for source-first | Safety proof is strong, but source-first model-check status is still missing. |
| `Paxos` | Yes | Bounded pass | Covered by checked-in integration test and fixture model. |
| `VerticalPaxos` | No | Untracked for source-first | Needs model file, exact-mode attempt, and blocker classification. |
| `EPaxos` | No | Untracked for source-first | No checked-in source-first run yet. Existing TLC wrapper notes already warn about large state spaces. |
| `PBFT` | No | Untracked for source-first | No checked-in source-first run yet. Existing TLC wrapper notes already warn about large state spaces. |
| `ChainReplication` | No | Untracked for source-first | Needs checked-in source-first model and automation. |
| `PrimaryBackup` | Yes | Bounded pass | Covered by checked-in integration test and fixture model. |
| `TwoPhase` | Yes | Bounded pass | Covered by checked-in integration test and fixture model. |
| `LeaderElection` | Yes | Bounded pass | Non-consensus control protocol; keep it green while expanding consensus coverage. |

## Known unsupported or incomplete areas

Implementation-backed limitations:

- `transpiler/src/modelcheck/evaluator.rs` still rejects:
  - general `forall`
  - expression-level `exists`
  - `match`
  - struct update expressions
  - bitwise/shift operators
  - non-identifier `let` patterns
- `transpiler/src/modelcheck/evaluator.rs` only supports casts to `int`, `nat`, and `bool`.
- `transpiler/src/modelcheck/domain.rs` only supports concrete built-in container expansion (`Seq`, `Set`, `Map`) and rejects broader generic-domain expansion.
- `transpiler/src/main.rs` currently requires exactly one concrete `LConstants` valuation after config resolution.
- `transpiler/src/modelcheck/solver.rs` can fall back to next-state candidate enumeration for predicate-only/helper branches. This is functionally useful but can explode badly.
- Liveness checking is only reported when the explored graph is complete; incomplete explorations report `liveness.skipped_reason = "incomplete_exploration"`.

Process gaps:

- No checked-in status matrix existed before this file; keep it current.
- No checked-in exact-mode benchmark discipline exists yet for performance claims.
- Several real consensus protocols still have no source-first automation or blocker write-up.

## Required work, in order

1. Close the real semantic blockers.
   Start with protocol-driven gaps: finite-domain quantifiers, `match`, struct updates, multi-valuation constants, and better solving for helper/predicate branches.
2. Build performance discipline before claiming wins.
   Keep exact-mode baselines, separate lossy vs exact runs, and require before/after telemetry for every optimization.
3. Push real consensus protocol coverage.
   Work through `RSL`, `Raft`, `VerticalPaxos`, `EPaxos`, `PBFT`, and `ChainReplication` instead of staying on already-green small protocols.
4. Keep differential evidence where TLC wrappers already exist.
   Shared small models should continue to agree qualitatively between wrapper-based and source-first workflows.

## Rules for updating this file

- Never mark a protocol as supported without a checked-in model plus automated evidence or a checked-in JSON report.
- Record exact-mode and lossy-mode results separately.
- When a protocol still fails, write the first blocker and the next concrete code task.
- When a new feature lands, update both the blocker list and the protocol matrix.
- Do not replace missing evidence with prose.
