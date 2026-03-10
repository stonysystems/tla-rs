# TLC vs Source-first Benchmark Comparison

Generated: 2026-03-08 16:25 UTC
Git rev: fd8967f

Source-first run: 2026-03-08 (from checked-in artifacts)
TLC run: 2026-03-08 16:15-16:25 UTC

## Column Meanings

- `States (gen)`: total states generated before deduplication. For TLC this includes revisited states.
- `Distinct`: unique states after deduplication/fingerprinting.
- `Depth`: maximum search depth reached in the run.
- `Wall (s)`: wall-clock elapsed time in seconds.
- For source-first, `States (gen)` is shown as `—` because the checked-in source-first benchmark artifacts currently expose deduplicated explored states (`summary.states`), not a separate generated-state counter.

## Side-by-side Results

Both engines use the same modeled constants/domains per protocol. TLC uses 1 worker on 64-core machine. Source-first uses single-threaded BFS with exact canonical dedup.

| Protocol | Engine | Result | States (gen) | Distinct | Depth | Wall (s) |
|----------|--------|--------|--------------|----------|-------|----------|
| TwoPhase | source-first | ok (exhausted) | — | 8 | 3 | 79 |
| | TLC | pass (exhausted) | 150 | 64 | 9 | 1 |
| PrimaryBackup | source-first | ok (exhausted) | — | 60 | 7 | 190 |
| | TLC | pass (exhausted) | 86 | 54 | 10 | 1 |
| LeaderElection | source-first | BLOCKED | — | — | — | — |
| | TLC | pass (exhausted) | 100,636 | 9,337 | 13 | 2 |
| Paxos | source-first | BLOCKED | — | — | — | — |
| | TLC | pass (exhausted) | 25,288,515 | 3,005,604 | 37 | 375 |

## Analysis

### TwoPhase (2 RMs)

Both engines fully exhaust the state space and find no invariant violations.

- **TLC**: 64 distinct states, depth 9, 1s. Reports 150 generated states (includes revisited states).
- **Source-first**: 8 distinct states, depth 3, 79s. The 8-vs-64 state-count difference is due to state representation: source-first uses a centralized `LState` without a separate message set variable, while TLC tracks `<<state, constants, msgs>>` as three separate variables. The message set alone introduces many additional distinct states.
- **Performance ratio**: TLC is ~79x faster. Source-first overhead comes from brute-force candidate enumeration (1,038,336 evaluations for 8 states).

### PrimaryBackup (max_log=1, values={0,1})

Both engines fully exhaust the state space and find no invariant violations.

- **TLC**: 54 distinct states, depth 10, 1s. Reports 86 generated states.
- **Source-first**: 60 distinct states, depth 7, 190s. The state-count is roughly similar (60 vs 54), differing because source-first and TLC model message delivery slightly differently.
- **Performance ratio**: TLC is ~190x faster. Source-first overhead from 2,764,800 candidate evaluations.

### LeaderElection (3 nodes)

- **TLC**: 9,337 distinct states, depth 13, 2s. Fully exhausted, all 3 invariants pass.
- **Source-first**: BLOCKED. Candidate enumeration evaluates 880K candidates in 76s without finding valid transitions. The multi-node action guards create a combinatorial space that brute-force enumeration cannot efficiently navigate.

### Paxos (3 nodes, quorum=2, values={0,1,2}, ballots={0,1,2,3})

- **TLC**: 3,005,604 distinct states (25.3M generated), depth 37, 375s (6min 15s). Fully exhausted, all 3 invariants pass.
- **Source-first**: BLOCKED. Same enumeration scalability issue as LeaderElection, but worse due to larger per-node state (accepted_bal, accepted_val, promised_bal, proposer fields, etc.).

## State-count Semantics

State-count semantics differ between engines:
- **Source-first** counts states on the centralized Verus `LState` directly. All states are canonical-deduplicated, so states = distinct states. Source-first does not track a separate message set variable.
- **TLC** counts states on the TLA+ wrapper (`<<state, constants, msgs>>`), which includes message-channel variables. TLC reports both "generated" (total including revisits) and "distinct" (fingerprint-deduplicated) state counts separately.

Direct state-count comparison requires normalizing for wrapper variables. Invariant pass/fail and exhaustion results are directly comparable.

## Key Findings

1. **Both engines agree on safety**: For the 2 protocols where both run (TwoPhase, PrimaryBackup), both engines fully exhaust the state space and report no invariant violations. This provides cross-validation of the model-checking correctness.

2. **TLC is dramatically faster**: 79x on TwoPhase, 190x on PrimaryBackup. Source-first overhead is dominated by brute-force candidate enumeration. TLC uses symbolic evaluation and efficient state-space exploration.

3. **Source-first has scalability blockers**: LeaderElection and Paxos cannot produce any transitions because the candidate enumeration cannot efficiently satisfy multi-node guard predicates. TLC handles both (9K and 3M distinct states respectively).

4. **The gap is algorithmic, not engineering**: Source-first needs constraint-aware successor computation (constraint propagation, symbolic evaluation, or SMT-backed solving) to handle multi-node protocols. Increasing enumeration limits alone will not close the gap.

## Blockers

1. **LeaderElection & Paxos source-first**: Blocked on candidate enumeration scalability. The source-first engine uses brute-force candidate enumeration for predicate-only branches, which cannot efficiently find valid transitions for multi-node models with complex guard predicates.

## Tool Versions

- **TLC**: 2026.03.05.210854 (rev: ec1a488), Java 17.0.18, 1 worker, `-Xmx4g`
- **Source-first**: `verus-transpile model-check` (debug build), exact canonical dedup, BFS

## Configs & Replay

- Source-first configs: `transpiler/tests/model_check_fixtures/benchmarks_1h/*.model.toml`
- TLC wrappers: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/`
- Replay: `scripts/run_model_check_benchmarks.sh`, `TLA2TOOLS=~/tla2tools.jar scripts/run_tlc_benchmarks.sh`, `scripts/compare_tlc_vs_source_first.sh`
