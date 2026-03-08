# TLC vs Source-first Benchmark Comparison

Generated: 2026-03-08
Git rev: a7f5ea5

## Side-by-side Results

| Protocol | Engine | Result | States | Distinct | Depth | Transitions | Wall (s) |
|----------|--------|--------|--------|----------|-------|-------------|----------|
| TwoPhase | source-first | ok (exhausted) | 8 | 8 | 3 | 24 | 79 |
| | TLC | *pending* | — | — | — | — | — |
| PrimaryBackup | source-first | ok (exhausted) | 60 | 60 | 7 | 169 | 190 |
| | TLC | *pending* | — | — | — | — | — |
| LeaderElection | source-first | BLOCKED | — | — | — | — | — |
| | TLC | *pending* | — | — | — | — | — |
| Paxos | source-first | BLOCKED | — | — | — | — | — |
| | TLC | *pending* | — | — | — | — | — |

## Source-first Detailed Results

### TwoPhase (2 RMs)
- **State space**: 8 states, fully exhausted (BFS, depth 3)
- **Safety invariants**: 3/3 pass (NoCommitAbortOverlap, CommittedSubsetPrepared, TmCommittedRequiresAllPrepared)
- **Performance**: 79s wall clock, 1,038,336 candidate evaluations, 64 fallback branch solves
- **Successor mode**: 100% enumeration fallback (0 direct-assignment solves)

### PrimaryBackup (max_log=1, values={0,1})
- **State space**: 60 states, fully exhausted (BFS, depth 7)
- **Safety invariants**: 3/3 pass (NoPendingImpliesClearedValue, UnackedImpliesPending, InactiveStateIsQuiescent)
- **Performance**: 190s wall clock, 2,764,800 candidate evaluations, 480 fallback branch solves
- **Successor mode**: 100% enumeration fallback (0 direct-assignment solves)

### LeaderElection (3 nodes) — BLOCKED
- Candidate enumeration evaluates 880K candidates in 76s with 0 valid transitions found.
- Requires constraint-aware successor computation.

### Paxos (3 nodes, quorum=2) — BLOCKED
- Candidate enumeration evaluates 327K candidates in 27s with 0 valid transitions found.
- Requires constraint-aware successor computation.

## State-count Semantics

State-count semantics differ between engines:
- **Source-first** counts states on the centralized Verus `LState` directly. All states are canonical-deduplicated, so states = distinct states.
- **TLC** counts states on the TLA+ wrapper, which may include additional message-channel variables. TLC reports both "generated" (total) and "distinct" (after hash-compaction) state counts separately.

Direct state-count comparison requires normalizing for wrapper variables. Depth and invariant pass/fail are directly comparable.

## Blockers

1. **TLC side**: Requires Java 11+ (system has Java 1.8). TLA+ wrappers and configs are checked in and ready.
2. **LeaderElection & Paxos source-first**: Blocked on candidate enumeration scalability. The source-first engine uses brute-force candidate enumeration for predicate-only branches, which cannot efficiently find valid transitions for multi-node models with complex guard predicates.

## Configs & Replay

- Source-first configs: `transpiler/tests/model_check_fixtures/benchmarks_1h/*.model.toml`
- TLC wrappers: `transpiler/tla_test_workspace/transpiler_generated_tla_with_properties/benchmarks_1h/`
- Replay: `scripts/run_model_check_benchmarks.sh`, `scripts/run_tlc_benchmarks.sh`, `scripts/compare_tlc_vs_source_first.sh`
