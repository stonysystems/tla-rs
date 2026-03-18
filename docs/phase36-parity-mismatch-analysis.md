# Phase 36.2.1: Parity Mismatch Classification

Analysis of cross-engine state-set mismatches between source-first and TLC
on the shared small models, using the Phase 36.1 parity harness.

## TwoPhase (56 TLC vs 37 SF — 23 shared) — FIXED in Phase 36.2.3

**Root cause: model config missing `PreparedVote` variant (FIXED)**

The `twophase_benchmark.model.toml` config had `[quantifiers.types.LTPCMessage]`
with `enum_subset` listing only `["Prepare", "Commit", "Abort"]`, omitting
`PreparedVote`. Since the outer existential `sent_packets: Seq<LTPCMessage>`
is expanded using this domain, the solver never produced assignments containing
`PreparedVote { rm }`, causing the `LRMReceivePrepare` branch to always fail
the deferred constraint check.

**Fix**: Added `"PreparedVote"` to the enum_subset variant list. This causes
the domain expansion to include `PreparedVote{rm:0}` and `PreparedVote{rm:1}`
as possible sent_packets values, unblocking all prepare/commit transitions.

**Post-fix parity**: 37 SF states vs 56 TLC states, 23 shared.
- 14 SF-only states: Source-first over-approximates because it doesn't model
  message channels. These states are reachable via transitions that the TLC
  wrapper would gate on message presence (e.g., `LRMReceiveCommit` without
  a `CommitMsg` in `msgs`). Some violate safety invariants.
- 33 TLC-only states: TLC explores states with message-channel combinations
  that the source-first spec can't represent (no `msgs` field). These include
  states with distinct `msgs` values but identical protocol state — after
  projecting out `msgs`, many collapse, but some remain due to different
  reachability through message-gated transitions.

**Remaining gap**: The 14 + 33 non-shared states are a fundamental modeling
difference (message channels), not a solver bug. Full parity would require
either adding message channel modeling to the source-first spec or using
the auto-generated relational wrapper (which doesn't include `msgs`).

## PrimaryBackup (54 TLC vs 60 SF — 0 shared)

**Root cause: wrapper/projection mismatch**

Zero shared states despite both engines exhausting the state space. The
TLC wrapper (`PrimaryBackup_Benchmark_MC.tla`) is **hand-written** and
adds a `phase` field (`"Idle"`, `"WaitBackup"`, `"WaitAck"`,
`"ReadyToCommit"`) that does NOT exist in the Verus spec (`LState` in
`src/protocol/PrimaryBackup/types.rs`).

This `phase` field is wrapper-level bookkeeping that decomposes the
source-first spec's atomic transitions into finer-grained message-passing
steps. It is NOT semantically part of the protocol state — it's an
artifact of the hand-written TLC wrapper's modeling choice.

**Consequence**: The TLC and source-first specs model the protocol at
different granularity levels. Parity comparison requires either:
1. Projecting out `phase` from TLC states before comparison, OR
2. Regenerating the TLC wrapper from the same Verus spec using the
   automated `generate-mc-wrapper` pipeline

**Fix priority: MEDIUM** — this is a normalization/projection issue, not a
semantic bug. Fix by either:
- Adding `phase` to the TLC normalizer's exclusion list, OR
- Regenerating the wrapper from the Verus spec (preferred long-term)

## LeaderElection (913 TLC vs 2 SF — 2 shared, 911 TLC-only)

**Root cause: successor-generation bug (performance/timeout)**

Source-first finds 2 states (1 initial + 1 successor) before timing out
at 30s. The 2 states it finds are in TLC's set. TLC finds 913 projected
distinct states (from 9,337 raw states) in ~2s.

The source-first engine spends almost all time in successor solving
(30s for just 2 states), indicating a solver scalability issue — likely
exponential candidate enumeration for branches with multiple existential
variables over the 3-node domain.

**Fix priority: MEDIUM** — this is a performance bug, not a correctness
bug. The 2 states source-first finds are correct; it just can't find
more within the timeout.

## Paxos (3M+ TLC vs ~75 SF at 1h — not compared)

**Status: not yet diffable**

Paxos source-first times out after finding ~75 states in 1 hour. TLC
finds 3M+ states. The state-space gap is too large for meaningful parity
comparison on the benchmark config. A much smaller Paxos config is needed
for parity work.

**Fix priority: LOW** — requires both a smaller model config and solver
performance improvements.

## Summary Classification Table

| Protocol | SF states | TLC states | Shared | Root cause | Bucket | Priority |
|----------|-----------|------------|--------|------------|--------|----------|
| TwoPhase | 37 | 56 | 23 | **FIXED** (config: PreparedVote missing from enum_subset) | config bug (fixed) | DONE |
| PrimaryBackup | 60 | 54 | 0 | Hand-written TLC wrapper adds `phase` field | wrapper/projection mismatch | MEDIUM |
| LeaderElection | 2 | 913 | 2 | Solver timeout during candidate enumeration | successor-generation bug (perf) | MEDIUM |
| Paxos | ~75 | 3M+ | N/A | State space too large for current engine | successor-generation bug (perf) | LOW |
