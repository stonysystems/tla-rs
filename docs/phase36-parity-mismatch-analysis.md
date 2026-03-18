# Phase 36.2.1: Parity Mismatch Classification

Analysis of cross-engine state-set mismatches between source-first and TLC
on the shared small models, using the Phase 36.1 parity harness.

## TwoPhase (56 TLC vs 8 SF — 8 shared, 48 TLC-only)

**Root cause: successor-generation bug**

All 8 source-first states are a strict subset of TLC's projected states.
Initial states match. The 48 TLC-only states all have non-empty
`rm_prepared` or `tm_prepared`, meaning the Prepare/Commit paths were
never explored by source-first.

Branch telemetry confirms:
- `LRMReceivePrepare` (branch_1): invoked 8 times, **0 successful successors**
- `LTMRcvPrepared` (branch_3): 0 successors (correctly — requires rm_prepared non-empty)
- `LTMSendCommit` (branch_4): 0 successors (correctly — requires tm_prepared == c.rm)
- `LRMReceiveCommit` (branch_6): 0 successors (correctly — requires rm_prepared non-empty)

The root cause is branch_1 (`LRMReceivePrepare`): the solver's direct
assignment reports 8 "hits" but produces 0 successors. This branch has:

```
exists |rm: int, sent_packets: Seq<LTPCMessage>|
    LRMReceivePrepare(s, s_, c, rm, sent_packets)
```

Where `LRMReceivePrepare` requires:
- `c.rm.contains(rm)` — rm ∈ {0, 1}
- `!s.rm_prepared.contains(rm)` — must not be prepared (satisfied at init)
- `!s.rm_aborted.contains(rm)` — must not be aborted
- `s_.rm_prepared == s.rm_prepared.insert(rm)` — update
- `sent_packets == seq![LTPCMessage::PreparedVote { rm }]` — output

The solver likely fails on constructing `PreparedVote { rm }` (an enum
variant with an `int` field) or on the existential `rm` resolution when
`c.rm` is a set. Investigation needed in the branch solver's handling of:
1. Enum variant construction with field values
2. Set membership constraints (`c.rm.contains(rm)`)
3. `sent_packets` output variable solving

**Fix priority: HIGH** — this is the simplest protocol and the bug blocks
all Prepare-path exploration.

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
| TwoPhase | 8 | 56 | 8 | Branch solver fails on PreparedVote enum | successor-generation bug | HIGH |
| PrimaryBackup | 60 | 54 | 0 | Hand-written TLC wrapper adds `phase` field | wrapper/projection mismatch | MEDIUM |
| LeaderElection | 2 | 913 | 2 | Solver timeout during candidate enumeration | successor-generation bug (perf) | MEDIUM |
| Paxos | ~75 | 3M+ | N/A | State space too large for current engine | successor-generation bug (perf) | LOW |
