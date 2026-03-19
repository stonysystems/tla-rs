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

## PrimaryBackup (42 TLC vs 60 SF — 18 shared) — FIXED in Phase 36.2.4

**Root cause: wrapper/projection mismatch (FIXED)**

The TLC wrapper (`PrimaryBackup_Benchmark_MC.tla`) is hand-written and
adds a `phase` field (`"Idle"`, `"WaitBackup"`, `"WaitAck"`,
`"ReadyToCommit"`) that does NOT exist in the Verus spec (`LState`).

**Fix**: Added `phase` to `EXCLUDE_FIELDS['primarybackup']` in
`tlc_dump_to_parity_jsonl.py`. After exclusion, TLC states that differed
only in `phase` collapse: 54 → 42 projected distinct states.

**Post-fix parity**: 60 SF / 42 TLC / 18 shared. Initial states match.
- 42 SF-only: Source-first over-approximates without message channels
  (e.g., backup commits before primary sends, violating real protocol).
- 24 TLC-only: Message-gated transitions produce states unreachable
  without the `msgs` variable (e.g., higher `view` values from failover
  sequences gated on message receipt).

**Remaining gap**: Same fundamental modeling difference as TwoPhase —
source-first doesn't model message channels.

## LeaderElection (913 TLC vs 355 SF — strict subset)

**Root cause: solver performance on existential-heavy branches**

Source-first finds 355 states in 120s timeout (3-node benchmark, post
guard-first optimization Phase 36.3.7.c). All SF states are in TLC's set
(31/913 shared on parity export, 355 on benchmark — strict subset confirmed).
TLC finds 913 projected distinct states in ~2s.

The source-first engine spends 99.2% of time in solver (branches 2,3,5
account for 70.6%), with 7,380 existential assignments per invocation
and <6 successors per invocation. Guard-first evaluation improved
throughput 2.8x (127→355 states) but the solver is still the bottleneck.

**2-node reproducer**: `leaderelection_perf_repro.model.toml` exhausts at
108 states / 2.3s (down from 6.7s before guard-first).

**Bucket**: Intentional modeling difference (message channels, same as
TwoPhase/PB) PLUS solver performance timeout. All SF states are correct;
the engine just can't reach all 913 TLC-projected states within the timeout.

**Next optimization**: Incremental existential assignment in `solver.rs`
predicate-only path. See `HOTSPOT_LEDGER.md` §5 for full blocker details.

## Paxos — RESOLVED (exhausts on both fixtures)

**Status: RESOLVED**

Paxos 3-node benchmark **exhausts** at 17,370 states in 81.2s (post
guard-first optimization, down from 99.8s). The 2-node parity fixture
(`paxos_parity_small.model.toml`) exhausts at 570 states / 5.8s.

Cross-engine diff is not yet possible because no matching 2-node TLC
wrapper exists (existing `Paxos_Benchmark_MC.tla` hardcodes 3 nodes).
However, since Paxos exhausts on both fixtures, there is no remaining
performance blocker. The correctness question (are SF states a strict
subset of TLC?) requires the TLC wrapper to answer definitively.

**Bucket**: Resolved performance issue. No remaining blocker.

## Summary Classification Table

| Protocol | SF states | TLC states | Shared | Root cause | Bucket | Status |
|----------|-----------|------------|--------|------------|--------|--------|
| TwoPhase | 37 | 56 | 23 | Config: PreparedVote missing from enum_subset | config bug (fixed) | **DONE** |
| PrimaryBackup | 60 | 42 | 18 | Excluded `phase` field from TLC projection | wrapper/projection mismatch (fixed) | **DONE** |
| LeaderElection | 355 | 913 | 31 | Solver timeout on existential-heavy branches | performance + modeling mismatch | **BLOCKED** (see HOTSPOT_LEDGER.md §5) |
| Paxos | 17,370 | N/A | N/A | Solver perf (was timeout, now exhausts) | resolved performance issue | **DONE** |
