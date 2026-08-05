# The 36 RSL `skip_functions`, classified

*Phase 54.15. Written 2026-08-05.*

"RSL is not fully auto-generated" is the standing limitation in the README, and the
36 entries in the RSL `skip_functions` lists are what backs it. Read as one list they
look like 36 units of debt. They are not, and this note records what they actually are
so that Phase 42 can be bounded honestly.

The classification below was written against the 30 entries that existed when Phase
54.15 ran. Phase 42.8.c.2.iv.J.3.d then added 6 more, all hand-implemented; they have
their own section at the end. Totals throughout are stated for all 36.

## The classification is in the config, not in intent

The task as originally written asked for a split into **trust boundary** (never
generated, by design) versus **capability gap** (should be generated, transpiler
cannot yet). Both categories are real, but the primary split turns out to be recorded
in the transpile configs already, and it cuts the list exactly in half.

Each `*_transpile.toml` has two lists that overlap:

- `skip_functions` — the transpiler does not translate the body.
- `no_stub_functions` — the transpiler does not even emit a stub, because something
  else supplies the function.

**21 of the 36 are in both** (15 classified below, plus the 6 added later). For those, a proven hand-written implementation already
exists, in `src/protocol/RSL/acceptor_manual.rs` and
`src/protocol/RSL/executor_manual.rs` (`manual_code = …` in the acceptor config points
at the first). These are not missing code. They are code that exists and is verified,
written by hand rather than generated.

**15 are in `skip_functions` only.** For those a stub *is* emitted and discharged via
`--proof-fallback`. These are the real "not generated" set, and this half did not
change when the 6 were added.

That distinction matters because it halves the apparent debt, and because the two
halves need completely different work: bucket A needs nothing unless one wants to
*replace* working proven code with generated code; bucket B is where generation is
genuinely absent.

## Bucket A — hand-implemented (`skip_functions` ∩ `no_stub_functions`), 15 of 21

| module | function |
|---|---|
| acceptor | `LAcceptorInit`, `LAcceptorProcess1a`, `LAcceptorProcess2a`, `LAcceptorProcessHeartbeat`, `LAcceptorTruncateLog`, `LAddVoteAndRemoveOldOnes`, `RemoveVotesBeforeLogTruncationPoint` |
| executor | `GetPacketsFromReplies`, `LClientsInReplies`, `LExecutorExecute`, `RepliesAreReplyType`, `UpdateNewCache` |
| replica | `ExtractSentPacketsFromIos`, `SpontaneousClock`, `SpontaneousIos` |

The three replica entries are the IO/clock framework surface — the same boundary
IronFleet leaves trusted, and the clearest "never generate this" cases in the list.
The acceptor and executor entries are protocol logic that happens to have been written
by hand first; several are the quantifier-defined map constructions
(`LAddVoteAndRemoveOldOnes`, `UpdateNewCache`) the original task singled out.

## Bucket B — stub-emitted (`skip_functions` only), 15

| module | function | reading |
|---|---|---|
| replica | `LSchedulerNext`, `LReplicaNextProcessPacket`, `LReplicaNextProcessPacketWithoutReadingClock`, `LReplicaNextReadClockAndProcessPacket`, `LReplicaNoReceiveNext`, `LReplicaNextProcess1b`, `LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints` | **trust boundary** — the host event loop and its packet/clock dispatch |
| proposer | `LProposerMaybeNominateValueAndSend2a`, `LProposerNominateNewValueAndSend2a`, `LProposerNominateOldValueAndSend2a` | **capability gap** — composite send-actions; Raft generates comparable ones (`CHandleAppendResponse`, `CTryAdvanceCommitIndex`) |
| learner | `LLearnerProcess2b`, `LLearnerForgetOperationsBefore` | **capability gap** |
| election | `BoundRequestSequence`, `ElectionStateReflectReceivedRequest` | **capability gap** |
| broadcast | `BuildLBroadcast` | **capability gap** — recursive sequence walk |

So the trust boundary is **7 + the 3 IO/clock entries in bucket A = 10**, matching the
original estimate of "roughly 8–10". The capability gap is **8**, not 20-something.

## A hypothesis that the evidence killed

`BoundRequestSequence` is `if bound is finite && 0 <= n < s.len() { s.subrange(0, n) }
else { s }`. `LAcceptorTruncateLog` is an if/else over a struct update. These look
easily generatable today — the transpiler has advanced a great deal since the skips
were added — which suggested a third bucket: *stale skips, generatable now, never
re-attempted*.

Tested rather than assumed, by removing the entry from a **copy** of the config in
`/tmp` and generating there (nothing checked in was touched):

- `BoundRequestSequence` → the transpiler emits a body, and that body is
  `assume(false)`. It is a real capability gap, not a stale skip.
- The two acceptor trials emitted nothing at all — **not** evidence about the
  transpiler, but an artefact of the measurement: those names are also in
  `no_stub_functions`, so removing them from `skip_functions` alone leaves neither a
  generated body nor a stub. That failed measurement is what surfaced the two-list
  structure this whole note is built on.

No stale-skip bucket, then. The binary split holds — but only after the
hand-implemented half is separated out first.

## What this bounds

- Full regeneration of RSL is **not** the goal and never was: 10 of the 36 are a
  deliberate trust boundary and 21 already have verified hand-written
  implementations.
- The genuine transpiler backlog RSL implies is **8 functions**, in four modules.
- The README limitation is more accurately stated as: *the RSL host event loop and IO
  dispatch are trusted, as in IronFleet; a further 8 protocol actions are hand-written
  because the transpiler cannot yet generate quantifier-defined map constructions,
  recursive sequence walks, or composite send-actions in this shape.*

## Phase 42.8.c.2.iv.J.3.d — replica actions with hand-written proofs (6)

Added 2026-08-05 so replica can regenerate. These are **not** translation gaps:
each has a complete, verified body in `src/generated/RSL/replica_gen.rs`. What
the transpiler cannot reproduce is the *proof* — the bodies carry
`broadcast use vstd::std_specs::hash::group_hash_axioms, ...` and explicit lemma
calls such as `lemma_creplycache_get`, followed by several `assert`s that
discharge the postcondition.

Listing them in `skip_functions` (and `no_stub_functions`, so no
`unimplemented!()` stub is emitted) means fresh output omits them and the merge
carries the proven bodies through untouched.

| function | why the generated proof fails |
|---|---|
| `LReplicaNextProcessRequest` | reply-cache reasoning needs `lemma_creplycache_get` and a `broadcast use` of the hash axioms |
| `LReplicaNextProcess2a` | same shape, over the acceptor's vote state |
| `LReplicaNextSpontaneousMaybeMakeDecision` | learner-state lemmas |
| `LReplicaNextSpontaneousMaybeExecute` | executor-state lemmas |
| `LReplicaNextReadClockMaybeSendHeartbeat` | timing/ballot reasoning |
| `LReplicaInit` | its `recommends` becomes a `requires` the caller in `ReplicaImpl.rs` does not establish |

**The alternative was measured and rejected.** Listing all 18 actions in
`proven_functions` instead makes replica reach `1040 verified, 6 errors`; backing
the 6 off *there* leaves them carrying `assume(false)`, which buys 11 more
trigger notes (66 vs 77) by converting six proven actions into assumed ones.
Trading verification strength for a trigger-note count is the same
metric-gaming that Phase 54 rejects `#![auto]` for, so the notes stay.

Removing an entry from this list requires teaching the transpiler to emit those
proofs — which is the route `CLAUDE.md` prescribes.
