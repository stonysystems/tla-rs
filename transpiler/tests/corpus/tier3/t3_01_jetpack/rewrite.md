# t3_01_jetpack — rewrite notes

**Source**: `docs/jetpack_reference/jetpack_raft_composition.tla` (+ `jetpack.tla`, `base_raft.tla`)
**Clean-distance at intake**: 2, **and not comparable to the other cases** — see below
**Status**: `clean.tla` written, linter accepts, translated, `golden.rs` passes `verus`, TLC completed under a bound.
**Reference**: `reference.rs` = Phase 51's partial hand-written spec (review aid, never byte-diffed)

Jetpack is the case the whole project is aimed at. Phase 51 tried to write this
spec by hand and stopped partway: the entry actions (51.9) were never written.
This case is the same protocol produced by the translator instead, which is why
`reference.rs` is here and why `golden.rs`'s header is mostly a comparison
against it.

## Why the clean-distance of 2 means nothing

The linter reported two violations on `original.tla`:

- **C4**: `messages` is only ever updated with `EXCEPT`, so it is a
  per-connection queue structure rather than one message set.
- **C5**: no node set could be identified.

That second finding is the reason the number is meaningless. The composition
module has **no type invariant** — the per-server types live inside the
`INSTANCE`d modules — so the linter never gets far enough to run C1 or C2 at
all. The real distance is unmeasured, and it is large. Reading "2" as "nearly
clean" would be badly wrong; the manifest says so in its notes.

This is the same limitation Raft's rewrite recorded: *the projection needs a
declaration to read an element type from*. Jetpack is the case where it stops
being an inconvenience and becomes the first thing the rewrite has to fix.

## Getting it to parse at all

Two parser gaps, neither of which tiers 0–2 exercised:

- **Set comprehension over more than one binder** —
  `{ [cmd_id |-> id, key |-> k] : id \in CmdId, k \in Key }`.
- **`LAMBDA`** — `SelectSeq(seq, LAMBDA x : x # NoOpCmd)`.

## The slice (R1)

Phase 51's R1, unchanged: the recovery state machine

```
Ready -> Recovery -> AfterBeginRecovery -> AfterPrepare -> AfterAccept -> Ready
```

run by one replica over **fixed membership**. Everything else is out, and each
exclusion has a reason rather than being a convenience:

| Excluded | Why |
|---|---|
| the base protocol (`currentTerm`, `ostate`, `log`, `commitIndex`) | a contract, not part of the recovery layer. `SendBeginRecovery`'s `ostate[i] = ToBeLeader` guard becomes "this replica is Ready", and the environment decides when. |
| client + execution layers | out of the recovery layer; they are what `Resubmit`/`AfterResubmit` exist for, so those go too and `AfterAccept` returns straight to `Ready`. |
| reconfiguration, `old_view`/`new_view`, `oepoch` | **Q2 puts membership change outside the subset.** `oepoch` exists only to order views, so it goes with them. |
| `FastpathQuorum` | a property of the *view*, which is gone. |

## What the rewrite had to decide

**The network (C4).** `messages` is a bag indexed per connection. It becomes one
set of messages tagged `msource`/`mdest`, and **receipt consumes** — Jetpack's
`Discard`/`Reply` remove the message, exactly as Raft's do and unlike Paxos's.
This is the per-spec fact Raft's rewrite learned to check rather than assume.

**Quorum → counting (P4).** The original's
`\E qs \in JQuorum(new_view[i]) : \A s \in qs : br_responses[i][s] /= NilJPool`
quantifies over a powerset of subsets. A replica cannot evaluate that. Each
phase instead accumulates a set of responders and the guard counts it:
`Cardinality(recoverySet[i]) * 2 > Cardinality(Server)`.

**Stored responses → online aggregation.** The original stores every reply in
`br_responses[i]` / `prep_responses[i]` and scans them in the `Complete*`
action, picking the highest `accepted_ballot`. The rewrite keeps
`highestSeenBallot` / `highestSeenValue` and updates them per response. This is
the same value once the quorum's replies are in, and it is what an
implementation does — the same decision Paxos's rewrite made, for the same
reason.

**The reject branches.** The original's `HandlePrepareRequest` and
`HandleAcceptRequest` reply on rejection too (`mok = FALSE`, carrying the
acceptor's own ballot so the proposer can catch up). The slice keeps only the
accepting branch, along with the proposer-side catch-up that consumes it.
Phase 51's hand-written spec made the same cut and says so; this is a
**narrowing**, and a spec that later needs liveness will have to put it back.

## Semantic fidelity (V2)

TLC 2.19, `CmdId = {c1}`, `Key = {k1}`, `MaxBallot = 1`, `Cardinality(msgs) <= 4`:

| | `Server = {s1, s2}` | `Server = {s1, s2, s3}` |
|---|---|---|
| states generated | 9,941,163 | 94,651,129 |
| distinct states | 2,060,998 | 19,536,088 |
| depth | 66 | 78 |
| `TypeOK` | holds | holds |
| `Consistency` | holds | holds |
| state space | **closed** | **closed** |

Both runs **close the state space** — no bound on the search other than the
model's own `MaxBallot` and the `Cardinality(msgs) <= 4` constraint. The
three-server run is the one that matters: at two servers a majority is *both*
replicas, so the quorum logic is degenerate and a broken `IsQuorum` would still
pass. At three it is two of three, and `Consistency` is a real test of the
value-selection rule.

This is a stronger result than `t2_01_raft` has, where the space does not close
at all and only bounded evidence exists.

`-deadlock` is required, and the reason is not a defect: `Ballot` is bounded, so
a behaviour that exhausts it has no successor and TLC's deadlock check fires on
a legitimate terminal state. The first run found exactly that — s1 back in
`Ready` with `jepoch = 1 = MaxBallot`, s2 an acceptor that never started its own
recovery, and an empty network. Nothing is enabled because nothing *should* be.

The original is **not** checked side by side, and that is a real gap, the same
one Paxos has: the composition module's properties are stated over the base
protocol and the client layer, which the slice does not contain, so there is no
common observable. What these runs establish is that the rewrite is a correct
Paxos-style recovery protocol — which is the property the rewrite had to
preserve. A behaviour-level comparison needs the spec-vs-spec comparator planned
in 53.6.

## Translator gaps this case exposed

**None.** `clean.tla` translated on the first attempt, and the output passed
`verus` on the first attempt. That is worth stating plainly, because it is the
first time in the corpus it has happened — and it happened because Raft had
already forced the projection to carry types. Jetpack's `Set<LCommand>` values,
its `LCommand` record, its named enum labels (`Ready == "ready"`) and its
`0 .. MaxBallot` binder are all things Raft paid for.

## V1: the golden verifies

```
verus -V no-solver-version-check golden.rs --crate-type=lib
verification results:: 0 verified, 0 errors
```

A spec-only file has no proof obligations, so this is the typecheck — and on
this corpus the typecheck is what has caught real defects (a missing variant
field, an unbound identifier, an `int`/`nat` mismatch, a predicate-typed
helper), so it is not a formality.

## Reproducing the TLC run

```bash
mkdir jp && cp clean.tla jp/JetpackClean.tla && cp clean.cfg jp/JetpackClean.cfg
(cd jp && java -cp tla2tools.jar tlc2.TLC -workers 8 -deadlock JetpackClean)
```
