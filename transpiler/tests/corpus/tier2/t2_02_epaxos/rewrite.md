# t2_02_epaxos — rewrite notes

**Source**: `efficient/epaxos` `tla+/EgalitarianPaxos.tla`
**Pinned commit**: `ab4dbeae58a7eabcb514865e9ccf1ab0386abfc3`
**Clean-distance at intake**: 3 (all C1)
**Status**: `clean.tla` written, linter accepts, translated, `golden.rs` passes `verus`, TLC closes the state space.
**Reference**: `reference.rs` = `src/protocol/EPaxos/epaxos.rs` (review aid, never byte-diffed)

## The manifest predicted the wrong thing

The manifest called this "the hardest tier-2 case; do it after Raft is green".
At intake it is the **cleanest**: EPaxos is natively message-passing, so `sentMsg`
is already one set, **C2 and C4 pass untouched**, and the node set `Replicas` is
found. The three findings are all C1 globals.

What it *was* hardest at is the translator — nine defects, every one about
types. They are listed in `golden.rs`'s header against the output they produce.

## The first measurement said 1, and it was wrong

`Next == \/ CommandLeaderAction \/ ReplicaAction` pushes the node quantifier one
level down into 0-ary grouping operators. The linter reported "cannot identify
the node set" and stopped, **never reaching C1 at all**. Fixed by expanding
0-ary *action* operators into `Next` before analysis.

This is the second case mismeasured this way — Jetpack's clean-distance of 2 had
the same cause. **A linter that cannot identify the node set reports a small
number, and a small number reads as "nearly clean".** Both cases now say so in
their notes.

## The slice

The **phase-1 commit path**: propose, pre-accept, collect replies, commit — fast
when the replies agree, slow via an explicit Accept round when they do not.

Out: recovery (`SendPrepare` / `ReplyPrepare` / `PrepareFinalize` /
`TryPreaccept`), execution, and the `executed` log. Recovery is what non-zero
ballots exist for, so ballots collapse to the leader's identity and `ballots` —
a shared counter, one of the three C1 findings — goes with them.

## What the rewrite had to decide

**`committed` is a history variable (C3).** The original keeps
`committed \in [Instances -> SUBSET (...)]` purely so `Nontriviality` and
`Stability` can be stated. Nothing in the protocol reads it. Deleted, and
`Consistency` restated over the replicas' own logs: *no two replicas commit the
same instance with different attributes*. That is the same claim, stated where a
replica can actually check it.

**`proposed` likewise.** It exists so `Nontriviality` can say "nothing committed
was not proposed". The command now arrives as an action parameter, which is what
a client request is.

**Instances become records, not tuples.** The original writes an instance as
`<<cleader, crtInst[cleader]>>`. A record projects to a struct; a tuple would
need a product type the projection does not have. Same information, and the
choice is stated here rather than hidden.

**Quorums → counting (P4), twice.** `FastQuorums(cleader)` and
`SlowQuorums(cleader)` are both sets of subsets. `IsFastQuorum` and
`IsSlowQuorum` count instead — and keeping them *distinct* matters, because the
fast path's larger quorum is exactly what buys the missing round.

**The unanimity test becomes an accumulator.** `Phase1Fast` scans `sentMsg` for
a quorum's worth of replies and asks `\A r1, r2 \in replies : r1.deps = r2.deps
/\ r1.seq = r2.seq`. A replica cannot read the network that way, so `agreed`
stays TRUE only while every reply matches what the leader proposed. Once the
quorum is in, "all replies agreed" is the same fact.

**`MaxSeq` is a new constant.** The original's `seq` is a `Nat` and grows
without bound. It is bounded here the way `MaxBallot` bounds Paxos, and the
actions are *guarded* on staying in range rather than capping the value — a
silent cap would be a different protocol.

The first draft got this wrong in a way TLC caught immediately: it computed
`NextSeq` as `1 + Cardinality(log)` rather than the original's
`1 + Max({t.seq : t \in log})`, and `TypeOK` failed at depth 4. The two agree
only when every sequence number is distinct and dense, which is not something the
protocol guarantees.

## Semantic fidelity (V2)

TLC 2.19, `Replicas = {r1, r2, r3}`, `Commands = {c1}`, `MaxInstance = 1`,
`MaxSeq = 3`, `Cardinality(msgs) <= 4`:

| | |
|---|---|
| states generated | 13,649,944 |
| distinct states | 3,214,576 |
| depth | 47 |
| `TypeOK` | holds |
| `Consistency` | holds |
| state space | **closed** |

`-deadlock` is required for the same reason as Jetpack's: `MaxInstance` bounds
the protocol, so a behaviour that exhausts it legitimately has no successor.

**No side-by-side comparison against the original**, and the reason is the slice
rather than a missing tool: `Consistency` here is stated over `cmdLog`, and the
original's is stated over the `committed` history variable that C3 deletes. The
two specs share `cmdLog` by name, but the original's records carry a `ballot`
field this slice does not have, so the projections are not comparable. This case
stays `golden`, not `green`.

## Reproducing the TLC run

```bash
mkdir ep && cp clean.tla ep/EPaxosClean.tla
cat > ep/EPaxosClean.cfg <<'EOF'
CONSTANTS
  Replicas = {r1, r2, r3}
  Commands = {c1}
  MaxInstance = 1
  MaxSeq = 3
SPECIFICATION Spec
INVARIANTS TypeOK Consistency
CONSTRAINT SmallState
EOF
(cd ep && java -cp tla2tools.jar tlc2.TLC -workers 8 -deadlock EPaxosClean)
```
