# t1_01_paxos — rewrite notes

**Source**: `tlaplus/Examples` `specifications/Paxos/Paxos.tla`
**Pinned commit**: `adccef97931d44120a64ba88054b5ab085f8c50d`
**Clean-distance at intake**: 1 (C5)
**Status**: `clean.tla` written, linter accepts, TLC checked.
**Reference**: `src/protocol/Paxos/paxos.rs` (review aid, never byte-diffed)

The MVP case. Paxos is the killer demo for the claim that a clean global TLA+
spec projects to a single-process Verus spec, and it is the first corpus case
that needs **P4 (quorum → counting)**.

## Which variable is the network (C4)

`msgs`, already a set in the original. The rewrite adds `src` and `dst` to every
message: the original broadcasts by leaving messages unaddressed and letting any
acceptor read any message, which a projected node cannot do.

**Messages are never removed**, exactly as in the original ("Messages are never
removed from `msgs` … receipt of the same message twice is therefore allowed").
Consuming them would be a different protocol — and, as the first draft of this
rewrite found, would deadlock: a state with an empty network enables nothing.

## The anonymous leader (C5) — decision 1

The original's `Phase1a(b)` and `Phase2a(b, v)` are performed by "the ballot b
leader", which is not a node in the spec. This is the single C5 violation the
linter reported, and it is a design question rather than a defect: the spec
deliberately abstracts the leader away.

**Decision: every acceptor may lead a ballot.** `Phase1a(a, b)` and
`Phase2a(a, v)` are now actions of node `a`, with the leader's bookkeeping
(`leaderBal`, `promises`, `promiseBal`, `promiseVal`, `proposed`) added as
per-node state. This is also what the hand-written tla-rs Paxos does — it models
"a single acceptor + proposer combined node" — so the two can be compared.

The alternative, a separate `Proposer` node set, is out: C5 requires a single
node set, and a spec with two would not project.

## Quorum → counting (P4) — decision 2

This is the heart of the rewrite. The original's `Phase2a`:

```tla
\E Q \in Quorum :
   LET Q1b == {m \in msgs : m.type = "1b" /\ m.acc \in Q /\ m.bal = b}
   IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
       /\ \/ Q1bv = {} \/ \E m \in Q1bv : m.mval = v /\ ...
```

scans the entire message set for a quorum's worth of replies and picks the
highest-ballot vote among them. A node cannot read the network that way.

**Decision: the leader accumulates.** `Phase1bReply(a, m)` adds `m.src` to
`promises[a]` and keeps the highest `(mbal, mval)` it has been told about; the
guard becomes `IsMajority(promises[a])`, i.e.
`Cardinality(promises[a]) * 2 > Cardinality(Acceptor)`.

Two consequences worth stating:

- The abstract `Quorum` constant is gone, replaced by a concrete majority test.
  The original's `QuorumAssumption` (any two quorums intersect) is what makes
  Paxos safe, and a majority test satisfies it — so this is a specialisation,
  not a weakening.
- "Highest ballot among the replies" becomes "highest ballot seen so far", which
  is the same value once the quorum's replies have all arrived, and is what an
  implementation actually does.

## Safety, restated

The original's safety comes from a refinement mapping onto module `Voting`
(`V!ShowsSafeAt`, `INSTANCE Voting`), which is not part of the clean subset. The
rewrite states the property directly over the votes acceptors recorded:

```tla
ChosenAt(b, v) == IsMajority({a \in Acceptor : maxVBal[a] = b /\ maxVal[a] = v})
Consistency == \A b1, b2, v1, v2 : ChosenAt(b1,v1) /\ ChosenAt(b2,v2) => v1 = v2
```

## Semantic-fidelity claim (V2)

TLC 2.19, `Acceptor = {a1, a2, a3}`, `Value = {v1, v2}`, `MaxBallot = 1`:

| | result |
|---|---|
| distinct states | 4,843,318 |
| depth | 26 |
| `TypeOK` | holds |
| `Consistency` | holds |

The original is **not** checked side by side here, and that is a real gap: its
correctness is the `Voting` refinement, so it has no directly checkable safety
property and there is no common observable to compare against. What this run
establishes is that the rewrite is a *correct Paxos*, which is the property the
rewrite had to preserve. A behaviour-level comparison needs the spec-vs-spec
comparator planned in 53.6.

The first draft, which consumed messages on receipt, was refuted by TLC with a
deadlock — the check has already caught one error in this rewrite.

## Translator gaps this case exposed

`clean-tla` reports three, and all three are the *point* of having a tier-1 case:

1. **`Value` is an uninterpreted CONSTANT set**, so the projection cannot read an
   element type off it. Values here are opaque identifiers, and the hand-written
   tla-rs Paxos represents them as `int`.
2. **Primed updates inside a conditional**: `Phase1bReply` has
   `IF m.mbal > promiseBal[a] THEN promiseBal' = … ELSE promiseBal' = …`. The
   conjunct classifier only handles a top-level `x' = e`. This is an extremely
   common TLA+ shape and has to be supported.
3. `IsMajority` itself — the counting rule (P4) that no tier-0 case needed.

## Golden review (before freezing golden.rs)

Not yet done: the golden waits on the three gaps above, since it has to be the
translator's actual output.

## Reproducing the TLC run

```bash
mkdir paxos && cp clean.tla paxos/PaxosClean.tla
cat > paxos/PaxosClean.cfg <<'EOF'
CONSTANTS
  Value = {v1, v2}
  Acceptor = {a1, a2, a3}
  MaxBallot = 1
SPECIFICATION Spec
INVARIANTS TypeOK Consistency
EOF
(cd paxos && java -cp tla2tools.jar tlc2.TLC -workers 8 PaxosClean)
```
