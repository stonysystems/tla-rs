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

## Golden review, against the hand-written tla-rs spec

The golden is the translator's actual output, frozen after the review below.
`reference.rs` is `src/protocol/Paxos/paxos.rs` + its `types.rs`, the
hand-written single-process Paxos this project already had. M2's acceptance
criterion names this comparison, so here it is in full.

**State corresponds one-to-one for everything the source spec covers:**

| generated | hand-written | |
|---|---|---|
| `max_bal` | `promised_bal` | highest ballot promised |
| `max_v_bal` | `accepted_bal` | ballot of the last vote |
| `max_val` | `accepted_val` | value of the last vote |
| `leader_bal` | `proposer_bal` | the ballot this node leads |
| `promises` | `promises_rcvd` | acceptors that answered |
| `promise_bal` | `highest_accepted_bal` | highest ballot reported |
| `promise_val` | `highest_accepted_val` | value reported with it |
| `proposed: bool` | `phase: LPhase` | see below |
| — | `accepts_rcvd`, `decided_val`, `proposed_val` | learner state, see below |

Actions correspond as well: `LPhase1a` ↔ `LSend1a`, `LPhase1b` ↔ `LSend1b`,
`LPhase1bReply` ↔ `LRecvPromise`, `LPhase2a` ↔ `LSend2a`, `LPhase2b` ↔
`LSend2b`.

**Three differences, and none of them is the translator being wrong:**

1. **Names.** The generated spec uses the source's vocabulary (`max_bal`), the
   hand-written one uses protocol vocabulary (`promised_bal`). Preserving the
   source's names is deliberate — it is what lets a reviewer read the output
   beside `clean.tla`. Renaming to something more idiomatic would require
   knowing what the names *mean*, which a translator does not.
2. **`proposed: bool` vs `phase: LPhase`.** `clean.tla` tracks "have I already
   sent 2a for this ballot" as a boolean, which is what the original's
   `~ \E m \in msgs : m.type = "2a" /\ m.bal = b` guard amounts to once the
   leader is a node. The hand-written spec models an explicit phase enum. Both
   are faithful to their own source; the difference is in the specs, not the
   translation.
3. **No learner.** The hand-written spec has `accepts_rcvd`, `decided_val` and
   an `LLearn` action. `Paxos.tla` explicitly does not: *"there will be learner
   processes … The learners are omitted from this abstract specification."* The
   generated output correctly reflects its input. This is the clearest case of a
   difference that lives in the **inputs**, not in the translator.

**Constants** differ in the same way: the hand-written spec carries a
precomputed `quorum_size`, while the generated one counts
(`s_arg.len() * 2 > c.acceptor.len()`) because that is what `clean.tla` says.
Both are P4-shaped; one pre-computes what the other derives.

**Conclusion.** For everything `Paxos.tla` specifies, the translator's output is
structurally the same spec a human wrote by hand — which is the claim M2 exists
to test.

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
