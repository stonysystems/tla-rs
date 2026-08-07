# t4_01_jetpack_full — the whole Jetpack, three modules

`tier3/t3_01_jetpack` is a **slice**: 11 of 22 variables, and the fast path
entirely absent (`grep -ci preaccept` = 0 against 15 in the original). Jetpack's
paper is *Consensus Made Generally Fast*; the fast path is the contribution and
the recovery layer is the fallback. The slice translated the fallback.

This case is the whole thing, in the shape the original has it: two library
modules and a composition that INSTANCEs both.

| file | what it is | lines |
|---|---|---|
| `base_raft_clean.tla` | the base Raft layer — library, no `Init`/`Next` | ~410 |
| `jetpack_clean.tla` | recovery **and the fast path** — library | ~580 |
| `jetpack_raft_clean.tla` | the spec: `Init`, `Next`, invariants | ~260 |

Linting a library alone reports "no next-state relation". That is correct — a
library is not a spec — and each file's header says so. The composition is what
gets linted, and it is **clean**: node set `Node`, 34 per-node variables.

---

## What is kept that the slice dropped

- **The fast path.** `ClientSendPreaccept`, `HandlePreacceptRequest`,
  `HandlePreacceptResponse`, `Resubmit`, `HandleFinishRecovery`, and the client
  quorum counting.
- **The base protocol**, rather than a contract standing in for it.
- **Views and reconfiguration** — see Q2 below.
- **The client layer.**

### `FastpathQuorum` is node-computable, and the slice never tried

The original's definition is second-order — it quantifies over every other
quorum:

```tla
FastpathQuorum(v) == {q \in JQuorum(v) :
    /\ v.proposing_replica_ids \subseteq q
    /\ \A q2 \in JQuorum(v) :
         v.proposing_replica_ids \subseteq q2 => (q \cap q2) \in JQuorum(v)}
```

which is exactly what a node cannot evaluate. It **collapses to a first-order
test**, verified by brute force against the literal definition over all 1,022
`(n, P)` combinations for `n <= 9`, zero mismatches:

```tla
IsFastQuorum(s, members, proposers) ==
  /\ proposers \subseteq s
  /\ IF Cardinality(proposers) * 2 > Cardinality(members)
       THEN Cardinality(s) * 2 > Cardinality(members)
       ELSE s = members
```

So the fast path was projectable all along. **It was dropped because it was
never attempted**, not because the subset excluded it.

Sizing note for any model: the Raft composition instantiates
`Proposer <- {"sole"}`, so `|P| = 1`; at 3 servers `1*2 = 2 <= 3`, which lands
in the second row — **the fast path there requires unanimity**. A model that
never reaches a unanimous preaccept never exercises it.

---

## Rewrite decisions

### C1 — one node set, both roles

`Node == Server \cup Client`, with both roles' state per-node and every action
guarded by role (`i \in Server`, `c \in Client`). This is `t1_02_twophase`'s
transaction-manager pattern: the coordinator becomes a node and every node
carries the field.

### C4 — one network, which the base layer now has to notice

`msgs` is one set carrying both layers' messages. That is what C4 asks for, and
it has a consequence the single-layer cases never had: **an action may be handed
a message from the other layer**. `UpdateTerm` read `m.mterm` off whatever was
in `msgs`, and TLC caught it reading `mterm` off a `paq`. It is now guarded on
`TermCarrying`, the four message types that carry a term.

### P4 — quorums counted, three distinct sizes kept distinct

- base Raft: `IsQuorumOf(s, members)` — a majority of the node's own
  `config[i].members`;
- Jetpack recovery: `IsQuorum(s, members)` over `viewMembers[i]`;
- the fast path: `IsFastQuorum` above, which is **larger**, and that is what
  buys the saved round.

Response tables become responder sets plus online aggregation: "highest ballot
among the replies" becomes "highest ballot seen so far", which is the same value
once the quorum is in, and is what an implementation does.

### Q2 — views are per-node state, not a varying node set

`Server` is a CONSTANT and `Server'` appears zero times. What varies is each
node's *opinion* of the membership (`config[i].members`, `viewMembers[i]`),
which is ordinary per-node state, no different in kind from `votedFor`. Q2
excludes the node set itself changing; it does not exclude this. Reconfiguration
is therefore **kept**, unlike in `t2_01_raft` and `t3_01_jetpack`.

---

## Still not faithful

Each of these is a deliberate difference, not a gap:

- **The message bag is a set.** The original's `messages` is a bag so that
  duplication can be modelled. Nothing in the protocol reads a count, and the
  original's own `SendMultipleOnce` already de-duplicates.
- **The four model-checking counters are per-node.** A global budget cannot
  survive projection. Keeping them as per-node state keeps the bounding
  mechanism visible rather than moving it into a `.cfg` constraint.
- **`log[i]["sole"]` loses its middle index.** `base_raft` hardcodes the string
  `"sole"` everywhere rather than quantifying, so this is exact rather than a
  specialisation.
- **Execution tracking is absent.** It is a history variable.
- **Every `\E m \in DOMAIN messages : ... LET i == m.mdest` becomes a handler
  `H(i, m)` guarded on `m.mdest = i`.** The same set of steps, stated so a node
  can take one, which is what C5 asks for.

---

## Model checking

```
CONSTANTS Server = {s1,s2,s3}  Client = {c1}  Commands = {v1}
          CmdId = {i1}  Key = {k1}
          MaxTerm = 2  MaxLogLen = 2  MaxElections = 1
          MaxRestarts = 0  MaxEpoch = 1
SPECIFICATION Spec
INVARIANTS  TypeOK  Consistency  OneLeaderPerTerm
PROPERTIES  LeaderOnlyAfterRecovery
CONSTRAINT  SmallState
```

**6,516,746 distinct states, depth 75, no violation**, with 32 of 34 actions
covered. `Restart` is dead by the model (`MaxRestarts = 0`).

> That run is against the version of the spec **before** the initial-log fix
> below. The re-run on the current files is in progress and had reached 15.6M
> distinct states at depth 48 with no violation when this was written. The
> number above is therefore evidence about a superseded version, and is left
> labelled as such rather than quietly reused.

### What TLC found

Six defects, all in this spec rather than in the tool. Two are worth reading
even if you never touch this case.

**`BecomeToBeLeader` both assigned `ostate'` and listed `ostate` in
`UNCHANGED`.** That conjunction is unsatisfiable, so no node could ever become
leader, and **24 of 34 actions never fired**. Nothing reported it: the module
parses, lints clean, and TLC finds no error — it explored 2,591 states instead
of 6.5 million and said "no error has been found". Now guarded permanently by
`tests/corpus_wellformed_guard.rs`.

**`LeaderHasRecovered` was mis-stated, and the spec was right.** As a state
invariant, "Leader implies `jstate` = Ready" is false at depth 37: a leader
receiving a `BeginRecoveryRequest` re-enters Recovery as a *participant*,
because `jstate` carries both roles. It is false in the original too —
upstream's `HandleBeginRecoveryRequest` adopts the incoming view
unconditionally, with no epoch guard. So the rewrite is faithful here and the
protocol was not "fixed". Restated as the action property the composition
actually guarantees, which is the one thing running the two layers side by side
would not give:

```tla
LeaderOnlyAfterRecovery ==
  [][ \A i \in Server :
        (ostate[i] # B!Leader /\ ostate'[i] = B!Leader)
          => (ostate[i] = B!ToBeLeader /\ jstate[i] = J!Ready) ]_vars
```

The other four: two unclosed comments (TLA+ comments nest, and our frontend is
more permissive than SANY, so nothing had reported them); `NilCmd \notin
Command`, so `TypeOK` failed in the *initial* state; `UpdateTerm` reading a
field off another layer's message; and an **empty initial log** — upstream's
`Init` gives every member `<<firstEntry>>` and sets the leader's `nextIndex` to
2, while mine started empty, and `LogOk` rejects any request carrying entries at
`prevLogIndex = 0`, so the first entry could never be replicated and
`AdvanceCommitIndex` was unreachable.

### Coverage is the check that found two of them

Both specs passed every invariant while most of the protocol was unreachable.
Run `-coverage` and read the **final** table — TLC prints it at every progress
report, cumulatively, so aggregating across reports lets the zeros from the
first one win. That mistake produced a wrong claim in a commit message before it
was caught.

---

## Translation

24 unprojectable parts at first measurement, **5** now. The features closed are
recorded in `TODO.md` 55.2.z. Two of them exposed defects that were already
shipped:

- **The node-set constant was named by "the first constant with a set type".**
  Paxos declares `CONSTANT Value, Acceptor, MaxBallot`, so
  `{ Msg1a(s, d, b) : d \in Acceptor }` was frozen in a **green** case's golden
  as `c.value.map(..)` — 1a broadcast to the set of *values*. V1 typechecks
  (both are `Set<int>`), V2 compares the two TLA+ specs and never looks at the
  golden, and V3 froze the wrong answer as the reference.

- **Operator inlining substituted parameters in sequence**, so a later parameter
  captured an identifier an earlier substitution had introduced.
  `PreacceptReq(s, d, e, c)` called with `e := clientEpoch[c]`, and a fourth
  parameter named `c`, produced `mepoch |-> clientEpoch[cmd]` **and**
  `msource |-> cmd`. Only the first errored; the second is a message sent from
  the wrong node and would have verified.

Remaining five, all genuine translator gaps rather than modelling problems:
`CASE` on the right of an update; a range as a quantifier domain
(`1 .. Len(log[i])`); nested `EXCEPT` over a per-node map (`cmdPool[i]`); a
`LET` whose definitions feed several updates; a multi-binder set comprehension
in a send.

**No golden is frozen yet**, because `clean-tla` refuses to emit an incomplete
spec — a file missing a conjunct still looks like a spec and would be reviewed
as one.

---

## V2

Not available, and the reason is the case rather than the tool. There is no
"original" to compare against as one file: the upstream is three modules whose
composition this *is*. The comparison that would mean something is a refinement
mapping against the unmodified originals, which is `TODO.md` 55.5's remaining
scope and is not done.
