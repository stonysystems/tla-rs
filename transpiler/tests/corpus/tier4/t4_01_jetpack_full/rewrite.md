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

Three models, all on the current files. The two that closed are the evidence;
the third is bounded and is labelled as such.

| # | model | states (distinct) | depth | result | actions covered |
|---|---|---|---|---|---|
| 1 | `MaxRestarts = 1`, `msgs <= 3` | **17,570,820** | 73 | **completed, no violation** | **34 / 34** |
| 2 | `MaxRestarts = 0`, `msgs <= 3` | 717,249 | 69 | completed, no violation | 33 / 34 |
| 3 | `MaxRestarts = 0`, `msgs <= 4` | 33,711,786 | 55 | **did not complete** | 33 / 34 |

```
CONSTANTS Server = {s1,s2,s3}  Client = {c1}  Commands = {v1}
          CmdId = {i1}  Key = {k1}
          MaxTerm = 2  MaxLogLen = 2  MaxElections = 1  MaxEpoch = 1
SPECIFICATION Spec
INVARIANTS  TypeOK  Consistency  OneLeaderPerTerm
PROPERTIES  LeaderOnlyAfterRecovery
CONSTRAINT  SmallState
```

Model 1 is the result to quote: the whole state space, every action reachable,
and no violation of `TypeOK`, `Consistency`, `OneLeaderPerTerm` or the action
property. Model 2 differs only in `MaxRestarts`, which is what leaves `Restart`
unreachable there.

Model 3 explored 33.7M distinct states to depth 55 without a violation and was
then **killed by the OOM killer**, not finished. It is evidence and it is not a
completed check; it is listed because a larger message bound reaching the same
depth without a counter-example is worth recording, not because it proves
anything model 1 does not.

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

## Checked against the original's own safety properties

**To run it:** `./stage_originals.sh <outdir>` generates the three upstream
modules this INSTANCEs, from `tier3/t3_01_jetpack/`, editing only the MODULE
line and the INSTANCE targets so three files whose upstream names collide with
the rewrite's can share a directory. They are generated rather than copied
because a copy drifts from the thing it claims to be, and this check is
worthless the moment it is checking a stale one. `--fix-vacuous-min`
additionally applies the one-line correction below; it is a flag and not a
default because editing upstream to make your own check look stronger is
exactly what this construction exists to avoid.

*(The script was missing at first. `jetpack_refinement.tla` was committed
without the modules it INSTANCEs, so the result below could not be reproduced
from a checkout at all — found by an adversarial review of this case.)*

`jetpack_refinement.tla` INSTANCEs the **unmodified** upstream composition under
an explicit mapping from the rewrite's state and checks *its* invariant
definitions -- `O!NoLogDivergence`, not a retyped copy. Retyping is the failure
mode the construction exists to avoid: a transcription slip in a hand-copied
invariant makes the check pass and says nothing.

The mapping is two lines, because only two things differ in the state these
invariants read: the original indexes logs by proposer (`log[i]["sole"]`) and
its variables range over `Server` rather than `Node`.

**Result: 34,718,400 distinct states, depth 73, state space closed, no
violation** — reproduced from the repository through `stage_originals.sh
<outdir> --fix-vacuous-min`, matching to the state, with `Commands = {v1, v2}` so the value comparison has something to
compare.

| invariant | verdict | has teeth? |
|---|---|---|
| `O!NoLogDivergence` | holds | **yes** — verified |
| `O!CommittedLogAgreement` | holds, **after correcting it** | yes, once corrected |
| `O!MaxOneReconfigurationAtATime` | holds | **no** — vacuous here |

**`CommittedLogAgreement` is vacuous in the upstream spec.** It computes

```tla
limit == Min({ci, ci2} \cup {0})
```

and `Min` is a genuine minimum, so with `ci, ci2 >= 0` the limit is **always 0**
and `\A k \in 1..limit` compares nothing. Confirmed by evaluating it:
`Min({3,5} \cup {0}) = 0`, `1..0 = {}`. It is the first of the five properties
in upstream's `Safety`, and the composition re-exports it as "per-proposer
committed log agreement". The `\cup {0}` was presumably meant to guard `Min`
against an empty set, but `{ci, ci2}` is never empty. The intended expression is
`Min({ci, ci2})`.

The vacuity was not hiding a bug: with the invariant corrected, the **original**
still passes (123,757 states, depth 52), and so does the rewrite. Upstream is
left unedited — it is not ours to change — and the correction is applied only to
the staged copy the refinement module reads.

**`MaxOneReconfigurationAtATime` is vacuous against this rewrite, for two
reasons, and the second is a defect in the mapping rather than in the rewrite.**

1. It needs two uncommitted config entries in a leader's log, and the rewrite
   never appends a config entry at all. `RequestReconfig` sets
   `pendingReconfig` and nothing turns it into a log entry — upstream has
   `AppendPendingReconfigToLog` and the rewrite dropped it. Reconfiguration
   here is requested and never applied.

2. **The tag spellings differ, so upstream's `IsConfigCommand` is false on
   every entry regardless.** Upstream writes `InitClusterCommand ==
   "InitClusterCommand"`; the rewrite writes `"initCluster"`. `O!IsConfigCommand`
   is evaluated *inside* the INSTANCE, so it tests membership in upstream's
   strings, and the mapped log carries the rewrite's. Confirmed rather than
   reasoned: a probe asserting no entry is a config command survives 1.8M
   states, when `FirstEntry`'s own `InitClusterCommand` would refute it in the
   **initial state** if the spellings matched.

Reason 2 is mine and it is the more serious of the two: it means the mapping
passes values through that upstream's definitions cannot recognise. It does not
touch the two invariants that *do* have teeth — `NoLogDivergence` and
`CommittedLogAgreement` compare entries against each other and mention no
upstream constant — but any `O!` predicate that tests against upstream's tags is
silently false-y under this mapping, and the write-up above said only that the
rewrite lacked the action.

Both recorded, neither fixed. The measured shape of the fix is in `TODO.md`
55.7.

**Anti-vacuity, run rather than asserted.** Adding an action that puts a
different value at index 1 on one server and commits it makes
`O!NoLogDivergence` — the original's own definition, reached through the
INSTANCE — refute immediately. Without that, "no violation" would be a statement
about the mapping rather than about the rewrite.

**What this is not: trace refinement.** It does not establish that every
behaviour of the rewrite is a behaviour of the original. It establishes that
every reachable state of the rewrite, mapped, satisfies the original's stated
safety invariants. Full refinement additionally needs step correspondence, and
the bag/set difference in the network plus the rewrite's handler decomposition
mean that is not a mapping away.

The two invariants that cannot be checked here at all are
`LogOrderMatchesExecution` and `ExecutionDedupMatches`: both are about
`execution_cmds`, a history variable the rewrite deletes by design.

---

## V2

Not available, and the reason is the case rather than the tool. There is no
"original" to compare against as one file: the upstream is three modules whose
composition this *is*. The comparison that would mean something is a refinement
mapping against the unmodified originals, which is `TODO.md` 55.5's remaining
scope and is not done.
