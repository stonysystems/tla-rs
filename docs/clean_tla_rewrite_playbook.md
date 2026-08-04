# The Clean-Subset Rewrite Playbook

How to take a TLA+ spec from the wild and rewrite it into the clean subset so the
translator can project it. This is the procedure the corpus was built by, and
every step here is a step that went wrong at least once.

- The contract: [`clean_tla_subset.md`](clean_tla_subset.md) (C1–C5).
- The corpus: [`transpiler/tests/corpus/`](../transpiler/tests/corpus/README.md).
- Plan of record: [`clean_tla_to_verus_translator_plan.md`](clean_tla_to_verus_translator_plan.md).

**The rewrite is the human's job and the translation is the tool's.** The subset
exists to draw that line. If you find yourself deciding *which message carries
which value*, you are doing the rewrite; if you find yourself deciding *how a
`Seq` index is offset*, that is the tool's and it is a bug.

---

## 0. Intake, and read the number sceptically

```bash
tests/corpus/scripts/intake_case.sh --tier N --id t<N>_<nn>_<name> --url <raw url>
```

It pins the upstream commit, measures the clean-distance, and scaffolds
`rewrite.md`. Then **check what the linter actually saw**:

```
verus-transpile tla-lint --json original.tla | python3 -m json.tool
```

Look at `node_set` and `per_node_variables` before you look at `violations`.

> **A small clean-distance can mean the linter never got started.** Jetpack
> measured 2 and EPaxos measured 1; both were wrong. Jetpack's composition
> module has no type invariant, so the node set could not be identified and C1/C2
> never ran. EPaxos writes `Next == \/ CommandLeaderAction \/ ReplicaAction`,
> pushing the node quantifier one level down, and the linter could not see
> through it — that one was a linter defect and is fixed. **If `node_set` is
> `null`, the number is not a distance, it is a failure to measure.**

**A spec that does not parse is unmeasured, not dirty.** Fix the frontend gap
first. Jetpack needed two (multi-binder set comprehensions, `LAMBDA`); every
tier-0 spec needed several.

---

## 1. Decide the slice before writing a line

Write the exclusions into `clean.tla`'s header *first*, with a reason each. A
reader has to know what is not there before reading what is.

Things that are legitimately out:

| Excluded | Why | Cases |
|---|---|---|
| reconfiguration, views, epochs | Q2 puts membership change outside the subset | Jetpack, Raft |
| the client / execution layer | not part of the protocol layer being projected | Jetpack, EPaxos |
| recovery | usually what non-zero ballots exist for, so ballots collapse with it | EPaxos |
| a base protocol underneath | model it as a contract, and say what the contract is | Jetpack |

"I could not translate it" is **not** a reason. If a construct defeats the
translator, that is a translator gap and it belongs in `rewrite.md` as one.

---

## 2. C1 — make every variable per-node, or the network, or gone

For each global variable, exactly one of these is true:

1. **It is per-node in disguise.** 2PC's `tmState` belongs to the coordinator;
   make the coordinator a node and give every node the field.
2. **It is a history variable.** It exists for an invariant or a proof and the
   protocol never reads it. Delete it and restate the invariant over the state
   the nodes actually hold. Raft's `allLogs`, EPaxos's `committed` and
   `proposed`, Jetpack's view bookkeeping.
3. **It is the network.** See C4.
4. **It is none of these, and the spec has no projection.** ReadersWriters is
   the specimen: `readers`, `writers`, `waiting` are all global, so *nothing* is
   per-node. Say so and stop — see "when not to rewrite" below.

> Deleting a history variable weakens whatever mentioned it. That is a rewrite
> decision, and `rewrite.md` has to record it. The V2 check compares observable
> behaviour, not invariants that no longer exist.

---

## 3. C2 — turn each cross-node read into a message, and *choose*

This is the step that cannot be automated, and the choice is usually not
obvious. `t0_01_simple` is the smallest demonstration: one read,
`x[(self-1) % N]`, and three defensible rewrites with **different verdicts**.

| Rewrite | What it does | Verdict |
|---|---|---|
| push | the neighbour broadcasts after setting `x` | `PCorrect` holds, but every behaviour that reads a 0 is deleted |
| local cache | read the last value you were told | **breaks** `PCorrect` |
| request/response | ask, and wait for the answer | preserves both |

Note that the cache answer is the *opposite* of LamportMutex's, where "cache
what you were told" is exactly right. **The difference is whether the property
depends on freshness**, and only a human knows that.

Write down which you chose and why. Then check it — see step 6.

---

## 4. C4 — designate the network, and read the source on receipt

One variable, a set of messages, each carrying `src`/`dst`.

**Does receipt consume?** This is a per-spec fact to read off the source, not a
rule of the subset:

- Paxos: **no** — "messages are never removed … receipt of the same message
  twice is therefore allowed". A draft that consumed them deadlocked.
- Raft, Jetpack, EPaxos: **yes** — `Discard`/`Reply` remove.

Getting it backwards is not subtle in its consequences and is silent in its
cause: Raft's draft copied Paxos's rule and the state space diverged past
depth 190.

**Flattening per-connection channels drops ordering.** LamportMutex's `network`
is `[Proc -> [Proc -> Seq(Message)]]`, a 2-D array of FIFO queues. Flattening it
into one set loses pairwise ordering, and TLC refuted the first attempt in **13
states**. If the protocol depends on order, ordering has to become explicit
protocol state — `sendSeq`/`recvSeq` per peer plus a `Deliverable` guard, which
is C1/C2-clean because both tables are per-node.

---

## 5. P4 — quorums become counting

Every real spec quantifies over a powerset: `\E Q \in Quorum`,
`\E qs \in JQuorum(new_view[i])`, `\E Q \in FastQuorums(cleader)`. A node cannot
evaluate that.

**Accumulate and count.** Keep a set of responders and guard on
`Cardinality(rcvd) * 2 > Cardinality(Nodes)`. Two consequences worth stating in
`rewrite.md`:

- the abstract quorum constant is gone, replaced by a majority test. That is a
  *specialisation*, not a weakening, because a majority satisfies the
  intersection property quorums are assumed to have;
- "highest ballot among the replies" becomes "highest ballot seen so far",
  which is the same value once the quorum's replies are in — and is what an
  implementation does.

Keep distinct quorum sizes distinct. EPaxos's fast path needs a *larger* quorum
than its slow path, and that is precisely what buys the missing round.

**Scanning the network for agreement is the same problem.** EPaxos's
`\A r1, r2 \in replies : r1.deps = r2.deps` becomes an accumulator that stays
TRUE only while every reply matches.

---

## 6. Check it with TLC before you translate

Not after. Every rewrite in this corpus that had a defect had it caught here.

```bash
mkdir run && cp clean.tla run/<Module>.tla && cp clean.cfg run/<Module>.cfg
(cd run && java -cp tla2tools.jar tlc2.TLC -workers 8 -deadlock <Module>)
```

- **`-deadlock` is usually right, and you must know why.** A bounded ballot or
  instance counter means a behaviour that exhausts it legitimately has no
  successor. Check the terminal state TLC reports and satisfy yourself it is
  termination rather than a stuck protocol.
- **Bound the message set.** Every send is a broadcast; `Cardinality(msgs) <= 4`
  is what makes the check finish.
- **Add a state constraint only if you add it to both sides** — see step 7.
- **A passing invariant proves little on its own.** If a degenerate rewrite
  would also satisfy it, check something the degenerate version would *fail*.
  `t0_01_simple` checks `EveryoneReadsOne` and requires TLC to **refute** it on
  both specs.

---

## 7. V2 — compare against the original

```bash
tests/corpus/scripts/tlc_fidelity.sh <case-dir> <tla2tools.jar>
```

Declare the observables in `observables.toml`: the variables that survive the
rewrite **under their own name and their own meaning**. Everything else is
bookkeeping you reshaped, and comparing it would report the rewrite working as
intended as a failure.

Good observables, from the corpus: 2PC's `rmState`, Paxos's acceptor triple,
Simple's `x`/`y`, LamportMutex's `clock`/`req`/`ack`, DiningPhilosophers'
`hungry`.

**Reading the result:**

- **only in clean** — the rewrite admits behaviour the original forbids. A
  defect. DiningPhilosophers' first draft did this: splitting "stop eating" from
  "become hungry again" reached 11 `hungry` states the original cannot.
- **only in original** — the rewrite lost behaviour. Often intended, but it must
  be *stated*.

**Two traps:**

1. **Hold the model equal.** A state constraint on one side truncates that side,
   and it reads as lost behaviour. LamportMutex reported 4,214 states only in the
   original until both sides ran the same constraint. The script warns on
   mismatched `CONSTRAINT` counts; it cannot check that the constants agree.
2. **It compares reachable *states*, not reachable *behaviours*.** Deleting an
   action whose effects another action also produces leaves the state set
   unchanged and the check silent — deleting `RMChooseToAbort` from 2PC still
   reports EQUAL. **Never write EQUAL up as behavioural equivalence.**

**Raw state counts are not the comparison.** They differ by 26× (Paxos), 2,600×
(DiningPhilosophers) and are meaningless on their own; the projection is the
comparison.

**Some cases cannot have a V2 result at all**, and that is a property of the
case. Jetpack's slice shares no observable with the composition module it came
from. Such a case stays `golden`, and its `rewrite.md` says why.

---

## 8. Translate, verify, freeze

```bash
verus-transpile clean-tla clean.tla --output golden.rs
verus -V no-solver-version-check golden.rs --crate-type=lib
```

`clean-tla` **refuses to emit an incomplete spec** — a file missing a conjunct
still looks like a spec and would be reviewed and trusted as one. Every gap it
reports is a translator task, and it names the construct.

**The Verus run is not a formality.** A spec-only file has no proof obligations,
so "0 verified, 0 errors" is the typecheck — and on this corpus the typecheck
has caught a missing variant field, an unbound identifier, an `int`/`nat`
mismatch, a predicate-typed helper, and a record field with no type at all.

Then write the golden's **header**, by hand, saying what the case shows and what
differences against `reference.rs` are real. Regenerate with
`tests/corpus/scripts/refresh_goldens.sh`, which replaces the `verus!` block and
leaves the prose alone — `clean-tla --output` would destroy it.

---

## 9. When *not* to rewrite

Some specs should not be translation cases at all, and pretending otherwise
wastes effort and produces a meaningless V2. Mark them `role = "reject-only"`
and write `why_reject_only.md`.

The test: **would the rewrite be a rewrite of *this algorithm*, or a different
algorithm that solves the same problem?**

- **Bakery** is shared-memory. A message-passing "Bakery" is a different
  algorithm — and its honest counterpart is *Lamport's* mutual exclusion, which
  is already `t0_05` in the corpus. Rewriting it would duplicate a case.
- **ReadersWriters** has no per-node state at all, so there is nothing to
  project. Turning it into a distributed lock means choosing a coordinator, a
  failure model, a grant protocol — none of which the source contains.

Contrast **DiningPhilosophers**, which *is* a translation case despite looking
similar: Chandy-Misra is natively a message algorithm, and the original merely
declines to model the handing. The rewrite writes the messages down. That is the
distinction to apply.

---

## Checklist

- [ ] `original.tla` parses; gaps filed as frontend work, not counted as dirt
- [ ] `node_set` non-null before the clean-distance is believed
- [ ] slice decided and written into `clean.tla`'s header, each exclusion with a reason
- [ ] every global variable classified: per-node / history / network / no projection
- [ ] every cross-node read message-ified, with the choice recorded
- [ ] receipt semantics read off the *source*
- [ ] ordering, if the protocol needs it, made explicit protocol state
- [ ] quorums counted, distinct sizes kept distinct
- [ ] TLC passes, `-deadlock` justified, anti-vacuity property checked
- [ ] V2 run, models held equal, result stated as state-set equality
- [ ] `clean-tla` emits with no gaps
- [ ] `verus` passes
- [ ] `rewrite.md` records every decision; golden header records the review
- [ ] manifest `status` and `clean_distance` updated; guards green
