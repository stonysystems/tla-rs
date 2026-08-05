# Clean-Subset TLA+ → Verus Translator: Evidence

What the translator has been shown to do, on which specs, checked how. This is
the scorecard for [Phase 52](clean_tla_to_verus_translator_plan.md); the claims
here are the ones the repository's tests re-check, and where a claim is *not*
mechanically re-checked this document says so.

- The contract: [`clean_tla_subset.md`](clean_tla_subset.md)
- How a case is made: [`clean_tla_rewrite_playbook.md`](clean_tla_rewrite_playbook.md)
- The cases: [`transpiler/tests/corpus/`](../transpiler/tests/corpus/README.md)

---

## The claim

> A TLA+ spec **inside the clean subset** can be mechanically projected into a
> single-process Verus spec of the shape tla-rs already hand-writes, and the
> result typechecks under Verus.

Not claimed: that the *rewrite into the subset* can be automated (it cannot —
that is C2, and the playbook exists because of it), that the output is proved
correct (only a spec is generated, never a proof), or that the projection is
behaviour-preserving in the strong sense (see V2 below).

---

## Scorecard

Ten cases across four tiers. `green` means all three checks below hold;
`golden` means the case translates and verifies but V2 is unavailable or
incomplete, for a reason the case records.

| Case | Tier | Clean-distance | Status | V1 verus | V2 state-set | V3 golden |
|---|---|---|---|---|---|---|
| `t0_01_simple` | 0 | 1 (C2) | **green** | pass | EQUAL | pass |
| `t0_03_dining_philosophers` | 0 | 6 (C2) | **green** | pass | EQUAL | pass |
| `t0_05_lamport_mutex` | 0 | 2 (C1, C4) | **green** | pass | EQUAL | pass |
| `t1_01_paxos` | 1 | 1 (C5) | **green** | pass | EQUAL | pass |
| `t1_02_twophase` | 1 | 2 (C1) | **green** | pass | EQUAL | pass |
| `t2_01_raft` | 2 | 6 (C1,C3,C4,C5) | golden | pass | bounded only | pass |
| `t2_02_epaxos` | 2 | 3 (C1) | golden | pass | n/a | pass |
| `t3_01_jetpack` | 3 | 2 (C4, C5) | golden | pass | n/a | pass |
| `t0_02_bakery` | 0 | 3 (C2) | reject-only | — | — | — |
| `t0_04_readers_writers` | 0 | 1 (C5) | reject-only | — | — | — |

The two `reject-only` cases exist so the linter has specimens it **must**
reject; rewriting them would produce a different algorithm, not a rewrite. See
each case's `why_reject_only.md`.

---

## What each check is, and what it is worth

### V1 — the output typechecks under Verus

`tests/corpus_v1_guard.rs`, over every `golden.rs`. Skips loudly when no Verus
is present; never passes having checked nothing.

A spec-only file has no proof obligations, so a pass reports `0 verified,
0 errors` — which looks like nothing happened. It is not nothing. On this
corpus the typecheck caught:

- a message variant constructed without the fields it declares (Raft);
- an unbound identifier where routing should have been (Raft's `msource`);
- an `int`/`nat` mismatch from `len()` (Raft);
- a value-returning helper typed `bool` (Raft's `LastTerm`, EPaxos's `Max`);
- a record field emitted with **no type at all** (EPaxos's `status`);
- a variant name that is not a Rust identifier (EPaxos's `pre-accepted`).

Every one would otherwise have shipped as a plausible-looking spec.

### V2 — the rewrite reaches the same observable states as the original

`tests/corpus/scripts/tlc_fidelity.sh`. Both specs are model-checked to
completion, every state is projected onto the observables the case declares in
`observables.toml`, and the two sets are compared.

**This is state-set equality, not behavioural equivalence**, and the difference
is demonstrable: deleting `RMChooseToAbort` from 2PC's clean spec entirely still
reports EQUAL, because an RM reaches `"aborted"` by receiving the TM's abort
anyway. A path disappears and the check is silent. No case's `rewrite.md` may
report EQUAL as behavioural equivalence.

Results, and note that raw state counts are *not* the comparison — they differ
by up to 2,600× because the rewrite splits atomic steps into message exchanges:

| Case | Observable | Raw states (clean / original) | Distinct observable |
|---|---|---|---|
| `t0_01_simple` | `x`, `y` | 293 / 51 | 18 = 18 |
| `t0_03_dining_philosophers` | `hungry` | 92,160 / 35 | 5 = 5 |
| `t0_05_lamport_mutex` | `clock`, `req`, `ack` | 10,401 / 10,209 | 8,562 = 8,562 |
| `t1_01_paxos` | `maxBal`, `maxVBal`, `maxVal` | 3,850 / 145 | 43 = 43 |
| `t1_02_twophase` | `rmState` | 288 / 288 | 34 = 34 |

**It has caught real defects**, in both directions:

- *the rewrite*: DiningPhilosophers' first draft split "stop eating" from
  "become hungry again", reaching 11 `hungry` states the original cannot;
- *the method*: LamportMutex reported 4,214 states only in the original until
  both sides ran under the same state constraint — a correct rewrite very
  nearly written up as a defect.

Where V2 is unavailable, the reason is the case rather than the tool: Jetpack
and EPaxos are deliberate slices whose safety properties are stated over state
the original keeps elsewhere, so there is no comparable projection. Raft's state
space does not close at any useful size, so its evidence is bounded — 3.7M states
explored under an in-flight bound with no violation, which is evidence and is
**not** a completed check.

### V3 — the translator still emits the frozen golden

`tests/corpus_v3_guard.rs`, byte-comparing the `verus!` block. The golden's
header prose is hand-written and excluded; `tests/corpus/scripts/refresh_goldens.sh`
regenerates the block and leaves the prose alone.

V3 alone is weak — a translator change that breaks a golden and regenerates it
passes. That is why V1 and V2 exist, and why goldens are regenerated only
alongside a re-run of both.

### Model checking of the rewrites themselves

Independently of V2, each `clean.tla` is model-checked against its own
invariants. Closed state spaces:

| Case | Model | Distinct states | Depth | Invariants |
|---|---|---|---|---|
| `t0_03_dining_philosophers` | NP=4 | 92,160 | 85 | TypeOK, ExclusiveAccess, ForkConservation |
| `t0_05_lamport_mutex` | N=3 | 1,064,028 | 55 | TypeOK, MutualExclusion |
| `t1_01_paxos` | 3 acceptors | 4,843,318 | 26 | TypeOK, Consistency |
| `t2_02_epaxos` | 3 replicas | 3,214,576 | 47 | TypeOK, Consistency |
| `t3_01_jetpack` | 3 servers | 19,536,088 | 78 | TypeOK, Consistency |

`t2_01_raft` is the exception and does not close.

---

## What the corpus found in the translator

The corpus is a *dev/test/eval* set, not a training set, and its purpose is to
find defects a unit test would not. Counted by the case that exposed them:

| Case | Defects exposed | Character |
|---|---|---|
| tier-0 intake | 5 originals unparseable, then **silent truncation** | `----` read as a module terminator; ReadersWriters was parsing 7 of 21 definitions and reporting success |
| `t0_05_lamport_mutex` | 2 | over-emitted constants; expressions emitted without parentheses (`(i-1) % N` → `i - 1 % N`) |
| `t1_01_paxos` | 3 | uninterpreted constant sets; primed updates inside a conditional; the counting rule itself |
| `t2_01_raft` | 6 + 1 | all type-shaped — see below — plus a **fidelity defect in an already-frozen golden**: `LNext` quantified over every integer because `\E b \in Ballot` dropped its binder's set |
| `t2_02_epaxos` | 9 + 2 | all type-shaped, plus a silent `..` precedence bug and an unresolved-identifier pass-through |
| `t3_01_jetpack` | 0 | translated and verified first try — because Raft had already paid for it |
| `t0_03_dining_philosophers` | 2 | multi-update `EXCEPT`; constant pruning running before `Init` was projected |

Two patterns are worth naming.

**The defects cluster by data shape, not by protocol.** Raft and EPaxos are the
two cases whose data is structured rather than scalar, and between them they
account for fifteen of the twenty-eight. Jetpack, the hardest protocol in the
corpus, exposed none — every gap it would have hit had already been closed by
Raft.

**Silent wrongness is the category that matters.** Three defects would have
produced a *plausible, verifying* spec that says something else: the `----`
truncation, the missing parentheses, and the `..` precedence bug. `0 .. N - 1` —
`t0_01_simple`'s node set — was mis-parsed as `(0 .. N) - 1` for the whole
project, and never changed a golden only because the node set survives as
rendered text.

---

## Limits, stated plainly

- **The rewrite is manual.** C2 is a design decision, and `t0_01_simple`
  demonstrates that three defensible rewrites of a single cross-node read give
  three different verdicts on the same property.
- **V2 is state-set equality**, with a worked counter-example above.
- **Only a spec is generated, never a proof.** The output is
  `LInit`/`LNext`/action predicates; invariants and their proofs remain human
  work.
- **Reconfiguration is outside the subset** (Q2). Raft's joint consensus and
  Jetpack's view machinery are stripped by hand, and their absence is recorded.
- **Two tier-2/3 cases were mismeasured at intake** because the linter could not
  identify their node set. Both are fixed, and the playbook now says to read the
  clean-distance sceptically — but the general lesson is that a linter's
  *silence* is not evidence.
