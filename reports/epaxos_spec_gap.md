# EPaxos spec gap — `src/protocol/EPaxos/` → EPaxos\*

**Date**: 2026-08-17
**Reference**: `docs/epaxos_reference/EPaxosCommitWithRecovery.tla` (616 lines, vendored — see that directory's README for provenance)
**Subject**: `src/protocol/EPaxos/epaxos.rs` (317 lines) + `src/protocol/EPaxos/types.rs` (81 lines)

## The premise this list rests on

"Correct" here means **aligned with EPaxos\***, not aligned with upstream.
`efficient/epaxos@ab4dbea` — the commit the corpus case pins — is the
specification Sutra refuted (IPL 2020). Chasing fidelity to it would be
reproducing a known-unsafe protocol. The reasoning is in
`docs/epaxos_reference/README.md`.

Two consequences worth stating before the list:

- `transpiler/tests/corpus/tier2/t2_02_epaxos/clean.tla` is **not wrong, it is
  silent**. It deleted recovery outright ("Recovery is what non-zero ballots
  exist for", `clean.tla:12-15`), and recovery is where the upstream bug lives.
  Its 3.2M-state closed TLC run and its `Consistency` result stand — for the
  failure-free path only.
- `src/protocol/EPaxos/epaxos.rs` is a different matter: it has an `LRecover`
  that *looks* like recovery and is not one.

## Summary table

| # | item | ours today | EPaxos\* | class |
|---|---|---|---|---|
| 1 | ballot count | one (`ballot: int`) | `bal` **and** `abal` | **the bug fix** |
| 2 | ballot write discipline | `LRecover` overwrites | 3 distinct Apply rules | **the bug fix** |
| 3 | instance dimension | single instance | `[Proc -> [Id -> _]]` | structural |
| 4 | dependencies | `dep_count: int` | `dep` + `initDep`, sets of `Id` | structural |
| 5 | `seq` | present (`seq`, `max_resp_seq`) | **absent** | delete |
| 6 | conflict test | free parameter | computed from state | correctness |
| 7 | phases | 5 (incl. `Executed`) | 4 | delete |
| 8 | quorums | unconstrained | `N-F` / `N-E` + `ASSUME` | correctness |
| 9 | fast-path condition | `has_conflict == false` | `\|{Dq = initDep}\| >= N-E` at `bal=0` | correctness |
| 10 | slow-path deps | absent | `UNION {Dq}` | add |
| 11 | message types | 6 | 11 | add |
| 12 | recovery | 1 action, unsound | 6 actions + validation | rewrite |
| 13 | ballot generation | free `new_ballot` | `k*N + p` | correctness |
| 14 | `Nop` | absent | present | add |
| 15 | invariants | none | Agreement / Visibility / TypeInv | add |
| 16 | network | output-only | `msgs` set, send **and** receive | structural |

---

## A. State structure — do this first, everything else depends on it

**A1. Lift state to per-(replica, command-id).**
Ours (`types.rs:31-56`) is one flat `LState` describing a single instance:
`cmd: int`, `seq: int`, `phase`, one `ballot`. EPaxos\* keeps every field as
`[Proc -> [Id -> _]]` (`.tla:94-113`), so one replica holds *all* instances it
knows about. Without this there is no `Agreement` to state — the invariant
quantifies over `id`.

Target shape for the single-host spec:

```rust
pub struct LInstanceState {
    pub phase: LPhase,          // Initial | PreAccepted | Accepted | Committed
    pub bal: int,               // A2
    pub abal: int,              // A2
    pub init_cmd: int,          // Bottom-able
    pub cmd: int,
    pub init_dep: Set<int>,     // A3
    pub dep: Set<int>,
}
pub struct LState {
    pub instances: Map<int, LInstanceState>,   // keyed by command id
    pub submitted: Set<int>,
    pub init_coord: Map<int, int>,             // id -> submitting process
}
```

**A2. Add `abal`. This is the fix.**
`.tla:99-100`:

```
bal,   \* bal[p][id] = current ballot known by process p for command id
abal,  \* abal[p][id] = the last ballot where p accepted a slow path value
```

Ours has only `ballot` (`types.rs:33`). One variable is exactly what Sutra
showed is insufficient.

**A3. `dep_count: int` → `dep: Set<int>` plus `init_dep: Set<int>`.**
`dep_count` (`types.rs:41`) is a counter, and — checked across all 24 of its
occurrences — it is never read in any guard. EPaxos\* needs the actual set twice
over: `dep` (current) and `initDep` (what the initial coordinator proposed), and
the fast-path test compares replies against `initDep` (`.tla:275`).

**A4. Delete `seq` and `max_resp_seq`.**
EPaxos\* has no sequence number at all — it orders on `(cmd, dep)` alone. Every
`seq`-looking token in the reference file is a substring of `phaseq` / `abalq` /
`Sequences`. Ours carries `seq` (`types.rs:39`) and `max_resp_seq`
(`types.rs:55`), the latter also never read in a guard.

**A5. Drop the `Executed` phase.**
Ours has 5 (`types.rs:17-28`); EPaxos\* has 4 (`.tla:50-53`). Execution is not in
the commit+recovery spec — nor in upstream's, where `executed'` never appears.
`LExecute` (`epaxos.rs:239`) and `LNewInstance` (`epaxos.rs:283`) go with it;
A1 makes `LNewInstance` meaningless anyway, since instances no longer share one
slot.

**A6. Add `Nop` and `Bottom`.**
`.tla:25-26`. `Nop` is what recovery commits when it cannot safely recover the
original payload — it appears in four separate branches. `Bottom` marks "no
payload yet". Neither exists in our types.

---

## B. Ballot write discipline — three rules, no exceptions

This is the whole of the Sutra fix, and it is worth transcribing exactly.

| EPaxos\* | guard | writes `bal` | writes `abal` |
|---|---|---|---|
| `ApplyAccept` (`.tla:185-192`) | `bal[p][id] <= b`, and `bal = b ⇒ phase ≠ Committed` | `:= b` | `:= b` |
| `ApplyCommit` (`.tla:197-202`) | `bal[p][id] = b` | — | `:= b` |
| `ApplyRecover` (`.tla:207-209`) | `bal[p][id] < b` | `:= b` | — |

**B1.** Promising (recover) must move `bal` and leave `abal` alone.
**B2.** Accepting must move both.
**B3.** Committing must move `abal` and must *require* `bal = b`, not assign it.

Ours has no analogue of any of these: `LRecover` (`epaxos.rs:260-280`) simply
sets `s_.ballot == new_ballot` and resets the instance to `PreAccepted` with the
same `cmd`.

---

## C. Commit path

**C1. `LPropose` → `Submit` (`.tla:238-247`).**
Must (a) guard `id ∉ submitted`, (b) record `initCoord[id] := p`, (c) compute
`D0 == ConflictingIds(p, c)` from the replica's own state, (d) broadcast
PreAccept, (e) self-deliver a PreAcceptOK. Ours (`epaxos.rs:50-69`) does none of
(a)–(c) and sets `seq := committed_count + 1`.

**C2. `LSendPreAcceptOk` → `HandlePreAccept` (`.tla:252-258`), and it must write state.**
Ours (`epaxos.rs:73-91`) is a pure frame — every field preserved — with **no
guard at all**, and it takes `local_conflict: bool` and `local_seq: int` as free
existentially-quantified parameters (`epaxos.rs:305`). EPaxos\* instead:

- guards on `bal[p][id] = 0 ∧ phase[p][id] = Initial` (via `ApplyPreAccept`, `.tla:173-174`);
- **computes** `Dfinal == m.body.D ∪ ConflictingIds(m.to, m.body.c)` (`.tla:254`);
- writes `cmd`, `initCmd`, `initDep`, `dep`, `phase := PreAccepted`;
- replies with the computed `Dfinal`.

So conflict detection stops being an oracle and becomes a function of state.

**C3. `LFastCommit` → the fast branch of `HandlePreAcceptOK` (`.tla:263-287`).**
Ours tests `has_conflict == false` and `preaccept_senders.len() >= fast_quorum_size`.
EPaxos\*:

```
/\ bal[p][id] = 0                                        \* fast path is ballot 0 only
/\ IsQuorumSized(quorumOfMessages)                        \* >= N - F
/\ largestFastQuorum == { m : m.body.Dq = initDep[p][id] }
/\ IF IsFastQuorumSized(largestFastQuorum)                \* >= N - E
   THEN ApplyCommit(p, p, 0, id, cmd[p][id], initDep[p][id])
```

Three differences that matter: the ballot-0 restriction, "replies equal to the
coordinator's `initDep`" rather than "no conflict flag", and two *different*
quorum thresholds in the same action.

**C4. Slow path: `Dfinal == UNION { m.body.Dq }` (`.tla:282`).**
Ours has no notion of combining the replies' dependency sets, because it has no
dependency sets. `LStartAccept` (`epaxos.rs:145`) carries `s.seq` forward instead.

**C5. `LReceiveAcceptOk` / `LSlowCommit` → `HandleAcceptOK` (`.tla:301-314`).**
EPaxos\* filters the quorum on `k.body.b = bal[p][id]` — replies from a stale
ballot do not count. Ours (`epaxos.rs:190-212`) accumulates `ao_sender: int` with
no ballot check and no bound on the sender at all.

---

## D. Recovery — 1 action becomes 6, plus a validation sub-protocol

Ours: `LRecover` (`epaxos.rs:260-280`) bumps the ballot, resets to `PreAccepted`
with the same `cmd`, clears the conflict flag, rebroadcasts PreAccept. It reads
no replies, so it can pick a payload that contradicts a committed one — and it
acts on the replica's *own* state, whereas recovery is by definition another
replica taking over.

EPaxos\* (`.tla:328-548`):

**D1. `StartRecover` (`.tla:328-340`)** — guard `id ∈ SeenIds(p)`; ballot
`b == IF bal = 0 THEN p ELSE bal + N`, so ballots are of the form `k*N + p` and
are globally unique per process. Ours takes `new_ballot` as a free parameter
constrained only by `new_ballot > s.ballot`, which permits two replicas to use
the same ballot.

**D2. `HandleRecover` (`.tla:345-354`)** — `ApplyRecover` (promise), then reply
`RecoverOK` carrying **`abal[p][id]`**, `cmd`, `dep`, `initDep`, `phase`. The
`abal` in this message is what B makes meaningful.

**D3. `HandleRecoverOK` (`.tla:359-432`)** — the core. Collect a quorum,
`bmax == max { abalq }`, `U == { k : k.abalq = bmax }`, then five ordered branches:

| branch | condition | action |
|---|---|---|
| 1 | `∃ n ∈ U : phaseq = Committed` | commit that `(c, D)` |
| 2 | `∃ n ∈ U : phaseq = Accepted` | accept that `(c, D)` |
| 3 | `initCoord[id] ∈ Q` | accept `Nop` |
| 4 | `\|Rmax\| >= \|Q\| - E`, where `Rmax == { n : phaseq = PreAccepted ∧ depq = initDepq }` | enter **validation** |
| 5 | otherwise | accept `Nop` |

Branch 4 is what replaces upstream's ambiguous "enough pre-accepts ⇒ go ahead".

**D4. `ComputeI` / `HandleValidate` (`.tla:220-227`, `:437-450`)** — `I` is the
set of `(id2, phase)` that could invalidate committing `(c, D)`: commands not in
`D`, conflicting with `c`, that do not list `id` among their own dependencies.
This is the check upstream never had.

**D5. `HandleValidateOK` (`.tla:455-490`)** — `I = {}` ⇒ accept `(c, D)`;
`∃` committed in `I`, or `|Rmax| = |Q| - E ∧ ∃x. initCoord[x] ∉ Q` ⇒ accept `Nop`;
otherwise broadcast `Waiting` and move to `PostWaiting`.

**D6. `HandlePostWaiting` (`.tla:495-548`)** — four disjuncts, including the
liveness escape: a `Waiting` message with `k > N - F - E` ⇒ give up and take
`Nop`. This is the deadlock fix.

**D7. Six new message types** — `Recover`, `RecoverOK`, `Validate`, `ValidateOK`,
`Waiting`, `PostWaiting` (`.tla:42-47`). Ours has 6 total; EPaxos\* has 11.
Ours also has a `ClientReply` variant that has no counterpart and belongs to the
execution layer.

---

## E. Quorums

**E1.** Replace `quorum_size` / `fast_quorum_size` (`types.rs:59-68`) with
constants `F` (crash tolerance) and `E` (fast-path tolerance), and derive:

```
IsQuorumSized(s)     == |s| >= N - F      (.tla:152)
IsFastQuorumSized(s) == |s| >= N - E      (.tla:153)
```

**E2.** Add the assumption, as a conjunct of the well-formedness predicate:

```
ASSUME N >= Max(2*E + F - 1, 2*F + 1)     (.tla:34)
```

Our `LInit` (`epaxos.rs:43-45`) currently constrains only
`num_replicas >= 3 ∧ quorum_size > 0 ∧ fast_quorum_size >= quorum_size` — which
admits `quorum_size = 1`. The doc comments in `types.rs:62,64` claim the real
formulas but nothing enforces them.

**E3.** Conflicts become a model parameter: `Conflicts(c1, c2)` (`.tla:147-150`)
with `Bottom` conflicting with nothing and `Nop` conflicting with everything,
over a `ConflictPairs` relation supplied by configuration
(`ExtraConfiguration.tla`).

---

## F. Invariants (verbatim targets)

```tla
Agreement ==                                              \* .tla:554-560
  \A id \in Id : \A p, q \in Proc :
    /\ phase[p][id] = CommittedPhase
    /\ phase[q][id] = CommittedPhase
    => dep[p][id] = dep[q][id] /\ cmd[p][id] = cmd[q][id]

Visibility ==                                             \* .tla:562-571
  \A id, id2 \in Id : \A p, q \in Proc :
    /\ id # id2
    /\ cmd[p][id] # Nop /\ cmd[q][id2] # Nop
    /\ phase[p][id] = CommittedPhase /\ phase[q][id2] = CommittedPhase
    /\ Conflicts(cmd[p][id], cmd[q][id2])
    => id \in dep[q][id2] \/ id2 \in dep[p][id]
```

Plus `TypeInv` (`.tla:573-592`) as the well-formedness predicate. We currently
have zero invariants anywhere in `src/protocol/EPaxos/`.

`Agreement` is the analogue of Raft's `StateMachineSafety`; `Visibility` has no
Raft counterpart and is the property that makes dependency-based ordering work.

---

## G. Distributed layer (shared with the refinement-proof plan)

**G1.** `src/protocol/EPaxos/` has no distributed/network module — only RSL and
Raft have one. `sent_packets` is an output parameter that nothing ever connects
to a receiver, so no distributed property is statable. EPaxos\* has `msgs` as a
first-class variable that every handler both reads and writes.

**G2.** Building that layer subsumes two defects found earlier:

- `pa_sender: int` / `ao_sender: int` are free integers (`epaxos.rs:306,310`)
  never bounded to `0 <= s < num_replicas`, so a leader can fabricate a quorum
  from thin air. Once quorums are filtered out of `msgs`, this cannot be
  expressed.
- `LSendPreAcceptOk` / `LSendAcceptOk` have no guards; a `msgs.contains(m)`
  receive guard supplies one.

---

## Decisions needed before starting

1. **Replace or fork?** Rewriting `src/protocol/EPaxos/epaxos.rs` in place breaks
   `epaxos.automan`, `epaxos_transpile.toml`, `src/generated/EPaxos/`,
   `src/implementation/EPaxos/host.rs` and `scripts/bench_epaxos.sh`. A new
   `src/protocol/EPaxosStar/` leaves the benchmark path intact.
2. **Corpus placement.** Suggest a new `tier2/t2_03_epaxos_star` with
   `docs/epaxos_reference/EPaxosCommitWithRecovery.tla` as its upstream, and
   demoting `t2_02_epaxos` to a documented known-unsafe historical case — it has
   standalone value as the specimen whose defect a reviewer should be able to
   find.
3. **Scope of the first pass.** EPaxos\*'s recovery is 220 lines of TLA+ with
   nested case analysis; `HandleRecoverOK` alone is 74. Landing A + B + C first
   (correct state shape, ballot discipline, commit path) gives something
   checkable before D is attempted.

## What this does not buy

EPaxos\*'s own correctness argument is a hand proof (paper Appendix D); its TLA+
model is TLC-checked in bounded configurations only (`Proc = {1,2,3}`, `F = E = 1`,
one recovery attempt per process per command). Aligning to it removes a known
unsafety; it does not by itself constitute a proof. Per
`docs/consensus_verification_survey.md`, no mechanized safety proof of EPaxos
exists in any system.
