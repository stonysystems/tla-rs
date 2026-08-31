# An open question about `ApplyValidate`, found while proving `CommittedImpliesChosen`

**Date**: 2026-08-31
**Status**: **question, not a claim.** It may be a real gap in EPaxos\*, or a gap
in this port, or something the paper's Appendix D rules out by an argument this
note has not reproduced. It has to be settled before `Agreement` can be proved,
because the slow-path commit site depends on it.

## What the proof needed

`CommittedImpliesChosen` has six commit sites. `LCommitFast` is
[done](../src/protocol/EPaxosStar/chosen.rs) —
`lemma_commit_fast_gives_fast_chosen`. `LCommitSlow` commits `(inst.cmd,
inst.dep)` at `inst.bal`, so `SlowChosen` requires

```
AcceptSent(network, id, inst.bal, inst.cmd, inst.dep)
```

i.e. an invariant of the form *"a replica in phase `Accepted` holds a value that
really was proposed in an `Accept` at that ballot"*.

## Two formulations, both false

**Over `bal`** — false, and instructively so. `LHandleRecover` applies
`RecoveredInstance`, which moves `bal` while leaving `phase`, `abal`, `cmd` and
`dep` alone, so a replica sitting in `Accepted` can have a `bal` at which no
`Accept` was ever sent. **`abal` exists precisely to be the ballot at which the
held value was accepted**, and the single-ballot protocol is unsound for exactly
the reason this formulation is wrong.

**Over `abal`** — also false, and this is the open question. `ApplyValidate`
(`docs/epaxos_reference/EPaxosCommitWithRecovery.tla:214-218`) writes `cmd`,
`initCmd` and `initDep`, and `HandleValidate` (`:437-450`) leaves `phase`,
`abal` and `dep` `UNCHANGED`. Its only guard is `bal[p][id] = b`.

## The scenario

Replica `X` is in a recovery quorum `Q` for instance `id` at ballot `b`, driven
by replica `Y`.

1. `X` answered `Y`'s `Recover`, so `ApplyRecover` set `bal[X] = b`. That is a
   promise: `abal[X] < b`.
2. `Y` reaches `HandleRecoverOK` branch 4 and sends `Validate(b, c, D)` to `Q`.
3. `Y`'s validation concludes in `LValidateNop` — an objection settled it — so
   `Y` broadcasts `Accept(b, Nop, {})`.
4. **`X` processes the `Accept` before the `Validate`.** Nothing forbids this:
   `msgs` is a set in the reference and the network here is a monotone set, so
   there is no ordering between two messages from the same sender.
5. `ApplyAccept` gives `X`: `phase = Accepted`, `bal = abal = b`, `cmd = Nop`,
   `dep = {}`.
6. `X` then processes the `Validate`. `bal[X] = b` still holds, so
   `ApplyValidate` fires: `cmd[X] := c`, `dep[X]` untouched.

`X` now reports, in any later `RecoverOK`, `abal = b`, `phase = Accepted`,
`cmd = c`, `dep = {}` — a pair that **was never accepted at `b`**. What was
accepted at `b` is `(Nop, {})`.

## Why it matters

`HandleRecoverOK` selects among replies by maximum `abal` and adopts that
reply's `(cmd, dep)`. A later recovery at `b' > b` whose maximum `abal` is `b`
and whose witness is `X` would adopt `(c, {})`. If `(Nop, {})` was committed at
`b`, that is an `Agreement` violation.

## What would rule it out

Any of these would close it, and none is established here:

1. **A guard this note has missed.** `HandleValidate` has no phase guard in the
   reference; if the intended protocol has one, the port should have it too.
2. **`Q`-membership** forbidding step 4 — some reason a member of the validation
   quorum cannot have accepted at `b` before the `Validate` arrives.
3. **The order being unreachable** for a reason outside these two actions.
4. **The value agreeing anyway** — if the recovery's `Validate` payload and its
   eventual `Accept` payload always coincide. They do for `LValidateAccept`
   (both `(cvar, dvar)`) and **do not** for `LValidateNop`, which is the case
   above.

## How to settle it

Model checking would answer this in minutes and is exactly what is unavailable:
the reference's own `.cfg` does not close (38M states, disk exhausted, Phase
56.0.e), `verus2-tla` cannot ingest this spec, and the corpus translator path is
blocked. Failing that, the paper's Appendix D covers the recovery argument and
should be read against this scenario specifically.

Until then `AcceptedStateHasAccept` stays unproved, and with it `LCommitSlow`'s
half of `CommittedImpliesChosen`. **Recorded rather than worked around: an
`assume` here would hide precisely the thing worth knowing.**
