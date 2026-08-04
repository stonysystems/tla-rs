# t0_03_dining_philosophers — rewrite notes

**Source**: `tlaplus/Examples` `specifications/DiningPhilosophers/DiningPhilosophers.tla`
**Pinned commit**: `41faafbabe549530ad54bd4301b07ca4fd93e65b`
**Clean-distance at intake**: 6 (C2)
**Status**: `clean.tla` written, linter accepts, translated, `golden.rs` passes `verus`, V2 **EQUAL**.

## The rewrite is not a redesign

The original is Chandy-Misra, and **Chandy-Misra is natively a message
algorithm** — philosophers hand forks to each other, and a request token
travels the other way. The original just declines to model the handing: it
represents each fork as a global record with a `holder`, and a philosopher
transfers one by writing `forks[LeftFork(self)].holder := LeftPhilosopher(self)`.

That write is the C2 violation, six times over. It is also the only thing
standing between this spec and the subset: everything else — the cleanliness
rule, the initial asymmetry, `CanEat` — carries over unchanged.

## What changed

**A fork stops being an object.** `hasFork[p][q]`, `forkClean[p][q]` and
`hasToken[p][q]` are per-edge facts held at each end. This is the same shape
`t0_05_lamport_mutex`'s `req` table has, and for the same reason: what a node
knows about a peer is state it accumulated, not state it peeks at.

**The token becomes explicit.** The original has no request token because it
has no requests to defer — it hands over any dirty fork it is holding whether
or not anyone wants it. Once asking is a message, deferring is a state, so
`hasToken` appears. It is not an addition to the algorithm; it is the part of
Chandy-Misra the original left implicit.

**Two invariants are added.** `ForkConservation` says a fork and its token each
sit on exactly one side of every edge. The original **cannot state it** — there
a fork is one record with one `holder`, so it is true by construction. After
the rewrite it is a real obligation, and it is what would catch a lost or
duplicated fork.

## The V2 check caught a defect in this rewrite

The first draft split "stop eating" from "become hungry again" into `Think` and
a separate `Hunger` action. That let a philosopher sit not-hungry and not-eating
indefinitely, and **the comparison reported 11 `hungry` states the original
cannot reach** — in the *defect* direction, "the rewrite admits behaviour the
original forbids".

The original reaches exactly five: everyone hungry, or exactly one philosopher
not. Its `Think` is precisely where `hungry := TRUE`, so a philosopher is
non-hungry only across the window between eating and thinking. Merging the two
actions — which is also the more faithful reading — makes the sets equal.

**This is the first time the comparator caught a rewrite error rather than a
configuration one**, and it caught it before the golden was frozen.

## Semantic fidelity (V2)

`tests/corpus/scripts/tlc_fidelity.sh tests/corpus/tier0/t0_03_dining_philosophers`,
at `NP = 4`:

| | clean | original |
|---|---|---|
| states dumped | 92,160 | 35 |
| distinct `hungry` | 5 | 5 |
| result | **EQUAL** | |

The raw counts differ by 2,600×, and that is the rewrite doing its job: one
atomic fork transfer became a request, a deferral, and a hand-over, each
interleavable with everything else. **The observable is untouched.**

`hungry` is the observable because it survives under its own name and its own
meaning, and because it is what the original's `NobodyStarves` is stated over.
`pc` does not compare — it is a PlusCal artefact, and the rewrite's counterpart
is a boolean `eating` rather than a string. `forks` does not compare because
dissolving it *is* the rewrite.

## Its own TLC run

`NP = 4`, `TypeOK` + `ExclusiveAccess` + `ForkConservation`: 92,160 distinct
states, depth 85, **space closed**, no violation.

`-deadlock` is required: with `msgs` consumed on receipt, a behaviour can reach
a state where nothing is enabled, which is termination rather than a defect.

## Reproducing

```bash
mkdir dp && cp clean.tla dp/DiningPhilosophersClean.tla
printf 'CONSTANT NP = 4\nSPECIFICATION Spec\nINVARIANTS TypeOK ExclusiveAccess ForkConservation\n' > dp/DiningPhilosophersClean.cfg
(cd dp && java -cp tla2tools.jar tlc2.TLC -workers 8 -deadlock DiningPhilosophersClean)
```
