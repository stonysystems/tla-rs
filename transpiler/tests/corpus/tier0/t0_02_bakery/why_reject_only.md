# t0_02_bakery — why this case is reject-only

**Source**: `tlaplus/Examples` `specifications/Bakery-Boulangerie/Bakery.tla`
**Pinned commit**: `dc6470ac55fe7f4f395ac62dba60ec6fd5d87c24`
**Clean-distance**: 3 (C2)
**Decided**: 2026-08-04

This case is **not** on the road to `green`, and it never had a real rewrite —
the `clean.tla` and `rewrite.md` that used to sit here were the intake
template's placeholders, and they have been removed rather than left to look
like unfinished work.

## What the linter finds, and why it is right

Bakery's doorway reads `num[j]` and `flag[j]` for every other process. Under
**C2** that is an instantaneous cross-node read, three of them, and the rule is
doing exactly its job: no distributed implementation can atomically observe
another process's current ticket.

## Why rewriting it would not be a rewrite of Bakery

Bakery is a **shared-memory** algorithm. The clean subset's whole premise is
that a node reads only its own state and what messages told it. Removing the
shared reads does not produce a message-passing Bakery; it produces a
*different algorithm that solves the same problem*. Two consequences, and
either alone is decisive:

1. **V2 would have nothing to compare.** The fidelity check asks whether
   `clean.tla` reaches the same observable states as `original.tla`. Between
   two different algorithms that question is not merely hard, it is
   meaningless.
2. **The honest counterpart already exists.** "Distributed mutual exclusion by
   timestamps, done with messages" is *Lamport's* mutual-exclusion algorithm —
   which is `t0_05_lamport_mutex`, already in the corpus and already `golden`.
   Rewriting Bakery would produce a second copy of a case we have.

## What it is for

It is the specimen the linter has to reject, with a pinned clean-distance and a
pinned rule set (`C2`), guarded by `tests/corpus_lint_guard.rs`. A linter that
started accepting Bakery would be broken, and this case is how we would find
out.
