# t0_04_readers_writers — why this case is reject-only

**Source**: `tlaplus/Examples` `specifications/ReadersWriters/ReadersWriters.tla`
**Pinned commit**: `ee05f259276db2b878a55a442ea6daa8429db7e9`
**Clean-distance**: 1 (C5)
**Decided**: 2026-08-04

As with `t0_02_bakery`, the `clean.tla` and `rewrite.md` that used to sit here
were intake placeholders, not a rewrite, and have been removed.

## What the linter finds

`readers`, `writers` and `waiting` are **all** global — the spec models a
shared lock, so *nothing* in it is per-node. This case is the C1 boundary in its
purest form, and it is the reason the linter says so in one line rather than
reporting three separate C1 violations: a spec with no per-node state is not
"almost clean", it has **no projection at all**.

## Why rewriting it would not be a rewrite of this spec

There is nothing to project. Turning a shared reader/writer lock into a
distributed one means designing a lock service — choosing a coordinator or a
quorum, deciding what a reader does while a writer's grant is in flight,
deciding what happens when the coordinator fails. Every one of those is a design
decision the source spec does not contain, which is precisely the boundary
`docs/clean_tla_subset.md` draws. The result would be a new protocol, and V2
would have no common observable to compare it against.

## What it is for

Two things. It pins the linter's handling of the C1 boundary — the "this spec
has no projection" verdict, as opposed to a list of violations — and it keeps a
case in the corpus whose answer to "what does projection do here?" is honestly
*nothing*.
