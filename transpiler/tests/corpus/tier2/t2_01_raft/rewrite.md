# t2_01_raft — rewrite notes

**Source**: `ongardie/raft.tla` `raft.tla`
**Pinned commit**: `935da8ef24c668176e5f061757b9f25d533e58f0`
**Clean-distance at intake**: 6

**Status**: `clean.tla` written, the linter accepts it, and the translator
produces `golden.rs`, which passes `verus`. **TLC does not complete** — see
"TLC status" below, which is why the case is `golden` and not `green`.

## What the linter found (clean-distance 6)

- **C3 caught `allLogs`** — the history-variable rule's first real hit: "built by
  gathering per-node state over all of `Server`".
- `elections` is global; `messages` is a **bag**, not a set (ongardie's Raft
  models duplication with a message→count function), so C4 reported a near-miss.
- The single C5 finding was *caused by* the history variable: `Next` is the whole
  disjunction **conjoined** with `allLogs' = allLogs \cup {log[i] : i \in Server}`.
  Removing `allLogs` fixes C3 and C5 together.

## The rewrite

- **History variables deleted**: `allLogs`, `elections`, `voterLog`, and the
  `mlog` field carried in messages. The original labels the last two itself —
  *"used as a history variable for the proof … would not exist in a real
  implementation"*.
- **Bag → set.** `DuplicateMessage` disappears: a set cannot express it. Receipt
  still **consumes**, as the original's `Discard`/`Reply` do.
- **`Quorum` → counting** (P4): `Cardinality(votesGranted[i]) * 2 >
  Cardinality(Server)`.
- **A `TypeOK` was added.** The original has none, and the subset states
  per-node-ness in terms of declarations.
- Log-conflict truncation is out of this slice.

## Two mistakes this rewrite made, and what they teach

1. **Non-consuming receipt was copied from Paxos, where it belongs, to Raft,
   where it does not.** Paxos's spec says messages are never removed; Raft's
   discards on receipt. Applying the wrong one made `msgs` accumulate without
   bound and the state space diverge (depth climbing past 190 with no sign of
   closing). Fixed. **The lesson is that "does receipt consume?" is a per-spec
   fact to read off the source, not a rule of the subset.**

2. **State-space blow-up from a fat message record.** The clean subset's message
   type is a union of record sets, and the projection derives each variant's
   payload from its constructor. To keep the union's members structurally
   identical this rewrite gave *every* message all twelve fields and filled the
   unused ones with a default. That multiplies the reachable field combinations,
   and TLC does not finish even at 2 servers, `MaxTerm = 2`, `MaxLogLen = 1`
   (86M states generated, 11M distinct, still growing).

   The original avoids this by giving each message type only the fields it
   needs. **The fix is to do the same** — the projection's per-variant payload
   rule already supports it, and the fat record actively defeats that rule. This
   is the next step for the case.

## TLC status: bounded evidence, not a completed check

Messages were restructured per type after the blow-up above, and TLC still does
not terminate. The honest reading is that this is a property of **Raft**, not of
the rewrite: the reachable subsets of a message set grow combinatorially, which
is why the original is model-checked with bounds too.

With an in-flight bound (`Cardinality(msgs) <= 2`), `Server = {s1, s2}`,
`MaxTerm = 2`, `MaxLogLen = 1`, TLC explores **3.7M states without finding a
violation** of `TypeOK` or `OneLeaderPerTerm`, and does not close the space.

That is evidence, and it is worth having, but it is **not** the completed check
that `t1_02_twophase` has. It must not be written up as one.

## Translator gaps this case closed

Raft was the case that made the projection carry **types**. Every gap it opened
was the same gap: the translator knowing what shape a value has. All are closed;
the golden's header lists them against the output they produce.

- `<<>>`, `Len`, `Append`, `SubSeq`, and record access on a sequence element.
- **TLA+ sequences are 1-indexed; Verus's `Seq` is 0-indexed.** Projecting an
  index unchanged produces an off-by-one that **still verifies** — the worst
  kind of bug. The fix is to subtract one *from the type*: a `Seq` index loses
  one, a `Map` key does not. Guessing from the expression could not tell
  `log[i]` from `nextIndex[j]`.
- **Helper parameter types are read off the call sites**, not off the body.
  `LastTerm(log[i])` says the parameter is `Seq<LLogEntry>`; the body's `Len`
  would only have said "some sequence", and `Seq<int>` is the wrong element
  type.
- **Length is coerced to `int`.** `len()` is a `nat` and TLA+ has one number
  type; without the coercion, comparing a log length to a term is a type error.
- **`Next`'s binders now travel with the action.** `\E j \in Server` becomes
  `c.server.contains(j) && LRequestVote(..)`. Dropping it let `LNext` take
  transitions the source has no state for — this affected Paxos too, where
  `\E b \in Ballot` had been quantifying over every integer.

## Remaining limitation

The projection still requires a **declaration** to read an element type from
(`x \in [Node -> T]`, or an `Init` function constructor). ongardie's Raft has no
`TypeOK` at all, which is why this rewrite adds one; a spec with neither would
not project today.

## V1: the golden verifies

`verus -V no-solver-version-check golden.rs --crate-type=lib` →
`0 verified, 0 errors`. A spec-only file has no proof obligations, so this is
the typecheck, and the typecheck is what catches the class of defect above: a
missing variant field, an unbound `msource`, an `int`/`nat` mismatch and a
predicate-typed helper were all found this way, not by review.
