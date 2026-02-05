# Phase 12: Proof Patterns for Eliminating Assumes

This document catalogs the proof patterns discovered while eliminating `assume()` calls from generated exec code, starting with the TwoPhase protocol.

## Overview

Generated exec functions have `ensures` clauses of the form:
1. `result.valid()` — validity of the constructed output
2. `LSpecPredicate(s@, result@, ...)` — spec refinement (exec refines spec)

Previously these were assumed. The goal is to replace each assume with an actual proof.

## Pattern 1: Validity by Construction

**Category:** Validity assumes (~27% of all assumes)

When the `valid()` predicate is a conjunction of per-field conditions, and the construction uses known-valid values, Verus can often prove validity automatically.

**Example (TwoPhase):**
```rust
// CState.valid() = self.tm_state.valid()
// CTMState::Init.valid() = true (all variants are valid)
// Therefore: CState { ..., tm_state: CTMState::Init }.valid() is trivially true
```

**When it works automatically:** Simple enums where all variants are valid, primitive fields (u64), and structs where validity only depends on field types.

**When hints are needed:** Nested struct validity, collection size constraints, or arithmetic bounds.

## Pattern 2: Spec Refinement via clone_hashset ensures

**Category:** Spec refinement assumes (~30% of all assumes)

When the spec predicate checks field equality (`s_.field == s.field`), and the exec code uses `clone_hashset(&s.field)`, the proof follows from `clone_hashset`'s ensures clause: `res@ == s@`.

**Key prerequisite:** `clone_hashset` must have `ensures res@ == s@` (added as part of Phase 12.1.1).

**Example (TwoPhase CTMCommit):**
```rust
// Spec: s_.rm_state == s.rm_state AND s_.tm_prepared == s.tm_prepared
// Exec: rm_state: clone_hashset(&s.rm_state), tm_prepared: clone_hashset(&s.tm_prepared)
// Proof: clone_hashset ensures res@ == s@
//   → result.rm_state@ == s.rm_state@
//   → result@.rm_state == s@.rm_state (by View definition)
// Verus proves this automatically given the ensures clause.
```

## Pattern 3: Input Preconditions from Spec Predicates

**Category:** Precondition assumes (~17% of all assumes)

Spec predicates often include conjuncts about the INPUT state (not the output). These cannot be proven — they must be required as preconditions.

**Rule:** For each conjunct in `LSpecPredicate(s, s_, c, ...)` that references only `s` and `c` (not `s_`), add it to the exec function's `requires` clause.

**Example (TwoPhase):**
```rust
// LTMCommit includes: s.tm_state is Init AND s.tm_prepared == c.rm
// These are about the input, not the output → add to requires:
requires
    s.tm_state is Init,
    s@.tm_prepared == c@.rm,
```

## Pattern 4: Empty Set Map Lemma

**Category:** Collection operation proofs

When constructing with `HashSet::new()`, and the View maps via `.map(|x: u64| x as int)`, we need to prove the mapped empty set equals `Set::<int>::empty()`.

**Proof:**
```rust
proof fn lemma_empty_set_map()
ensures
    Set::<u64>::empty().map(|x: u64| x as int) =~= Set::<int>::empty(),
{
    let f = |x: u64| x as int;
    let s = Set::<u64>::empty().map(f);
    assert forall|y: int| !(#[trigger] s.contains(y)) by { }
}
```

**Note:** The lambda must be bound to a `let` variable before use in `assert forall` to avoid trigger issues (Verus doesn't allow lambdas in triggers).

## Pattern 5: Set Insert-Map Commutativity

**Category:** Collection operation proofs

When the spec says `s_.field == s.field.insert(x)` and the exec does `clone + insert`, we need the map-insert commutativity lemma:

```
S.insert(x).map(f) =~= S.map(f).insert(f(x))
```

This is available as `Set::lemma_set_map_insert_commute` (broadcast proof in vstd/set_lib.rs).

**Usage:**
```rust
proof {
    broadcast use Set::lemma_set_map_insert_commute;
}
```

## Summary: TwoPhase Results

| Function | Assumes Removed | Proof Technique |
|----------|----------------|-----------------|
| CInit | 2 (valid + spec) | Pattern 1 + Pattern 4 (empty set map) |
| CTMRcvPrepared | 2 (valid + spec) | Pattern 1 + Pattern 3 (precondition) + Pattern 5 (insert-map) |
| CTMCommit | 2 (valid + spec) | Pattern 1 + Pattern 2 (clone ensures) + Pattern 3 (preconditions) |
| CTMAbort | 2 (valid + spec) | Pattern 1 + Pattern 2 (clone ensures) + Pattern 3 (precondition) |
| **Total** | **8** | |

## Infrastructure Changes

1. **`clone_hashset` ensures clause added:** `ensures res@ == s@` — this is critical for all protocols
2. **`use vstd::set_lib::*`** — needed for broadcast lemmas like `lemma_set_map_insert_commute`

## Verification Results

- Before: 579 verified, 0 errors, ~244 assumes
- After: 580 verified, 0 errors, ~236 assumes
- Net: +1 verified (the new proof lemma), -8 assumes
