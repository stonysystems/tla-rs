# Proof Pattern Catalog for Transpiler

This document catalogs the proof patterns observed across all hand-proven generated
files. The transpiler must generate these patterns to eliminate `assume()` calls.

## Status Summary

| Protocol | Functions | Assumes | Key Patterns Used |
|----------|-----------|---------|-------------------|
| TwoPhase | 4 | 0 | P1, P2, P6 |
| Paxos | 5 | 0 | P1, P2, P6 |
| LeaderElection | 5 | 0 | P1, P2, P3, P6 |
| Raft | 9 | 0 | P1, P2, P6, P7, P8, P11, P12 |
| ChainReplication | 7 | 0 | P1, P2, P3, P6, P7, P12 |
| RSL (non-dispatch) | ~40 | 0 | P1-P12 (all patterns) |
| RSL (IO dispatch) | 4 | 12 | Irreducible IO layer |

## Pattern Catalog

### P1: Empty Collection Map

**When needed:** A function initializes state with `HashSet::new()` / `Vec::new()`,
and the spec uses `Set::<int>::empty()` / `Seq::<int>::empty()`.

**View gap:** `HashSet::<u64>::new()@` = `Set::<u64>::empty()`, but the spec type
uses `Set::<int>`. The `.map(|x: u64| x as int)` in the View impl creates a gap
that Verus can't auto-close.

**Proof code:**
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

**Variants:**
- `lemma_empty_seq_map()` for `Vec<u64>` → `Seq<int>` (ChainReplication)
- `lemma_empty_log_map()` for `Vec<CLogEntry>` → `Seq<LLogEntry>` (Raft)

**Trigger:** Any function that constructs `HashSet::new()`, `Vec::new()`,
or `HashMap::new()` where the View type maps element types.

### P2: HashSet Insert + Map Commutativity

**When needed:** A function does `hashset.insert(x)` and the spec says
`s.insert(x as int)`.

**View gap:** After `insert`, the view is `s@.insert(x)` = `Set<u64>.insert(u64)`,
but spec expects `Set<int>.insert(int)`. Need:
`s.insert(x).map(f) == s.map(f).insert(f(x))`

**Proof code:**
```rust
proof {
    broadcast use Set::lemma_set_map_insert_commute;
}
```

**Trigger:** Any `HashSet::insert()` call where View maps `u64 → int`.

### P3: HashSet Remove + Map Commutativity

**When needed:** A function does `hashset.remove(&x)` and the spec says
`s.remove(x as int)`.

**View gap:** Same as P2 but for `remove`. vstd doesn't provide a broadcast
lemma for this, so we need our own.

**Proof code:**
```rust
proof fn lemma_set_map_remove_commute(s: Set<u64>, elt: u64)
ensures
    s.remove(elt).map(|x: u64| x as int) =~= s.map(|x: u64| x as int).remove(elt as int),
{
    let f = |x: u64| x as int;
    let lhs = s.remove(elt).map(f);
    let rhs = s.map(f).remove(f(elt));
    assert forall|y: int| (#[trigger] lhs.contains(y)) implies rhs.contains(y) by {
        let x = choose|x: u64| s.remove(elt).contains(x) && f(x) == y;
        assert(s.contains(x));
        assert(x != elt);
        assert(f(x) != f(elt));
        assert(s.map(f).contains(y));
    }
    assert forall|y: int| (#[trigger] rhs.contains(y)) implies lhs.contains(y) by {
        let x = choose|x: u64| s.contains(x) && f(x) == y;
        assert(y != f(elt));
        assert(f(x) != f(elt));
        assert(x != elt);
        assert(s.remove(elt).contains(x));
    }
}
```

**Trigger:** Any `HashSet::remove()` call where View maps `u64 → int`.

### P4: Struct Construction → Spec Conjunction Decomposition

**When needed:** The `ensures` clause includes `LSpecPredicate(s@, result@, ...)`,
and the spec predicate is a conjunction of field-level equalities.

**Why it works automatically (for simple protocols):** If each field of the result
maps directly to a spec field via View, Verus can verify the conjunction
automatically. No explicit proof block needed.

**When it fails (RSL):** When fields involve deep conversions (e.g.,
`abstractify_cvotes`, `abstractify_clearnerstate`) or complex collection
operations, explicit assertions are needed.

### P5: Validity Propagation

**When needed:** The `ensures` clause includes `result.valid()`.

**Why it works automatically (for simple protocols):** When `valid()` is trivially
`true` or a conjunction of `field.valid()` where each field's validity is
straightforward (e.g., enum variant → `true`).

**When it fails (RSL):** When `valid()` includes bounds checks, collection
constraints, or depends on multiple interacting fields.

### P6: Enum Variant Preconditions

**When needed:** The spec predicate has `recommends s.tm_state is Init` or similar.

**Solution:** The exec function adds a `requires` clause:
```rust
requires
    s.tm_state is Init,
```

**Key insight:** `is` variant test works in `requires` (spec context) with bare
variant names. The transpiler extracts these from spec `recommends` clauses.

### P7: Seq Push + Map Commutativity

**When needed:** A function does `vec.push(x)` and the spec says
`seq.push(x@)` or `seq.push(x as int)`.

**Proof code (for `Vec<CLogEntry>`):**
```rust
proof fn lemma_log_push_map_commute(s: Seq<CLogEntry>, x: CLogEntry)
ensures
    s.push(x).map(|i: int, e: CLogEntry| e@) =~= s.map(|i: int, e: CLogEntry| e@).push(x@),
{
}
```

**Proof code (for `Vec<u64>`):**
```rust
proof fn lemma_seq_push_map_commute(s: Seq<u64>, x: u64)
ensures
    s.push(x).map(|i: int, v: u64| v as int) =~= s.map(|i: int, v: u64| v as int).push(x as int),
{
}
```

**Note:** These lemmas have empty bodies — Verus can prove them automatically
via extensional equality.

**Trigger:** Any `Vec::push()` call where View maps element types.

### P8: HashMap Insert View Identity

**When needed:** A function does `hashmap.insert(k, v)` where `HashMap<u64, u64>`.

**Why it works automatically:** `HashMap<u64, u64>@` = `Map<u64, u64>` (identity,
no type conversion). So `m.insert(k, v)` in exec directly corresponds to
`m@.insert(k, v)` in spec (Verus does implicit int widening).

**No proof code needed** — just ensure the HashMap::insert() return value is
discarded: `{ m.insert(k, v); }`

### P9: clone_hashset Ensures `res@ == s@`

**When needed:** Any function that clones a HashSet field to build a new struct.

**Not a proof pattern per se** — this is a precondition that `clone_hashset` has
the right spec. Already implemented in `common/collections/hashsets.rs`.

### P10: Unreachable Arm from Requires

**When needed:** A match arm that can't be reached given the function's
preconditions.

**Current state (RSL):** Uses `assume(false); unreachable_value()`.

**Ideal proof code:**
```rust
_ => { proof { assert(false) by { /* contradiction from requires */ } } unreachable_value() }
```

**Note:** For simple protocols, unreachable arms don't arise. This is mainly
an RSL IO dispatch pattern.

### P11: Enum Clone Helper

**When needed:** Cloning an enum field of a struct where Verus can't derive
Clone specs automatically.

**Proof code:**
```rust
fn clone_server_role(r: &CServerRole) -> (res: CServerRole)
ensures
    res@ == r@,
    res.valid() == r.valid(),
{
    match r {
        CServerRole::Follower => CServerRole::Follower,
        CServerRole::Candidate => CServerRole::Candidate,
        CServerRole::Leader => CServerRole::Leader,
    }
}
```

**Trigger:** When a struct field is an enum type without `#[derive(Copy)]` and
needs to be cloned to build a new struct.

### P12: Vec Clone Helper (External Body)

**When needed:** Cloning a `Vec<T>` where `T` has a View impl, and the proof
needs `res@.map(f) =~= v@.map(f)`.

**Proof code:**
```rust
#[verifier(external_body)]
fn clone_log(v: &Vec<CLogEntry>) -> (res: Vec<CLogEntry>)
ensures
    res@ == v@,
    res@.map(|i: int, e: CLogEntry| e@) =~= v@.map(|i: int, e: CLogEntry| e@),
{
    v.clone()
}
```

**Why `external_body`:** Verus can prove `res@ == v@` from clone, but can't
derive the mapped equality automatically.

**Trigger:** Any `Vec<ComplexType>.clone()` where the View maps through element
views.

## Decision Tree: When to Emit Each Pattern

```
For each generated function:
1. Does it construct HashSet::new() / Vec::new()?
   → Emit lemma_empty_set_map / lemma_empty_seq_map (P1) in proof block
   → Only once per file (dedup)

2. Does it call HashSet::insert()?
   → Emit `broadcast use Set::lemma_set_map_insert_commute;` (P2) in proof block

3. Does it call HashSet::remove()?
   → Emit lemma_set_map_remove_commute (P3) helper + call in proof block
   → Only once per file (dedup)

4. Does it call Vec::push() where View maps element type?
   → Emit lemma_seq_push_map_commute (P7) helper + call in proof block
   → Only once per file (dedup)

5. Does it clone a Vec<ComplexType>?
   → Emit clone helper (P12) with mapped view ensures

6. Does it clone an enum field?
   → Emit enum clone helper (P11) with view/valid preservation

7. Does the spec have `recommends` clauses?
   → Extract as `requires` clauses (P6)

8. Are there unreachable match arms?
   → Emit `assume(false)` for now (P10, RSL-only)
```

## Generalizable vs Protocol-Specific

**Fully generalizable (emit for all protocols):**
- P1: Empty collection map (when HashSet/Vec constructed empty)
- P2: HashSet insert commutativity (when insert used)
- P3: HashSet remove commutativity (when remove used)
- P5: Validity propagation (automatic for simple valid())
- P6: Enum variant preconditions (from spec recommends)
- P8: HashMap insert identity (automatic)
- P9: clone_hashset spec (already in library)

**Semi-generalizable (need type-specific variants):**
- P7: Seq push commutativity (depends on element type and map function)
- P11: Enum clone helper (depends on enum variants)
- P12: Vec clone helper (depends on element View type)

**RSL-specific (IO dispatch layer):**
- P4: Complex struct decomposition (deep abstractify functions)
- P10: Unreachable arms from IO dispatch requires
