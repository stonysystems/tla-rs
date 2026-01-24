# Phase 4: Ghost Code Generation

## Objective
Add pre-loop assertions/assumes and in-loop proof helpers to make generated loops verify.

## Current State (Phase 3 Complete)
The generated loop structure includes:
- Ghost variable `seen_keys`
- 5 loop invariants
- Proof block to update `seen_keys`
- Broadcast use for hash axioms (before loop)

## Required Additional Ghost Code

### Pre-Loop Assertions
Based on manual `CRemoveVotesBeforeLogTruncationPoint`:
```rust
let m_keys = votes.keys();
assert(m_keys@.0 == 0);
assume(m_keys@.1.len() == votes@.len());
assert(m_keys@.1.to_set() =~= votes@.dom());
let ghost mut seen_keys = Set::empty();
assert(seen_keys == m_keys@.1.take(m_keys@.0).to_set());
let mut result = HashMap::new();
assert(result@ == Map::empty());
```

### In-Loop Assertions
```rust
for key in iter:m_keys
invariant ...
{
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    assume(votes@.contains_key(*key));
    assert(forall |opn| result@.contains_key(opn) ==> seen_keys.contains(opn));
    proof { seen_keys = seen_keys.insert(*key); }
    ...
}
```

## Implementation Steps

### Step 1: Add pre-loop assertions (~30 LOC)
- Assert iterator starts at 0
- Assume iterator length matches map length
- Assert iterator to_set matches map domain
- Assert empty seen_keys matches take(0)
- Assert result is empty map

### Step 2: Add in-loop assertions (~30 LOC)
- Add broadcast use at loop start
- Assume current key is in source map
- Assert result subset property before update

### Step 3: Update tests (~40 LOC)
- Verify pre-loop assertions are generated
- Verify in-loop assertions are generated

## Estimated: ~100 LOC total
