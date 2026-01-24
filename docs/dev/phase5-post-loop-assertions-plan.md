# Phase 5: Post-loop Assertions

## Objective
Add post-loop assertions and proof helpers to complete the verification of generated loops.

## Current State (Phase 4 Complete)
The generated loop includes:
- Pre-loop assertions for iterator state
- In-loop assertions (broadcast use, assume key in source)
- Ghost variable `seen_keys` with proof block update
- 5 loop invariants

## Required Post-Loop Assertions

Based on manual `CRemoveVotesBeforeLogTruncationPoint`:

### Termination Assertions
```rust
// After loop completes:
assert(seen_keys.subset_of(source@.dom()));
assert(forall |k| seen_keys.contains(k) ==> source@.contains_key(k));
assume(m_keys@.0 == m_keys@.1.len()); // Verus can't infer this
assume(seen_keys.len() == m_keys@.0);
assert(seen_keys.len() == m_keys@.1.len());
proof { subset_len_equal_implies_equal(seen_keys, source@.dom()) };
assert(seen_keys == source@.dom());
```

### Postcondition Assertions
```rust
assert(forall |k| result@.contains_key(k) <==> seen_keys.contains(k) && filter_pred(k));
assert(forall |k| source@.contains_key(k) && filter_pred(k) ==> result@.contains_key(k));
assert(forall |k| result@.contains_key(k) ==> filter_pred(k) && source@.contains_key(k) && result@[k] == source@[k]);
assert(forall |k| !filter_pred(k) ==> !result@.contains_key(k));
```

## Implementation Steps

### Step 1: Add post-loop assertions helper (~50 LOC)
```rust
fn generate_post_loop_assertions(
    &self,
    iter_name: &str,
    source_map: &str,
    key_var: &str,
    filter_pred: &str,
) -> Vec<ExecExpr>
```

### Step 2: Integrate into generate_map_filter_loop (~20 LOC)
Add post-loop assertions before the final `result` return.

### Step 3: Add tests (~30 LOC)
- Verify post-loop assertions are generated
- Check correct assertion content

## Estimated: ~100 LOC total
