# Phase 3: Invariant Templates for Common Patterns

## Objective
Create invariant templates that generate correct loop invariants for common iteration patterns.

## Current State (Phase 2 Complete)
The transpiler generates loop structure when `generate_loops_for_verification: true`:
```rust
{
    let m_keys = source.keys();
    let mut result: HashMap<_, _> = HashMap::new();
    for key in iter:m_keys
    invariant
        // TODO: Add loop invariants for verification
    {
        if filter_condition { ... }
    }
    result
}
```

## Target Output
```rust
{
    let m_keys = source.keys();
    let ghost mut seen_keys = Set::<K>::empty();
    let mut result: HashMap<K, V> = HashMap::new();
    for key in iter:m_keys
    invariant
        seen_keys.subset_of(source@.dom()),
        forall |k| seen_keys.contains(k) ==> source@.contains_key(k),
        forall |k| result@.contains_key(k) ==> filter_pred(k) && source@.contains_key(k),
        forall |k| result@.contains_key(k) ==> seen_keys.contains(k),
        forall |k| seen_keys.contains(k) && filter_pred(k) ==> result@.contains_key(k),
    {
        proof { seen_keys = seen_keys.insert(*key); }
        if filter_condition { ... }
    }
    result
}
```

## Implementation Steps

### Step 1: Define Invariant Template Structs (~50 LOC)
```rust
pub enum InvariantTemplate {
    /// Filter elements from a map based on key predicate
    MapFilter {
        source_map: String,
        key_var: String,
        filter_pred: String,  // String representation of filter predicate
    },
    /// Initialize sequence with constant elements
    SeqInit {
        length_expr: String,
        element_expr: String,
    },
    /// Update map with new entry and filter
    MapUpdate {
        source_map: String,
        key_var: String,
        filter_pred: String,
        new_key: String,
        new_value: String,
    },
}
```

### Step 2: Create MapFilter Invariant Generator (~80 LOC)
```rust
fn generate_map_filter_invariants(
    source_map: &str,
    key_var: &str,
    filter_pred: &str,
) -> Vec<String> {
    vec![
        format!("seen_keys.subset_of({}@.dom())", source_map),
        format!("forall |{k}| seen_keys.contains({k}) ==> {src}@.contains_key({k})",
                k=key_var, src=source_map),
        format!("forall |{k}| result@.contains_key({k}) ==> {pred} && {src}@.contains_key({k})",
                k=key_var, pred=filter_pred, src=source_map),
        format!("forall |{k}| result@.contains_key({k}) ==> seen_keys.contains({k})",
                k=key_var),
        format!("forall |{k}| seen_keys.contains({k}) && {pred} ==> result@.contains_key({k})",
                k=key_var, pred=filter_pred),
    ]
}
```

### Step 3: Update generate_map_filter_loop (~100 LOC)
- Add ghost variable for `seen_keys`
- Call invariant generator
- Add proof block to update `seen_keys`

### Step 4: Add Filter Predicate Stringification (~50 LOC)
- Convert ExecExpr to string representation for invariants
- Handle common patterns: comparisons, field access, etc.

### Step 5: Add Tests (~30 LOC)
- Test invariant generation for map filter
- Verify generated code structure

## Estimated: ~300 LOC total

## Key Insight
The invariants follow a standard pattern for any map filter operation:
1. Track which keys we've seen (ghost state)
2. Result only contains keys we've seen
3. Result contains all seen keys matching filter
4. All result keys satisfy the filter

This pattern can be parameterized by:
- Source map name
- Key variable name
- Filter predicate expression
