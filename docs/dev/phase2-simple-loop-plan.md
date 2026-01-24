# Phase 2: Simple Loop Generation Plan

## Objective
Replace iterator patterns like `.iter().filter().collect()` with explicit for loops
that can be extended with invariants later.

## Current State
The translator generates iterator chains in several places:
1. `QuantifierTemplate::MapFilter` - line ~2980
2. `try_extract_map_filter_conjunction` - line ~803
3. `transform_forall_with_template` - line ~2884
4. Set filter patterns - line ~3012
5. Map comprehensions - line ~3055

## Approach
Add a configuration flag `generate_loops_for_verification: bool` to control output format.
When true, generate explicit loops instead of iterator chains.

## Implementation Steps

### Step 1: Add Configuration Flag (~20 LOC)
Add to `TranslatorConfig`:
```rust
pub generate_loops_for_verification: bool,
```

### Step 2: Create Loop Generation Helper (~80 LOC)
Add helper method to generate the loop structure:
```rust
fn generate_map_filter_loop(
    &self,
    source_map: String,
    key_var: String,
    filter_expr: ExecExpr,
    ctx: &TransformContext,
) -> ExecExpr
```

### Step 3: Update MapFilter Template (~30 LOC)
Modify `QuantifierTemplate::MapFilter` handling to use loop when flag is set.

### Step 4: Update Map Filter Conjunction (~30 LOC)
Modify `try_extract_map_filter_conjunction` result handling.

### Step 5: Add Tests (~40 LOC)
- Test loop generation with config flag enabled
- Test iterator generation with config flag disabled

## Generated Loop Structure (no invariants yet)
```rust
{
    let m_keys = source.keys();
    let mut result: HashMap<K, V> = HashMap::new();
    for key in iter:m_keys {
        if filter_condition {
            let value = source.get(&key);
            match value {
                Some(v) => { result.insert(key, v.clone()); }
                None => { }
            }
        }
    }
    result
}
```

## Estimated: ~200 LOC total
