# F4 Issue 1: Self-Referential Pattern Fix Plan

## Date: 2026-01-28
## Status: COMPLETED

## Problem

In `LLearnerForgetOperationsBefore`, the spec uses a self-referential pattern:

```rust
&&& (forall |k| s_.unexecuted_learner_state.contains_key(k) <==> k >= ops_complete && s.unexecuted_learner_state.contains_key(k))
&&& (forall |k| s_.unexecuted_learner_state.contains_key(k) ==> s_.unexecuted_learner_state[k] == s.unexecuted_learner_state[k])
&&& s_ == LLearner{
    constants:s.constants,
    max_ballot_seen:s.max_ballot_seen,
    unexecuted_learner_state:s_.unexecuted_learner_state  // <-- s_ used before defined!
}
```

The transpiler generates invalid code:
```rust
CLearner {
    constants: s.constants,
    max_ballot_seen: s.max_ballot_seen,
    unexecuted_learner_state: s_.unexecuted_learner_state,  // ERROR: s_ undefined
}
```

## Root Cause

In `try_extract_struct_construction`, when processing `s_ == LLearner{...unexecuted_learner_state: s_.unexecuted_learner_state}`:
1. The function sees `s_.unexecuted_learner_state` in the struct literal RHS
2. It transforms this to `s_.unexecuted_learner_state` in the generated code
3. But `s_` is the output being defined, so it doesn't exist yet

The foralls define what `s_.unexecuted_learner_state` should be, but the transpiler doesn't connect them.

## Solution

### Step 1: Detect Self-Referential Struct Fields

When processing a struct literal `s_ == StructType{..., field: s_.field}`:
1. Check if any field value is `Expr::Field(base, field_name)` where `base` is an output variable
2. If so, mark this as a self-referential field that needs special handling

### Step 2: Find Foralls That Define the Self-Referential Field

Look for forall patterns in the conjunction that define the output field:
- Domain forall: `forall |k| output.field.contains_key(k) <==> domain_pred(k)`
- Value forall: `forall |k| output.field.contains_key(k) ==> output.field[k] == value_expr(k)`

Extract:
- `domain_pred`: The predicate defining which keys are in the map
- `value_expr`: The expression defining the value for each key

### Step 3: Generate Intermediate Variable

Generate a let binding that computes the field value:
```rust
let __s_unexecuted_learner_state = s.unexecuted_learner_state
    .iter()
    .filter(|(k, _)| *k >= ops_complete)
    .cloned()
    .collect();
```

### Step 4: Substitute in Struct Construction

Replace the self-reference with the intermediate variable:
```rust
CLearner {
    constants: s.constants.clone(),
    max_ballot_seen: s.max_ballot_seen.clone(),
    unexecuted_learner_state: __s_unexecuted_learner_state,
}
```

## Implementation Location

Modify `try_extract_struct_construction` in `transpiler/src/translator/mod.rs`:

1. Add helper: `detect_self_referential_fields(struct_expr, ctx) -> Vec<(String, String)>`
   - Returns list of (output_var, field_name) pairs that are self-referential

2. Add helper: `find_field_defining_foralls(field_name, exprs, ctx) -> Option<(Expr, Expr)>`
   - Returns (domain_pred, source_map) from foralls that define the field

3. Modify `try_extract_struct_construction`:
   - Before generating struct, detect self-referential fields
   - For each self-referential field, find defining foralls
   - Generate intermediate variable with filter expression
   - Add let binding to result
   - Substitute intermediate variable in struct fields

## Test Cases

1. `LLearnerForgetOperationsBefore` - map filter with k >= threshold
2. Similar patterns in replica.rs

## Expected Output

For `CLearnerForgetOperationsBefore`:
```rust
pub exec fn CLearnerForgetOperationsBefore(s: &CLearner, ops_complete: &COperationNumber) -> (result: CLearner)
requires
    s.valid(),
    ops_complete.valid(),
ensures
    result.valid(),
    LLearnerForgetOperationsBefore(s@, result@, ops_complete@),
{
    let __s_unexecuted_learner_state: HashMap<COperationNumber, CLearnerTuple> =
        s.unexecuted_learner_state
            .iter()
            .filter(|(k, _)| (*k >= *ops_complete))
            .cloned()
            .collect();
    CLearner {
        constants: s.constants.clone(),
        max_ballot_seen: s.max_ballot_seen.clone(),
        unexecuted_learner_state: __s_unexecuted_learner_state,
    }
}
```

## Estimated LOC

- detect_self_referential_fields: ~30 LOC
- find_field_defining_foralls: ~60 LOC
- Integration in try_extract_struct_construction: ~40 LOC
- Total: ~130 LOC
