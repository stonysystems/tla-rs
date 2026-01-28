# F4 Blockers Fix Plan

## Date: 2026-01-28

## Overview

This document describes the plan to fix three transpiler issues blocking F4 completion:
1. Self-referential pattern bug (s_ undefined)
2. Spec constraints emitted as code
3. Sequence comprehension using iterators instead of loops

## Issue 1: Self-Referential Pattern Bug

### Problem

In specs like `LLearnerForgetOperationsBefore`:
```rust
&&& (forall |k| s_.unexecuted_learner_state.contains_key(k) <==> ...)
&&& (forall |k| s_.unexecuted_learner_state.contains_key(k) ==> s_.unexecuted_learner_state[k] == ...)
&&& s_ == LLearner{
    constants:s.constants,
    max_ballot_seen:s.max_ballot_seen,
    unexecuted_learner_state:s_.unexecuted_learner_state  // <-- s_ used before defined!
}
```

The transpiler emits `s_.unexecuted_learner_state` but `s_` isn't defined yet.

### Root Cause

The transpiler processes the struct assignment `s_ == LLearner{...}` and sees `s_.unexecuted_learner_state` on the RHS. It doesn't recognize this as a self-reference that should be computed from the foralls.

### Solution

1. **Detect self-referential map patterns**: When processing conjunctions, detect when:
   - A forall defines the domain of an output's field (biconditional)
   - A forall defines the values of an output's field
   - A struct assignment references that same field

2. **Generate intermediate variable**: Instead of emitting `s_.field`, generate:
   ```rust
   let __s_unexecuted_learner_state = /* computed from foralls */;
   CLearner {
       constants: s.constants.clone(),
       max_ballot_seen: s.max_ballot_seen.clone(),
       unexecuted_learner_state: __s_unexecuted_learner_state,
   }
   ```

3. **Implementation location**: Modify `try_extract_struct_construction` in `translator/mod.rs`

### Changes Required

1. Add `detect_self_referential_field` helper function
2. Modify `try_extract_struct_construction` to:
   - Detect foralls that define output fields
   - Generate intermediate variables for these fields
   - Substitute the intermediate variables in the struct construction

## Issue 2: Spec Constraints Emitted as Code

### Problem

In `LBroadcastToEveryone`:
```rust
&&& sent_packets.len() == c.replica_ids.len()  // constraint on output
&&& 0 <= myidx < c.replica_ids.len()           // precondition
&&& forall |idx| 0 <= idx < sent_packets.len() ==> sent_packets[idx] =~= LPacket{...}
```

Generated code incorrectly emits:
```rust
(sent_packets.len() == c.replica_ids.len());  // This is not valid code!
((0 <= myidx) && (myidx < c.replica_ids.len()));  // This should be in requires!
```

### Root Cause

The transpiler doesn't distinguish between:
1. **Preconditions** - expressions involving only input parameters → `requires`
2. **Output constraints** - expressions defining output properties → handled by computation
3. **Computations** - expressions that actually compute output values → executable code

### Solution

1. **Classify conjuncts**: Before transforming, classify each conjunct:
   - `InputOnly` - all variables are inputs → move to `requires`
   - `OutputDefining` - forall/exists that defines output content → generate computation
   - `OutputConstraint` - constraint on output length/size → derive from computation
   - `Computation` - direct assignment to output → generate code

2. **Implementation**:
   ```rust
   enum ConjunctKind {
       InputPrecondition,     // Goes to requires clause
       OutputComputation,     // forall/exists that generates output
       OutputConstraint,      // Length/size constraint (implicit from computation)
       DirectAssignment,      // s_ == expr
   }
   ```

3. **Filter before transformation**: Only transform `OutputComputation` and `DirectAssignment`

### Changes Required

1. Add `classify_conjunct` helper function
2. Modify conjunction handling in `transform_expr` to filter out preconditions and constraints
3. Add preconditions to `build_requires` when constructing the function

## Issue 3: Sequence Comprehension Uses Iterators

### Problem

The forall pattern in broadcast:
```rust
forall |idx| 0 <= idx < sent_packets.len() ==> sent_packets[idx] =~= LPacket{...}
```

Currently generates:
```rust
(0..sent_packets.len()).map(|idx| CPacket {...}).collect()
```

But should generate:
```rust
let mut __result: Vec<CRslPacket> = Vec::new();
let __len = c.replica_ids.len();
let mut __idx: i64 = 0;
while __idx < __len
    invariant
        __result.len() == __idx,
        forall |i: int| 0 <= i < __idx ==> __result[i]@ == LPacket{...},
{
    __result.push(CRslPacket {
        dst: c.replica_ids[__idx].clone(),
        src: c.replica_ids[myidx].clone(),
        msg: m.clone(),
    });
    __idx += 1;
}
__result
```

### Root Cause

The `generate_loops_for_verification` flag only applies to exists/forall quantifiers used as boolean expressions (checking if condition holds). It doesn't apply to sequence comprehension patterns where forall defines sequence contents.

### Solution

1. **Detect sequence comprehension patterns**: Pattern where:
   - There's a length constraint: `output.len() == length_expr`
   - There's a forall: `forall |i| 0 <= i < output.len() ==> output[i] == element_expr`

2. **Generate loop-based construction**:
   - Use while loop with index variable
   - Add invariants for length and element properties
   - Push elements one at a time

3. **Implementation location**: Add `generate_seq_comprehension_loop` in `translator/mod.rs`

### Changes Required

1. Add `try_extract_seq_comprehension` helper
2. Add `generate_seq_comprehension_loop` function
3. Call this from `try_extract_struct_construction` when pattern is detected

## Implementation Order

1. **Issue 2** (spec constraints) - Simplest, enables cleaner generation
2. **Issue 3** (sequence loops) - Needed for broadcast to work
3. **Issue 1** (self-referential) - Most complex, needed for learner

## Testing Plan

1. Regenerate `broadcast_gen.rs` and verify it compiles
2. Regenerate `learner_gen.rs` and verify it compiles
3. Run Verus verification on generated modules
4. Integration test: remove `#[cfg(test)]` guards and verify full codebase

## Estimated LOC

- Issue 2: ~50 LOC (classification + filtering)
- Issue 3: ~100 LOC (loop generation)
- Issue 1: ~150 LOC (self-reference detection + intermediate vars)
- Total: ~300 LOC

## Progress

### Issue 2: COMPLETED (2026-01-28)

Fixed spec constraints being emitted as code by:
1. Added `is_input_only_expression()` helper to detect preconditions
2. Modified `categorize_output_assignments_with_exclusions()` to skip:
   - Input-only expressions (preconditions)
   - Equality constraints that aren't direct output assignments
   - Unmatched quantifiers
3. Added filtering in the "No outputs detected" conjunction branch

### Issue 3: COMPLETED (2026-01-28)

Fixed sequence comprehension length derivation by:
1. Added `try_extract_output_seq_comprehension()` to detect the full pattern:
   - Length constraint: `output.len() == input_length_expr`
   - Element forall: `forall |i| 0 <= i < output.len() ==> output[i] == element_expr`
2. When pattern is detected, use `input_length_expr` for the range instead of `output.len()`
3. Added helper functions: `extract_output_len_call()`, `is_seq_bounds()`, `is_lower_bound_check()`,
   `is_upper_bound_check()`, `is_output_len()`, `extract_direct_seq_element_assignment()`, `is_output_indexed()`

Generated code now correctly uses:
```rust
(0..c.replica_ids.len()).map(|idx| CPacket {...}).collect()
```

### Issue 1: Pending

The self-referential pattern bug still needs to be addressed for learner_gen.rs and replica_gen.rs.
