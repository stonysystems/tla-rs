# F2: Election Module Analysis

**Date**: 2026-01-28
**Task**: Use election.rs as test case for making transpiler generate verifiable code.

## Generated Code Overview

Successfully generated `src/generated/RSL/election_gen.rs` with 6 functions:
- `CElectionStateInit`
- `CElectionStateProcessHeartbeat`
- `CElectionStateCheckForViewTimeout`
- `CElectionStateCheckForQuorumOfViewSuspicions`
- `CElectionStateReflectReceivedRequest`
- `CElectionStateReflectExecutedRequestBatch`

## Key Transpiler Improvements Made

### 1. Exists Quantifier with Disjunction (FIXED)
**Pattern**: `exists |x| (c1.contains(x) || c2.contains(x)) && pred(x)`

**Generated code**:
```rust
es.requests_received_prev_epochs.iter()
  .chain(es.requests_received_this_epoch.iter())
  .any(|earlier_req| CRequestsMatch(&earlier_req, &req))
```

This was a new pattern not previously supported. Added:
- `extract_contains_disjunction()` helper
- `extract_exists_containers_and_pred()` for multiple containers
- Chain generation for multiple iterators

## Remaining Gaps

### 1. Primitive Type Validity Check
**Issue**: Generated code calls `clock.valid()` on `&i64`
**Location**: Line 45, 93, etc.
**Fix needed**: Don't generate `valid()` calls for primitive types (i64, u64, bool)

### 2. Empty Collection Constructor
**Issue**: `Cempty()` used for empty Vec/HashSet
**Location**: Lines 33-37, 74, 78, etc.
**Fix needed**: Use `Vec::new()` for sequences, `HashSet::new()` for sets

### 3. Method Style Mismatch
**Manual code**: `pub fn CElectionStateInit(c: CReplicaConstants) -> Self` (pass by value, returns Self)
**Generated code**: `pub fn CElectionStateInit(c: &CReplicaConstants) -> CElectionState` (pass by reference)

This affects:
- Clone requirements (manual may not need clone, generated always clones)
- Method chaining in callers

### 4. Missing Proof Blocks
**Manual code** has extensive proof blocks:
```rust
proof {
    let rcv = rc@;
    assert(rcv.constants == cv);
    // ... many assertions
}
```

**Generated code** has no proof blocks.

For simple functions, proof blocks may not be needed. For complex ones, verification may fail without them.

### 5. Optimization Fields
**Manual `CElectionState`** has optimization fields:
```rust
pub cur_req_set: HashSet<CRequestHeader>,
pub prev_req_set: HashSet<CRequestHeader>,
```

These are not in the spec and not generated. Would need separate optimization pass.

### 6. Iterator Patterns May Not Verify
The generated code uses iterator patterns:
```rust
es.requests_received_prev_epochs.iter()
  .chain(es.requests_received_this_epoch.iter())
  .any(|earlier_req| CRequestsMatch(&earlier_req, &req))
```

Verus may not be able to verify this automatically. Manual code might use explicit loops.

## Comparison: CElectionStateInit

### Manual (src/implementation/RSL/ElectionImpl.rs:225-271)
- Takes `c: CReplicaConstants` by value
- Creates explicit local variables for each field
- Has proof block with 8 assertions
- Uses `c.clone_up_to_view()` for constants
- Includes optimization fields (cur_req_set, prev_req_set)

### Generated (src/generated/RSL/election_gen.rs:19-39)
- Takes `c: &CReplicaConstants` by reference
- Direct struct construction
- No proof block
- Uses `c.clone()` for constants
- No optimization fields

## Recommendations

### High Priority (Blocking Verification)
1. Fix primitive type `valid()` calls
2. Replace `Cempty()` with proper constructors
3. Test if iterator patterns verify

### Medium Priority
4. Add configurable proof block generation
5. Support pass-by-value option for function parameters

### Low Priority
6. Support optimization fields (requires spec/impl separation knowledge)
7. Generate `clone_up_to_view()` style methods

## Next Steps

1. Fix the primitive type validity check in transpiler
2. Replace Cempty() with proper constructors
3. Run Verus on the generated election code to see what fails
4. Document remaining verification gaps
