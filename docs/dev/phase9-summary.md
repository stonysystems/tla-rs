# Phase 9: Code Generation Fixes - Summary

**Date**: 2026-02-04
**Status**: Plan Created, Implementation Pending

## Overview

This document summarizes the issues found in generated code and the plan to fix them.

## Issues Identified from election_gen.rs

By analyzing the manual corrections in `src/generated/RSL/election_gen.rs`, we identified **8 major translation issues** preventing compilation:

### 1. Vector View Functions
**Problem**: Generated `self.field@` but needs `.map(|i, elem: T| elem@)` for Vec<T>

**Location**: Lines 62-63 in election_gen.rs
```rust
// ❌ Wrong: requests_received_this_epoch: self.requests_received_this_epoch@,
// ✅ Right:
requests_received_this_epoch: self.requests_received_this_epoch@.map(|i, r:CRequest| r@),
```

### 2. HashSet View Functions
**Problem**: HashSet<u64> needs `.map(|x: u64| x as int)` for Set<int>

**Location**: Lines 56-57
```rust
// ❌ Wrong: current_view_suspectors: self.current_view_suspectors@,
// ✅ Right:
current_view_suspectors: self.current_view_suspectors@.map(|x:u64| x as int),
```

### 3. Vector Validity Predicates
**Problem**: Vec<T> fields need forall checks, not simple .valid()

**Location**: Lines 40-42
```rust
// ✅ Right:
&&& (forall |i:int| 0 <= i < self.requests_received_this_epoch@.len()
    ==> self.requests_received_this_epoch@[i].valid())
```

### 4. Enum Pattern Matching
**Problem**: `enum is Variant` syntax doesn't work in exec, needs match statements

**Location**: Lines 104-112
```rust
// ❌ Wrong:
if ((lengthBound is UpperBoundFinite) && ((0 <= lengthBound.n) ...

// ✅ Right: Use match statement
match lengthBound {
    CUpperBound::CUpperBoundFinite { n } => {
        if 0 <= *n && (*n as usize) < s.len() { ... }
    }
    CUpperBound::CUpperBoundInfinite => s.clone(),
}
```

### 5. EndPoint Comparisons
**Problem**: Can't use `==` for EndPoint, need special function

**Location**: Lines 123-124
```rust
// ❌ Wrong: r1.client == r2.client
// ✅ Right:
do_end_points_match(&r1.client, &r2.client)
```

### 6. Type Refinement Checks
**Problem**: Unnecessary `expr is Type` checks in exec code

**Location**: Line 123 (commented out)
```rust
// ❌ Wrong: ((r1 is Request) && ((r2 is Request) && ...
// ✅ Right: Remove type checks (parameters are already typed)
do_end_points_match(&r1.client, &r2.client) && r1.seqno == r2.seqno
```

### 7. Vector Operations
**Problem**: No `.subrange()` in exec, needs while loop

**Location**: Lines 106-107
```rust
// ❌ Wrong: s.subrange(0, lengthBound.n)
// ✅ Right: Need while loop to construct new vec
let mut result = Vec::new();
let mut i = 0;
while i < n {
    result.push(s[i].clone());
    i += 1;
}
result
```

### 8. Integer Casts
**Problem**: Missing `as u64` when comparing with `.len()`

**Location**: Line 80
```rust
// ✅ Right:
if ((b.proposer_id + 1) < c.config.replica_ids.len() as u64) {
```

## Files to Translate

After fixing the transpiler, translate these 4 spec files:

### 1. parameters.rs (Simplest)
- **Input**: `src/protocol/RSL/parameters.rs`
- **Output**: `src/generated/RSL/parameters_gen.rs`
- **Complexity**: Low - simple struct with int fields
- **Challenges**: int → u64 conversions, UpperBound enum handling

### 2. constants.rs
- **Input**: `src/protocol/RSL/constants.rs`
- **Output**: `src/generated/RSL/constants_gen.rs`
- **Complexity**: Low - composition of other structs
- **Challenges**: Nested struct View implementations

### 3. configuration.rs
- **Input**: `src/protocol/RSL/configuration.rs`
- **Output**: `src/generated/RSL/configuration_gen.rs`
- **Complexity**: Medium - has helper functions
- **Challenges**: Set/Seq of EndPoint, quantifiers, external helper calls

### 4. message.rs (Most Complex)
- **Input**: `src/protocol/RSL/message.rs`
- **Output**: `src/generated/RSL/message_gen.rs`
- **Complexity**: High - large enum with 10 variants
- **Challenges**: Each variant needs View impl, validity for all cases

## Implementation Plan

See `TODO.md` Phase 9 for detailed task breakdown:

### Phase 9.1: Core Type System Fixes (Week 1-2)
- Vector view function generation
- HashSet view function generation
- Vector validity predicate generation

### Phase 9.2: Expression Translation Fixes (Week 1-2)
- Enum "is" operator to match conversion
- EndPoint comparison function injection
- Type refinement check removal
- Integer cast insertion

### Phase 9.3: Collection Operation Translation (Week 3)
- Vector subrange to while loop
- Vector concatenation to extend
- Empty collection constructors

### Phase 9.4: Spec File Translation (Week 4)
- Translate parameters.rs
- Translate constants.rs
- Translate configuration.rs
- Translate message.rs

### Phase 9.5: Integration and Validation (Week 5)
- Re-generate election_gen.rs
- Update module imports
- Compilation verification
- Compare with manual implementations

### Phase 9.6: Testing and Documentation (Week 6)
- Add transpiler test cases
- Update translation rules doc
- Create phase 9 summary
- Update main README

## Success Criteria

Phase 9 complete when:

1. ✅ All 8 transpiler issues fixed with passing tests
2. ✅ 4 new spec files translated and compiling
3. ✅ `scons --verus-path=$VERUS_PATH` succeeds (0 errors)
4. ✅ Regenerated election_gen.rs matches manual corrections
5. ✅ At least 9 new transpiler tests added
6. ✅ Documentation updated

## Critical Files for Implementation

1. **`transpiler/src/codegen/mod.rs`** - Type generation (View, validity)
2. **`transpiler/src/translator/mod.rs`** - Expression transformation
3. **`transpiler/src/printer/mod.rs`** - Code output
4. **`src/generated/RSL/election_gen.rs`** - Reference with manual fixes
5. **`docs/dev/translation-rules.md`** - Complete rules specification

## Key Resources

- **Translation Rules**: `docs/dev/translation-rules.md` - Complete specification
- **Manual Reference**: `src/generated/RSL/election_gen.rs` - Working example
- **TODO Plan**: `TODO.md` Phase 9 - Detailed task breakdown
- **Existing Implementations**: `src/implementation/RSL/*.rs` - Patterns to match

## Next Steps

1. Start with **Phase 9.1** - Core type system fixes are foundational
2. Add tests for each fix before moving to next
3. Use election_gen.rs as validation target throughout
4. Translate spec files in order: parameters → constants → configuration → message
5. Regenerate election_gen.rs at end to validate all fixes work together

## Estimated Timeline

- **Weeks 1-2**: Core fixes (Phases 9.1-9.2)
- **Week 3**: Collection operations (Phase 9.3)
- **Week 4**: Spec translation (Phase 9.4)
- **Week 5**: Integration (Phase 9.5)
- **Week 6**: Testing/docs (Phase 9.6)

**Total**: ~6 weeks for complete Phase 9 implementation
