# Phase B3: Verify Generated Types Compile with Verus

## Goal
Make the generated types in `src/generated/RSL/types_gen.rs` compile correctly with Verus.

## Issues to Fix

### 1. Integer Conversion in View Impls
Current generated code:
```rust
open spec fn view(&self) -> Ballot {
    Ballot {
        seqno: self.seqno,  // ERROR: self.seqno is i64, needs int
        proposer_id: self.proposer_id,
    }
}
```

Should be:
```rust
open spec fn view(&self) -> Ballot {
    Ballot {
        seqno: self.seqno as int,
        proposer_id: self.proposer_id as int,
    }
}
```

### 2. Missing Import Configuration
The generated file needs proper imports for:
- Spec types: `Request`, `Reply`, `Ballot`, `Vote`, `ClockReading`, `LearnerTuple`
- Exec types used as fields: `CAbstractEndPoint`, `CAppMessage`, `CRequestBatch`

### Implementation Plan

1. **Update `translate_type()` in codegen** (~30 LOC)
   - Track whether we're generating View impl vs struct definition
   - Add `as int` conversion for i64/u64 fields in View impl

2. **Add View field conversion helper** (~20 LOC)
   - New method `generate_view_field()` that handles conversions
   - For i64/u64: append `as int`
   - For types with View: append `@`
   - For primitives: no conversion

3. **Test the changes** (~50 LOC)
   - Add test that verifies `as int` is present for integer fields
   - Add test for nested types with @ operator

4. **Create a standalone test file** (~30 LOC)
   - Copy generated types_gen.rs with proper imports
   - Verify it compiles (not full Verus verification)

## Estimated LOC: ~130
