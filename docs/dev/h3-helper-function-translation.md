# H3: Implement Helper Function Translation

## Status: COMPLETE [26:01:29]

## Goal
Add translation support for helper functions (non-predicate spec functions).

## Difference from Predicates

### Predicates
- Have input (+) and output (-) parameters
- Return type is bool
- Body describes relationship between inputs and outputs
- Translation extracts output assignments from body

### Helper Functions
- All parameters are inputs (+)
- Return type is non-bool (Ballot, Seq<Request>, etc.)
- Body directly computes the return value
- Translation is simpler: transform body to exec expressions

## Example Transformation

### Input (spec)
```rust
pub open spec fn ComputeSuccessorView(b: Ballot, c: LConstants) -> Ballot {
    if b.proposer_id + 1 < c.config.replica_ids.len() {
        Ballot{seqno: b.seqno, proposer_id: b.proposer_id + 1}
    } else {
        Ballot{seqno: b.seqno + 1, proposer_id: 0}
    }
}
```

### Output (exec)
```rust
pub exec fn CComputeSuccessorView(b: &CBallot, c: &CConstants) -> (result: CBallot)
requires
    b.valid(),
    c.valid(),
ensures
    result.valid(),
    result@ == ComputeSuccessorView(b@, c@),
{
    if b.proposer_id + 1 < c.config.replica_ids.len() as i64 {
        CBallot { seqno: b.seqno, proposer_id: b.proposer_id + 1 }
    } else {
        CBallot { seqno: b.seqno + 1, proposer_id: 0 }
    }
}
```

## Implementation Summary

### 1. Modified `translate()` to dispatch based on kind
- Added import for `FunctionKind` in translator
- Modified `translate()` to call `translate_predicate()` or `translate_helper()` based on `func.kind`

### 2. Added `translate_helper()` method
- All params become inputs (passed by reference)
- Return type from annotation (translated to exec type)
- Simpler body transformation (no output extraction needed)

### 3. Added `translate_type_string()` method
- Parses return type strings from annotations (e.g., "Seq<Request>")
- Handles generic types: Seq -> Vec, Set -> HashSet, Map -> HashMap
- Handles primitive types: bool, int -> i64, nat -> u64
- Handles struct types: translates using L->C prefix rules

### 4. Added helper-specific methods
- `translate_helper_params()`: translates all params as immutable references
- `build_helper_return_type()`: builds return type from annotation or spec function
- `build_helper_requires()`: generates validity requirements for all params
- `build_helper_ensures()`: generates `result.valid()` and spec linkage
- `build_helper_spec_call()`: generates `result@ == SpecFn(param1@, param2@, ...)`

## Files Modified
1. `transpiler/src/translator/mod.rs` - Added translate_helper method and helpers (~150 LOC)

## Tests Added
- `test_translate_type_string_simple` - tests primitive and struct type translation
- `test_translate_type_string_generic` - tests Seq, Set, Map type translation
- `test_translate_helper_simple` - tests basic helper function translation
- `test_translate_helper_bool_return` - tests bool-returning helpers (no result.valid())
- `test_translate_helper_seq_return` - tests collection-returning helpers
- `test_build_helper_spec_call` - tests spec linkage generation
