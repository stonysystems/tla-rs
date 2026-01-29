# H3: Implement Helper Function Translation

## Status: IN PROGRESS [26:01:29]

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

## Implementation Plan

### 1. Add `translate_helper()` method (~100 LOC)
- Check that function is marked as Helper
- All params become inputs (passed by reference)
- Return type from annotation (translated to exec type)
- Simpler body transformation (no output extraction needed)

### 2. Modify `translate()` to dispatch based on kind (~10 LOC)
- If kind == Predicate: use existing translation
- If kind == Helper: use new `translate_helper()`

### 3. Update `build_ensures_for_helper()` (~30 LOC)
```rust
// For helpers, ensures clause is:
// result.valid(),
// result@ == SpecFunctionName(param1@, param2@, ...)
```

### 4. Handle different return types (~20 LOC)
- Struct types: CStructName
- Collection types: Vec<CType>, HashSet<CType>, HashMap<K, V>
- Primitive types: bool, i64, u64

## Files to Modify
1. `transpiler/src/translator/mod.rs` - Add translate_helper method

## Estimated LOC: ~160
