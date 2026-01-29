# H5: Update Code Generation Pipeline

## Status: COMPLETE [26:01:29]

## Goal
Update the code generation pipeline to process helper functions alongside predicates.

## Analysis

The existing `transpile_file()` function in `lib.rs` already:
1. Parses all spec functions from the input file
2. Parses all annotations from the annotation file
3. For each spec function with a matching annotation, calls the translator
4. The translator dispatches based on `FunctionKind` (added in H3)

No additional changes are needed because:
- H2 extended annotations to support `helper` keyword with return types
- H3 added `translate_helper()` method and dispatch logic in `translate()`
- The pipeline automatically handles both predicates and helpers

## Verification

Tested with election module:

```bash
./target/debug/verus-transpile \
  -i ../src/protocol/RSL/election.rs \
  -a ../src/protocol/RSL/election.automan \
  -c ../src/protocol/RSL/election_transpile.toml \
  --stdout
```

Generated helper functions:
- `CComputeSuccessorView(b: &CBallot, c: &CConstants) -> CBallot`
- `CBoundRequestSequence(s: &Vec<CRequest>, lengthBound: &CUpperBound) -> Vec<CRequest>`
- `CRequestsMatch(r1: &CRequest, r2: &CRequest) -> bool`
- `CRequestSatisfiedBy(r1: &CRequest, r2: &CRequest) -> bool`

All with proper:
- Requires clauses for validity
- Ensures clauses with spec linkage (`result@ == SpecFn(...)`)
- Correct type translations

## Files Modified

1. `src/protocol/RSL/election.automan` - Added helper function annotations

## Remaining Items

H6-H8 still needed to:
- Remove manual implementation dependencies
- Test with complete election module
- Apply to all RSL modules

## Notes

- Recursive helpers (`RemoveAllSatisfiedRequestsInSequence`, `RemoveExecutedRequestBatch`) still need H4 implementation
- Some generated code calls these undefined recursive helpers - will fail to compile until H4 is complete
