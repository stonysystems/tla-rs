# Verus Integration Plan for Generated Code

## Status [2026-01-25, 03:00]

### Current State

**Completed:**
- ✅ Main codebase compiles with Verus (456 verified, 0 errors)
- ✅ Integration test file created (`src/implementation/RSL/generated_acceptor_test.rs`)
- ✅ Type compatibility issues fixed (HashMap::new(), .clone() for struct fields)
- ✅ Configurable validity predicate name

**Blocked:**
- ❌ Generated code passes Verus proofs - requires loop generation with invariants

### Findings

1. **Main codebase compiles**: The main tla-rs codebase compiles with Verus (warnings only, no errors)
   - Command: `/home/shuai/tools/verus-x86-linux/verus src/lib.rs --crate-type=lib`
   - Result: 456 verified, 0 errors (57 deprecation warnings)

2. **Generated code patterns**: The transpiler generates code using:
   - Iterator methods: `.iter().filter().collect()`
   - High-level patterns without explicit loop invariants
   - Simpler type signatures without `well_formed()` predicates

3. **Manual implementation patterns**: The existing acceptorimpl.rs uses:
   - Explicit for loops with invariants
   - Ghost variables and assume statements
   - `well_formed()` and `valid()` predicates
   - Complex proof assertions

### Challenges

1. **Pattern Mismatch**: The generated code uses iterator patterns that may not be directly verifiable:
   ```rust
   // Generated:
   votes.iter().filter(|(opn, _)| (opn >= log_truncation_point)).collect()

   // Manual:
   for key in iter:m_keys
   invariant
       seen_keys.subset_of(votes@.dom()),
       // ... detailed invariants
   ```

2. **Missing Predicates**: Generated code uses `well_formed()` in requires/ensures, but this needs to be:
   - Either defined on the types
   - Or translated to the actual validity predicates

3. **Type Signatures**: Generated functions have different parameter types:
   - Generated: `log_truncation_point: &COperationNumber`
   - Manual: `log_truncation_point: COperationNumber`

### Integration Strategy

#### Option A: Modify Transpiler Output (Recommended)
1. Generate code that matches the manual implementation style
2. Include loop invariants in the generated code
3. Use the existing validity predicates

#### Option B: Add Verification Layer
1. Keep generated code as-is
2. Add proof wrappers that connect to the spec predicates
3. Use `assume` statements initially for unverified iterator methods

#### Option C: Extend Verus Libraries
1. Add verified iterator methods to vstd
2. Allow the simpler generated patterns to verify directly

### Loop Generation Requirements

To generate verifiable code, the transpiler would need to:

1. **Generate explicit for loops** instead of iterator chains
   ```rust
   // Instead of:
   votes.iter().filter(|(opn, _)| opn >= threshold).collect()

   // Generate:
   for key in iter:m_keys
   invariant
       // Loop invariants derived from postcondition
   {
       if *key >= threshold {
           result.insert(*key, votes[key]);
       }
   }
   ```

2. **Derive loop invariants from spec postconditions**
   - The spec predicate `RemoveVotesBeforeLogTruncationPoint` has 3 postconditions
   - Each needs to be translated to a loop invariant
   - Ghost variable tracking (`seen_keys`) may be needed

3. **Add ghost variables and proof blocks**
   - `ghost mut seen_keys = Set::empty()`
   - `proof { seen_keys = seen_keys.insert(*key) }`

4. **Add post-loop assertions**
   - Help SMT solver connect loop invariants to postconditions

**Complexity analysis:**
- Manual `CRemoveVotesBeforeLogTruncationPoint`: 80 LOC with invariants, ghost code, assumes
- Generated version: 1 line with iterator chain
- The gap requires significant invariant synthesis

### Next Steps

1. [x] Choose integration strategy - **Option B initially** (use `external_body` for iterator methods)
2. [x] Create a minimal test case with a single function using `external_body` [26:01:25, 03:30]
   - Added `generated_remove_votes_before_truncation` to generated_acceptor_test.rs
   - Uses `#[verifier::external_body]` to trust iterator implementation
   - Contracts (requires/ensures) are verified
3. [x] Verify that test case compiles with Verus - 456 verified, 0 errors
4. [ ] Explore Option A (loop generation) as a future enhancement

### Test Case Template

```rust
// File: src/tests/generated_acceptor_test.rs

use vstd::prelude::*;
use crate::implementation::RSL::acceptorimpl::*;
use crate::protocol::RSL::acceptor::*;

verus! {
    // Test that generated CRemoveVotesBeforeLogTruncationPoint matches spec
    #[test]
    fn test_generated_remove_votes() {
        // Create test data
        // Call generated function
        // Assert postconditions
    }
}
```
