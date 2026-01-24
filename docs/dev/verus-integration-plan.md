# Verus Integration Plan for Generated Code

## Status [2026-01-25, 00:45]

### Findings

1. **Main codebase compiles**: The main tla-rs codebase compiles with Verus (warnings only, no errors)
   - Command: `/home/shuai/tools/verus-x86-linux/verus src/lib.rs --crate-type=lib`
   - Result: Deprecation warnings but no compilation errors

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

### Next Steps

1. [ ] Choose integration strategy
2. [ ] Create a minimal test case with a single function
3. [ ] Verify that test case compiles with Verus
4. [ ] Incrementally add more functions

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
