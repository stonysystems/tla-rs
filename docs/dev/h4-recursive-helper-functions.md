# H4: Handle Recursive Helper Functions

## Status: BLOCKED - Requires design decision

## Goal
Support translation of recursive spec helper functions to exec implementations.

## Analysis

### Recursive Functions in election.rs
1. `RemoveAllSatisfiedRequestsInSequence(s: Seq<Request>, r: Request) -> Seq<Request>`
2. `RemoveExecutedRequestBatch(reqs: Seq<Request>, batch: RequestBatch) -> Seq<Request>`

### Existing Manual Implementation Pattern

From `ElectionImpl.rs`, the manual implementation uses:
- Recursive exec functions (not transformed to loops)
- `decreases` clauses for termination
- Proof blocks for verification assertions

```rust
pub fn CRemoveAllSatisfiedRequestsInSequence(s: &Vec<CRequest>, r: &CRequest) -> (rc: Vec<CRequest>)
    requires
        forall |i: int| 0 <= i < s@.len() ==> s@[i].valid(),
        r.valid(),
    ensures
        forall |i: int| 0 <= i < rc@.len() ==> rc@[i].valid(),
        rc@.map(|i, req:CRequest| req@) == RemoveAllSatisfiedRequestsInSequence(s@.map(|i, req: CRequest| req@), r@),
    decreases s.len(),
{
    if s.len() == 0 {
        let empty: Vec<CRequest> = Vec::new();
        proof { ... }
        return empty;
    }

    let head = s[0].clone_up_to_view();
    let tail = truncate_vec(s, 1, s.len());
    let tail_filtered = Self::CRemoveAllSatisfiedRequestsInSequence(&tail, r);

    if Self::CRequestSatisfiedBy(&head, r) {
        proof { ... }
        tail_filtered
    } else {
        let res = concat_vecs(&vec![head], &tail_filtered);
        proof { ... }
        res
    }
}
```

## Design Options

### Option 1: Generate Recursive Exec Functions (Simpler)
Pros:
- Direct translation from spec
- Preserves structure for proof verification

Cons:
- Requires proof blocks for correctness
- Proof blocks are complex to generate
- Helper functions like `truncate_vec`, `concat_vecs` needed

### Option 2: Transform to Iterative Loops (More Complex)
Pros:
- Better runtime performance
- Standard pattern for Verus verification

Cons:
- Complex transformation algorithm
- Loop invariants must be synthesized
- May not be possible for all recursive patterns

### Option 3: Skip Recursive Helpers (Temporary)
- Don't annotate recursive helpers in `.automan` files
- Use manual implementations from `ElectionImpl.rs`
- Focus on non-recursive helpers first

## Recommendation

**Option 3 (Skip)** for now, then **Option 1 (Recursive)** as next step.

Rationale:
- Option 1 is feasible but requires proof block generation
- The proof blocks in manual implementation are non-trivial
- Better to have working non-recursive helpers than broken recursive ones

## Implementation Steps for Option 1 (Future)

1. **Detect Recursive Functions**
   - Parse function body for self-calls
   - Mark function as recursive in AnnotatedFunction

2. **Generate Decreases Clause**
   - Analyze which parameter decreases (usually sequence length)
   - Generate `decreases param.len()` or similar

3. **Generate Recursive Body**
   - Transform base case (len == 0)
   - Transform recursive case with self-call
   - Handle Vec construction patterns

4. **Generate Proof Blocks** (Hardest Part)
   - Analyze manual implementations for patterns
   - Generate assertions for map/subrange equivalences
   - May need template-based generation

## Dependencies
- Need helper functions: `truncate_vec`, `concat_vecs`, `clone_vec_crequest`
- Need proper type mapping for CRequest with .map()

## Next Steps
For now, skip annotating recursive helpers and use manual implementations.
Future work should tackle Option 1 with proper proof block generation.
