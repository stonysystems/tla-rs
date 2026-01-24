# Loop Generation Analysis for Verus Verification

## Status [2026-01-25, 04:30]

This document analyzes the requirements for generating explicit loops with invariants
to replace iterator-based patterns in generated code.

## Problem Statement

The transpiler currently generates iterator patterns:
```rust
votes.iter().filter(|(opn, _)| opn >= threshold).collect()
```

These don't verify in Verus because:
1. Iterator methods are not verified in vstd
2. No loop invariants to establish postconditions
3. No ghost code to track iteration progress

Manual implementations use explicit loops:
```rust
for key in iter:m_keys
invariant
    seen_keys.subset_of(votes@.dom()),
    forall |opn| seen_keys.contains(opn) ==> votes@.contains_key(opn),
    // ... more invariants
{
    // loop body with proof blocks
}
```

## Complexity Analysis

Looking at `CRemoveVotesBeforeLogTruncationPoint`:

**Manual implementation**: 80 LOC
- 1 ghost variable declaration
- 5 loop invariants
- 6 in-loop assertions/assumes/proof blocks
- 10+ post-loop assertions

**Generated (iterator)**: 1 LOC

## Required Components for Loop Generation

### 1. Loop Structure Generation (~100 LOC)
- Parse spec function to identify map/seq iterations
- Generate `for key in iter:container.keys()` pattern
- Generate result variable initialization

### 2. Invariant Derivation (~200 LOC)
This is the hardest part. Need to:
- Analyze spec postconditions
- Derive loop invariants that:
  - Hold initially (empty result)
  - Are preserved by loop body
  - Imply postconditions when loop terminates

**Common patterns**:
- "seen_keys subset of source.dom()" - tracks iteration progress
- "result.dom() subset of seen_keys" - result only contains processed keys
- "filter condition preserved" - result contains only filtered elements

### 3. Ghost Variable Generation (~50 LOC)
- Track iteration progress (seen_keys)
- Maintain ghost state for proof

### 4. Post-Loop Assertions (~100 LOC)
- Connect loop termination to postconditions
- Help SMT solver with "seen_keys == source.dom()" reasoning

### 5. Assume Statements (~30 LOC)
- Some facts Verus cannot infer:
  - Iterator progress tracking
  - Set equality from subset + cardinality

## Task Breakdown

### Phase 1: Infrastructure (~150 LOC)
- [ ] Add ExecExpr variants for Verus loop constructs
  - ForInIter { var, iter_name, iter_source, invariants, body }
  - GhostVar { name, ty, init }
  - ProofBlock { stmts }
  - Assume { expr }
- [ ] Add printer support for new constructs

### Phase 2: Simple Loop Generation (~200 LOC)
- [ ] Identify map filter patterns in AST
- [ ] Generate basic loop structure without invariants
- [ ] Generate result initialization

### Phase 3: Invariant Templates (~300 LOC)
- [ ] Create invariant templates for common patterns:
  - MapFilter: filter elements from source map
  - SeqInit: initialize sequence to constant
  - MapUpdate: modify map with condition
- [ ] Match spec postconditions to invariant templates

### Phase 4: Ghost Code Generation (~100 LOC)
- [ ] Generate ghost variables for iteration tracking
- [ ] Generate proof blocks for ghost updates

### Phase 5: Post-Loop Assertions (~100 LOC)
- [ ] Generate post-loop assertions from postconditions
- [ ] Add assume statements for unprovable facts

## Estimated Total: ~850 LOC

This should be broken into 5-6 sub-tasks of ~150 LOC each.

## Alternative Approaches

### Option A: Full Invariant Synthesis (Complex)
Generate invariants automatically from postconditions.
- Pro: Fully automated
- Con: Requires invariant synthesis research

### Option B: Template-Based (Moderate)
Define templates for common patterns (filter, map, fold).
- Pro: Practical, covers most cases
- Con: Limited to predefined patterns

### Option C: Annotation-Based (Simple)
User provides loop invariants in annotation files.
- Pro: Simple to implement
- Con: Manual effort for users

## Recommendation

Start with **Option B (Template-Based)** for the map filter pattern,
as this is the most common case in RSL. Then expand to other patterns.

The first sub-task should be Phase 1: adding infrastructure for loop constructs.
