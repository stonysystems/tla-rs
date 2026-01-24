# Helper Predicate Output Binding Plan

## Problem

When a spec has helper predicate calls with output parameters, the generated code references those outputs without binding them.

**Spec pattern:**
```rust
&&& LProposerProcessRequest(s.proposer, s_.proposer, received_packet)
&&& s_ == LReplica {
    proposer: s_.proposer,  // <-- references s_.proposer
    ...
}
```

**Current generated code (broken):**
```rust
CProposerProcessRequest(s.proposer, s_.proposer, received_packet)  // <-- s_.proposer undefined
CReplica {
    proposer: s_.proposer,  // <-- s_.proposer still undefined
    ...
}
```

**Expected generated code:**
```rust
let s_proposer = CProposerProcessRequest(&s.proposer, &received_packet);
CReplica {
    proposer: s_proposer,
    ...
}
```

## Analysis

The transformation requires:
1. Identify helper predicate calls in the Conjunction
2. Determine which parameters are outputs (from `.automan` annotations)
3. Generate let bindings with unique variable names
4. Substitute output parameter references in subsequent expressions

## Key Components Needed

### 1. Helper Call Detection

Detect patterns like:
```rust
Expr::Call { func: "LProposerProcessRequest", args: [s.proposer, s_.proposer, packet] }
```

### 2. Output Parameter Identification

From `.automan` files:
```
LProposerProcessRequest(+, -, +);  // s is input, s_ is output, packet is input
```

### 3. Variable Binding Generation

For each helper call with outputs:
```rust
let s_proposer = CProposerProcessRequest(&s.proposer, &received_packet);
```

### 4. Reference Substitution

Replace `s_.proposer` with `s_proposer` in the struct construction.

## Implementation Approach

### Option A: Pre-processing pass (Recommended)

Before transforming the Conjunction:
1. Scan for helper predicate calls
2. Build a map: `s_.field` -> generated variable name
3. Generate let bindings
4. Apply substitution to remaining expressions

### Option B: Context threading

Pass output bindings through the TransformContext and substitute during transformation.

## Estimated Effort

- Detection logic: ~100 LOC
- Binding generation: ~100 LOC
- Substitution logic: ~150 LOC
- Tests: ~100 LOC

Total: ~450 LOC

## Dependencies

- Need access to `.automan` annotation info during transformation
- Currently annotation info is used for mode detection but not parameter position mapping
