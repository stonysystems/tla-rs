# Tuple Return Generation Fix Plan

## Problem

Generated code produces separate statements instead of tuple returns:

**Current output:**
```rust
s.clone()
Cempty()
```

**Expected output:**
```rust
(s.clone(), Cempty())
```

## Root Cause

In `translator/mod.rs:507-516`, Conjunction expressions are transformed to Block statements:
```rust
Expr::Conjunction(exprs) => {
    if let Some(struct_expr) = self.try_extract_struct_construction(exprs, ctx)? {
        return Ok(struct_expr);
    }
    // Otherwise transform as a block
    let stmts: TranspileResult<Vec<_>> =
        exprs.iter().map(|e| self.transform_expr(e, ctx)).collect();
    Ok(ExecExpr::Block(stmts?))
}
```

This doesn't handle the case where multiple outputs need to be returned as a tuple.

## Analysis of RSL Patterns

### Pattern 1: Simple two-output return
Spec:
```rust
&&& s_ == s
&&& sent_packets == Seq::empty()
```

Should generate:
```rust
(s.clone(), Vec::new())
```

### Pattern 2: Struct + packets return
Spec:
```rust
&&& LAcceptorProcess1a(s.acceptor, s_.acceptor, received_packet, sent_packets)
&&& s_ == LReplica { acceptor: s_.acceptor, ... }
```

Should generate:
```rust
{
    let (s_acceptor, sent_packets) = CAcceptorProcess1a(s.acceptor, received_packet);
    (CReplica { acceptor: s_acceptor, ... }, sent_packets)
}
```

### Pattern 3: Multiple helper calls
Spec:
```rust
&&& LProposerProcess1b(s.proposer, s_.proposer, received_packet)
&&& LAcceptorTruncateLog(s.acceptor, s_.acceptor, opn)
&&& s_ == LReplica { ... }
&&& sent_packets == Seq::empty()
```

Should generate:
```rust
{
    let s_proposer = CProposerProcess1b(s.proposer, received_packet);
    let s_acceptor = CAcceptorTruncateLog(s.acceptor, opn);
    (CReplica { proposer: s_proposer, acceptor: s_acceptor, ... }, Vec::new())
}
```

## Solution Approach

### Step 1: Identify output expressions in Conjunction

Add a function to categorize expressions in a Conjunction:
- **Struct assignments**: `s_ == LReplica { ... }` → output state
- **Sequence assignments**: `sent_packets == Seq::empty()` → output packets
- **Helper predicate calls**: `LHelper(in, out, ...)` → side effects

### Step 2: Collect outputs into tuple

After processing Conjunction:
1. If there are multiple output variables, wrap them in `ExecExpr::Tuple`
2. If there's struct construction + packet expression, combine them

### Step 3: Handle helper predicate calls

For each helper call:
1. Generate let binding with tuple destructuring if it has outputs
2. Thread the outputs to the final return tuple

## Implementation Tasks

1. Add `categorize_conjunction_exprs()` function
2. Modify `transform_conjunction()` to collect outputs
3. Add `wrap_outputs_as_tuple()` helper
4. Add unit tests for tuple return patterns

## Estimated LOC: ~150 lines
