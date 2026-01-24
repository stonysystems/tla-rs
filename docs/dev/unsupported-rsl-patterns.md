# Unsupported RSL Patterns Analysis

## Overview

This document identifies patterns in RSL specifications that the transpiler cannot currently handle, along with recommendations for addressing them.

## Transpilation Results

| File | Status | Blocking Issue |
|------|--------|----------------|
| acceptor.rs | Success (with TODOs) | None |
| proposer.rs | **FAILED** | Exists quantifier |
| learner.rs | Success (with TODOs) | None |
| executor.rs | Success (with TODOs) | None |
| replica.rs | **FAILED** | Forall pattern unsupported |
| broadcast.rs | Success (with TODOs) | None |

## Critical Unsupported Patterns

### 1. Exists Quantifier (HIGH PRIORITY)

**Status:** Completely unsupported - all `exists` patterns are rejected

**Pattern:**
```rust
exists |p:RslPacket| S.contains(p) && pred(p)
```

**Location:** `proposer.rs` (3+ occurrences)

**Example from LExistsAcceptorHasProposalLargeThanOpn:**
```rust
exists |p:RslPacket| S.contains(p) && LExistVotesHasProposalLargeThanOpn(p, op)
```

**Why it fails:** The transpiler explicitly rejects all exists quantifiers in `translator/mod.rs:800-807` because finding a witness is non-deterministic.

**Potential solutions:**
1. Add `choose!` macro transformation for simple exists patterns
2. Generate iterator-based search: `set.iter().find(|p| pred(p)).is_some()`
3. For specifications that return bool, transform to: `set.iter().any(|p| pred(p))`

### 2. Forall with Collection Membership and Field Comparison (MEDIUM PRIORITY)

**Status:** Template matching fails - pattern not recognized

**Pattern:**
```rust
forall |var:Type| container.contains(var) ==> var.field != other_value
```

**Location:** `replica.rs:117`

**Example from LReplicaNextProcess1b:**
```rust
forall |other_packet:RslPacket|
    s.proposer.received_1b_packets.contains(other_packet)
    ==> other_packet.src != received_packet.src
```

**Why it fails:** The forall template matcher expects patterns like:
- `seq[i] == expr` (sequence construction)
- `k in map <==> pred` (map domain)
- `map[k] == expr` (map value)

But this pattern has:
- Collection membership in premise
- Field comparison (not assignment) in conclusion

**Potential solutions:**
1. Add template: `ForallCollectionCheck` that generates:
   ```rust
   container.iter().all(|var| var.field != other_value)
   ```
2. Recognize negation pattern and generate appropriate code

## Currently Supported Templates

The following forall patterns ARE supported (in `checker/mod.rs`):

| Template | Pattern | Generated Code |
|----------|---------|---------------|
| SeqComprehension | `forall \|i\| 0 <= i < len ==> seq[i] == expr` | `(0..len).map(\|i\| expr).collect()` |
| MapDomainBiconditional | `forall \|k\| output.contains_key(k) <==> pred` | `source.iter().filter(...).collect()` |
| MapPreservation | `forall \|k\| output[k] == source[k]` | `source.clone()` |
| MapConditionalValue | `forall \|k\| output[k] == if cond { v1 } else { v2 }` | `.map(...).collect()` |
| MapFilter | `forall \|k\| output.contains_key(k) <==> source.contains_key(k) && pred` | `.filter(...).collect()` |
| SetComprehension | `forall \|x\| x in set <==> pred` | `.filter(...).collect()` |

## Generated Code Quality Issues

Even successful transpilations produce code with issues:

### TODO Comments
```rust
// TODO: Map domain constraint - opn in output <==> ...
// TODO: Value mapping - output[k] = ...
```

These indicate incomplete semantic translation where:
- Domain constraints are recognized but not fully generated
- Value mappings are detected but not implemented

### Missing Variable Bindings
Generated code sometimes references variables like `s_.votes` that are never defined in scope.

## Recommendations

### High Priority (Blocking)
1. **Add exists quantifier support** - At minimum, transform simple exists to `.any()`
2. **Add forall collection check template** - Handle `container.contains(x) ==> pred(x)`

### Medium Priority (Code Quality)
1. Fix TODO comments to generate actual code
2. Ensure all output variables are properly bound

### Low Priority (Optimization)
1. Reduce unnecessary `.clone()` calls
2. Optimize iterator chains

## Implementation Notes

### For Exists Support
The safest approach is to transform exists to iterator methods:
```rust
// Spec
exists |p| set.contains(p) && pred(p)

// Exec
set.iter().any(|p| pred(p))
```

### For Forall Collection Check
```rust
// Spec
forall |x| container.contains(x) ==> x.field != value

// Exec
container.iter().all(|x| x.field != value)
```

## Files Modified for This Analysis

- Created: `docs/dev/unsupported-rsl-patterns.md` (this file)
- Analysis date: 2026-01-24
