# RSL Patterns Analysis

## Overview

This document tracks patterns in RSL specifications and their transpiler support status.

## Transpilation Results (Updated 2026-01-24)

| File | Status | Notes |
|------|--------|-------|
| acceptor.rs | SUCCESS | All functions transpile |
| proposer.rs | SUCCESS | Exists quantifier now supported |
| learner.rs | SUCCESS | All functions transpile |
| executor.rs | SUCCESS | All functions transpile |
| replica.rs | SUCCESS | Collection check now supported |
| broadcast.rs | SUCCESS | All functions transpile |

**All 6 RSL spec files now transpile successfully!**

## Recently Resolved Patterns

### 1. Exists Quantifier ✅ RESOLVED (2026-01-24)

**Pattern:**
```rust
exists |p:RslPacket| S.contains(p) && pred(p)
```

**Solution implemented:**
- Pattern: `exists |x| container.contains(x) && pred(x)`
- Generated code: `container.iter().any(|x| pred(x))`
- Supports nested field access: `s.acceptor.last_checkpointed_operation.contains(opn)`

### 2. Forall Collection Check ✅ RESOLVED (2026-01-24)

**Pattern:**
```rust
forall |other_packet:RslPacket|
    s.proposer.received_1b_packets.contains(other_packet)
    ==> other_packet.src != received_packet.src
```

**Solution implemented:**
- Added `CollectionCheck` template to checker/mod.rs
- Pattern: `forall |x| container.contains(x) ==> pred(x)`
- Generated code: `container.iter().all(|x| pred(x))`

## Supported Templates

The following forall/exists patterns are supported:

| Template | Pattern | Generated Code |
|----------|---------|---------------|
| **ExistsContainer** | `exists \|x\| container.contains(x) && pred(x)` | `.iter().any(\|x\| pred(x))` |
| **CollectionCheck** | `forall \|x\| container.contains(x) ==> pred(x)` | `.iter().all(\|x\| pred(x))` |
| SeqComprehension | `forall \|i\| 0 <= i < len ==> seq[i] == expr` | `(0..len).map(\|i\| expr).collect()` |
| MapDomainBiconditional | `forall \|k\| output.contains_key(k) <==> pred` | `source.iter().filter(...).collect()` |
| MapPreservation | `forall \|k\| output[k] == source[k]` | `source.clone()` |
| MapConditionalValue | `forall \|k\| output[k] == if cond { v1 } else { v2 }` | `.map(...).collect()` |
| MapFilter | `forall \|k\| output.contains_key(k) <==> source.contains_key(k) && pred` | `.filter(...).collect()` |
| SetComprehension | `forall \|x\| x in set <==> pred` | `.filter(...).collect()` |
| MapExclusion | `forall \|k\| pred ==> !output.contains_key(k)` | (constraint only) |
| MapInclusion | `forall \|k\| pred ==> output.contains_key(k)` | (constraint only) |

## Remaining Code Quality Issues

Generated code has some quality issues that don't block transpilation:

### Multiple Return Values
Expressions are generated on separate lines instead of as tuples:
```rust
// Generated
s.clone()
Cempty()

// Should be
(s.clone(), Cempty())
```

### Helper Predicate Positioning
Calls to helper predicates appear before struct construction instead of being integrated:
```rust
// Generated
CProposerProcess1b(s.proposer, s_.proposer, received_packet)
CReplica { ... }

// Should use result of helper
```

### Missing Variable Bindings
Generated code sometimes references variables like `s_.votes` that need to be bound from helper predicate results.

## Recommendations

### High Priority (Code Quality)
1. Fix tuple return generation for multiple output values
2. Properly sequence helper predicate calls with result binding
3. Ensure all output variables are properly scoped

### Medium Priority (Optimization)
1. Reduce unnecessary `.clone()` calls
2. Optimize iterator chains
3. Use references where possible

## Change History

- **2026-01-24**: Added exists quantifier support (.any())
- **2026-01-24**: Added forall collection check template (.all())
- **2026-01-24**: All 6 RSL spec files now transpile
