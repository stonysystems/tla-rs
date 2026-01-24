# Map Filter Code Generation Plan

## Overview

This document outlines the plan to improve the transpiler's code generation for map filter patterns, replacing placeholder comments with actual executable loop code.

## Current State

The transpiler recognizes 8 map-related quantifier patterns but only generates real code for 1 (MapFilter). The rest emit placeholder comments.

| Pattern | Status | Priority |
|---------|--------|----------|
| MapFilter | Working | - |
| MapPreservation | Partial (clone) | High |
| MapDomainBiconditional | Placeholder | High |
| MapConditionalValue | Placeholder | High |
| MapComprehension | Placeholder | Medium |
| MapExclusion | Placeholder | Low |
| MapInclusion | Placeholder | Low |

## Implementation Plan

### Task 1: MapPreservation Enhancement
**Input pattern:**
```rust
forall |k| output.contains_key(k) ==> source.contains_key(k) && output[k] == source[k]
```
**Current output:** `source.clone()`
**Target output:** `source.clone()` (already correct for full preservation)

Note: This pattern already works for full preservation. Enhancement only needed if combined with domain filtering.

### Task 2: MapDomainBiconditional Code Generation
**Input pattern:**
```rust
forall |k| output.contains_key(k) <==> pred(k) && source.contains_key(k)
```
**Target output:**
```rust
source.iter().filter(|(k, _)| pred(k)).cloned().collect::<HashMap<_, _>>()
```

### Task 3: MapConditionalValue Code Generation
**Input pattern:**
```rust
forall |k| output.contains_key(k) ==> output[k] == if cond { v1 } else { v2 }
```
**Target output:**
```rust
source.iter()
    .map(|(k, v)| (k.clone(), if cond { v1.clone() } else { v.clone() }))
    .collect::<HashMap<_, _>>()
```

### Task 4: Combined Domain + Value Patterns
When MapDomainBiconditional and MapConditionalValue appear together (common in RSL), generate combined code:
```rust
source.iter()
    .filter(|(k, _)| domain_pred(k))
    .map(|(k, v)| (k.clone(), if cond { new_v } else { v.clone() }))
    .collect::<HashMap<_, _>>()
```

### Task 5: MapComprehension Code Generation
**Input pattern:**
```rust
forall |k| k in result <==> domain_pred(k) && result[k] == value(k)
```
**Target output:**
```rust
domain.iter()
    .filter(|k| domain_pred(k))
    .map(|k| (k.clone(), value(k)))
    .collect::<HashMap<_, _>>()
```

## Implementation Location

File: `transpiler/src/translator/mod.rs`
Function: `translate_quantifier_template()`
Lines: ~1100-1262

## Testing Strategy

1. Add unit tests for each pattern in `translator/mod.rs` tests section
2. Create Verus verification examples in `verus_examples/`
3. Verify with Verus that generated code satisfies spec predicates

## Key Files

- `transpiler/src/translator/mod.rs` - Code generation
- `transpiler/src/checker/mod.rs` - Pattern recognition
- `transpiler/verus_examples/` - Test examples

## Estimated Changes

~150-200 lines of new code generation logic, replacing placeholder comment generation with proper iterator-based code.
