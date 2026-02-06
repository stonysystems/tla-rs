# Phase 2.1: Round-trip Consistency Design

## Overview

This document outlines the design for implementing round-trip consistency testing between TLA+ and Verus specifications.

## Goals

1. **Verus → TLA+ → Verus** round-trip: Converting Verus spec code to TLA+, then back to Verus should produce semantically equivalent code.
2. **TLA+ → Verus → TLA+** round-trip: Converting TLA+ to Verus, then back to TLA+ should produce semantically equivalent code.

## Challenges

### Semantic vs Syntactic Equivalence

Round-trip conversion won't produce identical text due to:
- Different naming conventions (LReplica ↔ Replica)
- Different expression syntax (forall |x: T| P(x) ↔ \A x \in T : P(x))
- Whitespace and formatting differences
- Comment stripping
- Type annotations presence/absence

**Solution**: Define canonical forms and compare at the AST level or semantic level, not text level.

### Information Loss

Some constructs don't have direct mappings:
- **Verus → TLA+**: `decreases` clauses, triggers, proof code are stripped
- **TLA+ → Verus**: Temporal operators ([], <>, ~>) have no direct Verus equivalent
- **Both directions**: Some type information may be lost or inferred differently

**Solution**: Define "round-trip preservable" subsets of each language.

## Approach

### Phase 2.1.1: Define Canonical AST Representations (~100 LOC)

Create canonical forms for comparison:
1. Normalize identifiers (strip L/C prefixes)
2. Normalize operator names
3. Sort record fields alphabetically
4. Normalize binary operators (e.g., a != b → ~(a = b))

### Phase 2.1.2: AST Comparison Infrastructure (~150 LOC)

Implement AST comparison that:
1. Compares TlaExpr trees structurally
2. Allows for known equivalent forms
3. Reports meaningful differences

### Phase 2.1.3: Verus → TLA+ → Verus Round-trip Tests (~150 LOC)

Test workflow:
1. Parse Verus spec function
2. Convert to TLA+ AST using verus2tla
3. Convert TLA+ AST back to Verus using tla translator
4. Compare original and result ASTs

### Phase 2.1.4: TLA+ → Verus → TLA+ Round-trip Tests (~150 LOC)

Test workflow:
1. Parse TLA+ module
2. Convert to Verus code using translator
3. Parse generated Verus code
4. Convert back to TLA+ using verus2tla
5. Compare original and result TLA+ ASTs

### Phase 2.1.5: Round-trip Test Suite for RSL Protocol (~100 LOC)

Apply round-trip tests to:
- Simple operators (Type definitions, helper functions)
- State predicates (Init, TypeOK)
- Complex expressions (quantifiers, set operations)

## File Structure

```
transpiler/
├── src/
│   └── roundtrip/
│       ├── mod.rs           # Module exports
│       ├── canonical.rs     # Canonical form conversion
│       └── compare.rs       # AST comparison utilities
└── tests/
    └── roundtrip.rs         # Round-trip test suite
```

## Success Criteria

1. All "round-trip preservable" expressions maintain equivalence
2. Clear error messages when round-trip fails
3. Test coverage for RSL protocol components

## Estimated LOC

| Task | LOC |
|------|-----|
| 2.1.1 Canonical forms | ~100 |
| 2.1.2 AST comparison | ~150 |
| 2.1.3 V→T→V tests | ~150 |
| 2.1.4 T→V→T tests | ~150 |
| 2.1.5 RSL test suite | ~100 |
| **Total** | **~650** |

## Priority

This is a "Low" priority feature that validates the bidirectional transpiler but doesn't block primary functionality.
