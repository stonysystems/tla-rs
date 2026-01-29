# H2: Extend Annotation Format for Helper Functions

## Status: COMPLETE [26:01:29]

## Goal
Extend the annotation format to support helper function annotations alongside predicates.

## Current Format
```
module RSL::Election {
    ElectionStateInit(-, +);           // predicate: first param is output
    ElectionStateProcessHeartbeat(+, -, +, +);  // predicate
}
```

## Proposed Extension

### Option A: Explicit `helper` keyword (CHOSEN)
```
module RSL::Election {
    // Predicates (existing syntax)
    ElectionStateInit(-, +);
    ElectionStateProcessHeartbeat(+, -, +, +);

    // Helper functions (new syntax)
    helper ComputeSuccessorView(+, +) -> Ballot;
    helper BoundRequestSequence(+, +) -> Seq<Request>;
    helper RequestsMatch(+, +) -> bool;
}
```

### Option B: Infer from return type
Not chosen because:
- Predicates also return bool, making inference ambiguous
- Less explicit, harder to understand at a glance

## Implementation Plan

### 1. Add FunctionKind enum to AST (~10 LOC)
```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum FunctionKind {
    #[default]
    Predicate,
    Helper,
}
```

### 2. Update FunctionAnnotation (~15 LOC)
```rust
pub struct FunctionAnnotation {
    pub name: String,
    pub kind: FunctionKind,
    pub param_modes: Vec<ParameterMode>,
    pub return_type: Option<String>,  // For helpers, e.g., "Ballot"
}
```

### 3. Update Parser (~50 LOC)
- Detect `helper` prefix
- Parse optional `-> Type` return type
- Create appropriate FunctionAnnotation

### 4. Add Tests (~40 LOC)
- Test parsing helper function syntax
- Test parsing mixed predicates and helpers
- Test error handling for malformed helper annotations

## Files to Modify
1. `transpiler/src/ast/mod.rs` - Add FunctionKind enum
2. `transpiler/src/annotation/mod.rs` - Update parser and FunctionAnnotation

## Estimated LOC: ~115
