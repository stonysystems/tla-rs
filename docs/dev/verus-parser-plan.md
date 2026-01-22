# Verus Parser Implementation Plan

## Goal
Implement a parser that extracts `spec fn` declarations from Verus source files and converts them to our internal AST representation.

## Scope
- Parse `verus! { ... }` macro blocks (or raw Verus syntax)
- Extract `spec fn` declarations with their signatures and bodies
- Handle Verus-specific syntax extensions
- Convert to our `SpecFunction` AST type

## Approach

### Strategy: syn-based parsing with custom extensions

We'll use `syn` for standard Rust parsing, then handle Verus extensions through custom parsing logic.

### Key Verus Syntax to Handle

1. **Function modifiers**: `spec`, `exec`, `proof`, `tracked`, `ghost`
2. **Verus operators**:
   - `&&&` (conjunction chain)
   - `|||` (disjunction chain)
   - `==>` (implication)
   - `<==` (reverse implication)
   - `<==>` (biimplication)
3. **Spec expressions**:
   - `@` suffix (view operator)
   - `->` (enum variant field access)
   - `seq![]`, `set![]`, `map![]` macros
   - `forall|x|`, `exists|x|` quantifiers
4. **Spec clauses**: `requires`, `ensures`, `recommends`, `decreases`

### Implementation Steps

1. **Phase 1: Basic spec fn parsing** (~200 LOC)
   - Parse function signature (name, params, return type)
   - Parse function body as raw token stream initially
   - Handle basic type parsing

2. **Phase 2: Expression parsing** (~300 LOC)
   - Parse Verus operators (&&&, |||, ==>)
   - Parse field access, method calls
   - Parse if/match expressions
   - Parse quantifiers (forall/exists)

3. **Phase 3: Verus-specific constructs** (~100 LOC)
   - Parse view operator (@)
   - Parse arrow operator (->)
   - Parse seq!/set!/map! macros

## Implementation Details

### File: `parser/mod.rs`

```rust
// Structure:
// 1. VerusParser - main parser struct
// 2. parse_verus_block() - find and parse verus! macro invocations
// 3. parse_spec_fn() - parse a single spec fn
// 4. parse_verus_expr() - parse Verus expressions
// 5. parse_verus_type() - parse Verus types
```

### Test Cases

1. Simple spec fn with bool return
2. Spec fn with if-else
3. Spec fn with quantifiers
4. Spec fn with collection operations
5. Spec fn with struct updates

## Estimated LOC
~500 lines for a basic working parser

## Dependencies
- `syn` with "full" feature for Rust parsing
- `proc_macro2` for token handling
- `quote` for macro handling

## Notes
- The parser doesn't need to be perfect initially
- Focus on patterns used in the tla-rs codebase (RSL protocol)
- Can add more expression types as needed
