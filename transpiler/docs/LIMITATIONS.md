# Limitations and Workarounds

This document describes known limitations of the transpiler and how to work around them.

## Type System Limitations

### 1. Generic Type Instantiation

**Limitation:** Complex generic type instantiation in expressions may not be inferred correctly.

**Workaround:** Add explicit type annotations in the spec function:
```rust
// Instead of:
let x = Map::empty();

// Use:
let x: Map<int, Value> = Map::empty();
```

### 2. Dependent Types

**Limitation:** Value-dependent typing (where types depend on runtime values) has limited support.

**Workaround:** Use separate spec functions for each variant or add type annotations.

### 3. Recursive Types

**Limitation:** Deeply recursive type structures may cause stack overflow during transpilation.

**Workaround:** Flatten recursive structures or limit recursion depth.

## Quantifier Limitations

### 1. Multiple Bound Variables

**Limitation:** Quantifiers with multiple bound variables cannot be automatically converted to loops.

```rust
// NOT SUPPORTED:
forall |i: int, j: int| 0 <= i < j < n ==> matrix[i][j] == ...
```

**Workaround:** Restructure using nested quantifiers:
```rust
// SUPPORTED:
forall |i: int| 0 <= i < n ==>
    forall |j: int| i < j < n ==> matrix[i][j] == ...
```

### 2. Existential Quantifiers

**Limitation:** `exists` quantifiers cannot be automatically converted to executable code.

**Workaround:** Implement as a search function manually or provide the witness explicitly.

### 3. Complex Triggers

**Limitation:** Complex trigger expressions may not translate efficiently.

**Workaround:** Use simpler triggers or restructure the quantifier.

## Collection Limitations

### 1. Infinite Collections

**Limitation:** Verus spec collections (Map, Set, Seq) are mathematically infinite, but exec code needs finite bounds.

**Workaround:** Always ensure bounds are specified:
```rust
// In spec:
forall |i: int| 0 <= i < len ==> ...
//             ^^^^^^^^^^^^^^^ explicit finite bound
```

### 2. Map/Set Comprehensions

**Limitation:** Complex map/set comprehensions with filtering may not match templates.

**Workaround:** Decompose into simpler operations:
```rust
// Instead of:
Set::new(|x| x in s1 && x in s2 && predicate(x))

// Use:
// 1. Filter s1 by s2 membership
// 2. Then filter by predicate
```

### 3. Nested Collections

**Limitation:** Deeply nested collections (Map<K, Vec<Map<...>>>) may cause issues.

**Workaround:** Use type aliases and break down operations.

## Control Flow Limitations

### 1. Match Expressions

**Limitation:** Complex match expressions with guards may not transpile correctly.

**Workaround:** Use simpler patterns or convert to if-else chains.

### 2. Loop Constructs

**Limitation:** While loops and for loops in spec functions are not supported.

**Workaround:** Use recursion with termination proofs.

## External Functions

### 1. FFI Calls

**Limitation:** External function calls must be marked and handled specially.

**Workaround:** Mark external functions with `#[verifier(external)]` and provide trusted implementations.

### 2. I/O Operations

**Limitation:** I/O operations cannot be automatically generated.

**Workaround:** Use the C#/Rust FFI layer for I/O and wrap with trusted specs.

## Proof Limitations

### 1. Complex Lemma Calls

**Limitation:** Lemma calls with complex arguments may not be inserted automatically.

**Workaround:** Add proof hints manually in a `proof { }` block.

### 2. Termination

**Limitation:** Recursive functions need termination proofs that may not be inferred.

**Workaround:** Add explicit `decreases` clauses.

## Known Issues

### 1. Type Name Collisions

If a type name like `CMessage` already exists, the transpiler may generate conflicts.

**Workaround:** Use the remapping configuration:
```toml
[remapping]
"LMessage" = "CMessage_Gen"
```

### 2. Import Resolution

The transpiler may not correctly resolve imports across modules.

**Workaround:** Use fully qualified paths or add explicit use statements.

### 3. Whitespace Sensitivity

Some edge cases in the parser may be whitespace-sensitive.

**Workaround:** Use consistent formatting (run through rustfmt).

## Reporting Issues

If you encounter a limitation not listed here:

1. Create a minimal reproducing example
2. Check if it matches any known template
3. File an issue with the spec code and expected output

## Future Improvements

The following limitations are planned for future versions:

- [ ] Multi-variable quantifier support
- [ ] Existential quantifier synthesis
- [ ] Better recursive predicate handling
- [ ] Automatic lemma insertion
