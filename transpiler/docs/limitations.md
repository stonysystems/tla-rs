# Limitations and Workarounds

This document describes the current limitations of the Verus transpiler and suggested workarounds.

## Quantifier Limitations

### Nested Quantifiers

**Not Supported:**
```rust
forall |i| forall |j| i < j ==> expr[i] < expr[j]
```

**Workaround:** Flatten to a single quantifier with tuple unpacking or restructure the spec.

### Multiple Bound Variables

**Not Supported:**
```rust
forall |i, j| predicate(i, j)
```

**Workaround:** Use separate quantifiers or introduce helper predicates.

### Complex Bodies

The transpiler matches quantifiers against known templates. Bodies that don't match patterns like:
- `forall |i| 0 <= i < n ==> seq[i] == expr`
- `forall |k| k in map ==> map[k] == expr`

will produce an "Unrecognized" template error.

**Workaround:** Restructure to match a known pattern, or implement the exec code manually.

## Expression Limitations

### Recursive Spec Functions

Recursive spec functions cannot be directly transpiled to exec code without termination analysis.

**Workaround:** Use iterative algorithms in the spec or implement exec code manually.

### Ghost Code in Exec

Ghost/proof code cannot be directly translated.

**Workaround:** The transpiler automatically strips ghost code; ensure exec-relevant logic is not in ghost blocks.

### Complex Arithmetic

Arbitrary arithmetic expressions may not translate cleanly due to potential overflow.

**Workaround:** Use bounded types and explicit overflow handling.

## Type Limitations

### Infinite Collections

Verus `Set` and `Map` are infinite by default.

**Workaround:** Ensure specs use finite bounds (e.g., `set.dom().finite()`).

### Dependent Types

Value-dependent typing is not fully supported.

**Workaround:** Use explicit type annotations and runtime checks.

### Generic Type Instantiation

Complex generic expressions may need manual type annotation.

**Workaround:** Add explicit type parameters where inference fails.

## Mode Analysis Limitations

### Partial Assignment Detection

The analyzer tracks field-level assignments but may miss complex nested structures.

**Workaround:** Ensure each output field is explicitly assigned in one place.

### Branch Coverage

All branches of conditionals must assign the same output fields.

**Not Supported:**
```rust
if cond {
    s_.field1 == value
    // field2 not assigned
} else {
    s_.field2 == value
    // field1 not assigned
}
```

**Workaround:** Ensure both branches assign all output fields.

### Use-Before-Assignment

Using an output variable before it's assigned is detected but complex data flow isn't analyzed.

**Workaround:** Order conjuncts so assignments come before uses.

## Integration Limitations

### Verus Macro Parsing

The parser handles `verus! { }` blocks but may not recognize all Verus-specific syntax.

**Workaround:** Report parsing issues; the parser is actively being improved.

### External Functions

Functions marked `#[verifier(external)]` cannot be transpiled.

**Workaround:** Implement exec versions manually and ensure they're linked correctly.

### FFI Boundaries

The transpiler does not handle FFI code generation (C#/Rust interop).

**Workaround:** Write FFI wrappers manually; use generated exec code within Rust.

## Performance Considerations

### Clone Overhead

Generated code may use `.clone()` more liberally than hand-written code.

**Workaround:** Profile critical paths and optimize manually if needed.

### Collection Operations

Template-based collection generation may not be optimal for large collections.

**Workaround:** Consider custom implementations for performance-critical paths.

## Debugging Tips

1. **Check Template Match**: If a quantifier isn't transpiling, check if it matches a known template
2. **Saturation Errors**: Ensure all output fields are assigned
3. **Mode Conflicts**: Verify input/output annotations match intended usage
4. **Type Mismatches**: Check that L-prefixed types have corresponding C-prefixed implementations

## Reporting Issues

When reporting issues, include:
1. The spec function that fails to transpile
2. The mode annotations
3. The error message
4. Expected vs actual behavior

File issues at: https://github.com/stonysystems/tla-rs/issues
