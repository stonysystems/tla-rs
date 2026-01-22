# Mode Annotation Format

The Verus transpiler uses `.automan` files to specify input/output mode annotations for spec function parameters.

## File Format

Annotation files use a simple text format with module declarations and function annotations.

### Basic Syntax

```
# Comments start with # or //

module Path::To::Module {
    FunctionName(mode1, mode2, ...);
}
```

### Mode Specifiers

| Symbol | Meaning | Description |
|--------|---------|-------------|
| `+` | Input | Parameter is read-only, passed by reference |
| `-` | Output | Parameter must be computed/assigned |

### Example

```
# RSL Acceptor mode annotations

module RSL::Acceptor {
    # (state_in, state_out)
    LAcceptorInit(-, +);

    # (state_in, state_out, packet_in, packets_out)
    LAcceptorProcess1a(+, -, +, -);
    LAcceptorProcess2a(+, -, +, -);
}

module RSL::Proposer {
    LProposerInit(-, +);
    LProposerProcess1b(+, -, +, -);
}
```

## Rules

1. **Parameter Count**: The number of modes must match the spec function's parameter count
2. **Output Coverage**: All output parameters must be fully assigned in the spec function body
3. **Input Safety**: Input parameters cannot be assigned to

## Spec Function Mapping

For a spec function:
```rust
spec fn LAcceptorProcess1a(
    s: LAcceptor,      // mode: +  (input)
    s_: LAcceptor,     // mode: -  (output)
    inp: RslPacket,    // mode: +  (input)
    sent: Seq<Packet>  // mode: -  (output)
) -> bool
```

The annotation declares which parameters are inputs (read) and outputs (computed):
```
LAcceptorProcess1a(+, -, +, -);
```

## Generated Code

The transpiler uses these annotations to:

1. **Generate function signature**:
   - Inputs become `&T` reference parameters
   - Outputs become the return tuple `(T1, T2, ...)`

2. **Generate requires clauses**:
   - `input.well_formed()` for each input

3. **Generate ensures clauses**:
   - `result.N.well_formed()` for each output
   - `LSpecFn(input@, result.0@, result.1@, ...)` linking to spec

## Best Practices

1. Place annotation files alongside spec files with `.automan` extension
2. Group related functions in the same module block
3. Add comments explaining non-obvious parameter roles
4. Keep annotations in sync with spec function signatures
