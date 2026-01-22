# Mode Annotation Format

This document describes the `.automan` annotation file format used by the Verus transpiler to specify how spec predicates should be transpiled into executable functions.

## File Format

Annotation files use the `.automan` extension and consist of module declarations containing function annotations.

### Basic Syntax

```
module ModulePath::Name {
    FunctionName(mode1, mode2, ...);
    AnotherFunction(+, -, +);
}
```

### Modes

- `+` - **Input mode**: The parameter is read-only and will be passed by reference
- `-` - **Output mode**: The parameter's value is computed by the function

### Comments

Lines starting with `#` or `//` are treated as comments:

```
# This is a comment
// This is also a comment
module RSL::Acceptor {
    # Initialize an acceptor state
    LAcceptorInit(-, +);  // (output state, input constants)
}
```

## Complete Example

```
# Mode annotations for the RSL Acceptor module
module RSL::Acceptor {
    # LAcceptorInit(s_, c) - Initialize acceptor state
    # s_ is the new state (output), c is constants (input)
    LAcceptorInit(-, +);

    # LAcceptorProcess1a(s, s_, inp, sent_packets)
    # s: current state (input)
    # s_: new state (output)
    # inp: incoming packet (input)
    # sent_packets: packets to send (output)
    LAcceptorProcess1a(+, -, +, -);

    # Similar pattern for Process2a
    LAcceptorProcess2a(+, -, +, -);
}

module RSL::Proposer {
    LProposerInit(-, +);
    LProposerMaybeEnterNewViewAndSend1a(+, -, +, -);
}
```

## Rules and Constraints

### Saturation
Every output parameter must be fully assigned by the predicate body. The transpiler checks that all fields of output structs are assigned exactly once.

### Harmony
No field of an output parameter may be assigned more than once. The transpiler detects double assignments.

### Obligation
Output parameters can only be used after they are assigned. The transpiler tracks assignment order.

## Generated Code

Given annotations like:
```
LAcceptorProcess1a(+, -, +, -);
```

The transpiler generates:
```rust
pub exec fn CAcceptorProcess1a(
    s: &CAcceptor,      // + becomes &T
    inp: &CRslPacket,   // + becomes &T
) -> (result: (CAcceptor, Vec<CRslPacket>))  // - params become tuple
    requires
        s.well_formed(),
        inp.well_formed(),
    ensures
        result.0.well_formed(),
        LAcceptorProcess1a(s@, result.0@, inp@, result.1@),
{
    // Generated body
}
```

## Command Line Usage

Check an annotation file for errors:
```bash
verus-transpile check --annotations src/protocol/RSL/acceptor.automan
```

Output:
```
OK: 1 module(s) parsed successfully
  - RSL::Acceptor (3 functions)
```
