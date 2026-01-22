# Automan Annotation Format

## Overview

The `.automan` annotation files specify input/output modes for spec function parameters.
This allows the transpiler to determine which parameters are inputs (read-only) and which
are outputs (computed values).

## File Format

```
// Comments start with //

module RSL::Acceptor {
    // Function annotations
    LAcceptorInit(-, +);           // s_ is output, c is input
    LAcceptorProcess1a(+, -, +, -); // s is input, s_ is output, etc.
    LAcceptorProcess2a(+, -, +, -);
}

module RSL::Proposer {
    LProposerInit(-, +);
    LProposerProcess1b(+, -, +, +, -);
}
```

## Grammar (informal)

```
file         := module_decl*
module_decl  := "module" module_path "{" func_decl* "}"
module_path  := identifier ("::" identifier)*
func_decl    := identifier "(" mode_list ")" ";"
mode_list    := mode ("," mode)*
mode         := "+" | "-"
identifier   := [a-zA-Z_][a-zA-Z0-9_]*
comment      := "//" anything-to-EOL
```

## Mode Semantics

- `+` (plus) = Input parameter - read-only, value comes from caller
- `-` (minus) = Output parameter - must be computed/assigned by the function

## Parser Implementation

The parser processes the file line by line:
1. Skip empty lines and comments
2. Track current module context
3. Parse function declarations within module blocks
4. Build `ModuleAnnotations` with function map

## Example Parsed Structure

```rust
ModuleAnnotations {
    module_path: "RSL::Acceptor",
    functions: {
        "LAcceptorInit" => FunctionAnnotation {
            name: "LAcceptorInit",
            param_modes: [Output, Input],
        },
        "LAcceptorProcess1a" => FunctionAnnotation {
            name: "LAcceptorProcess1a",
            param_modes: [Input, Output, Input, Output],
        },
    }
}
```
