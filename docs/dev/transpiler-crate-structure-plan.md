# Transpiler Crate Structure Plan

## Goal
Create the initial crate structure for the Verus spec-to-implementation transpiler as described in TODO.md Section 2.1.

## Crate Structure

```
transpiler/
├── Cargo.toml
├── src/
│   ├── lib.rs              # Library entry point, re-exports modules
│   ├── main.rs             # CLI entry point (stubbed)
│   ├── parser/
│   │   └── mod.rs          # Verus parsing (stubbed)
│   ├── ast/
│   │   └── mod.rs          # AST definitions (stubbed)
│   ├── annotation/
│   │   └── mod.rs          # Mode annotation handling (stubbed)
│   ├── moder/
│   │   └── mod.rs          # Mode analysis (stubbed)
│   ├── checker/
│   │   └── mod.rs          # Validation passes (stubbed)
│   ├── translator/
│   │   └── mod.rs          # Code generation (stubbed)
│   ├── printer/
│   │   └── mod.rs          # Output formatting (stubbed)
│   └── error.rs            # Error types (stubbed)
└── tests/
    └── integration.rs      # Integration tests (placeholder)
```

## Dependencies

Per TODO.md Section 2.1:
- `syn` + `quote` + `proc-macro2` for Rust parsing
- `serde` + `serde_json` for configuration
- `clap` for CLI
- `miette` for error reporting (chosen over ariadne for better ecosystem integration)

## Implementation Notes

- Each module will be stubbed with placeholder types and functions
- The lib.rs will re-export all public types for easier access
- Error types will use miette for span-aware, accumulating error handling
- CLI will be basic but functional (parse args, show help)

## Task Breakdown

1. Create directory structure
2. Create Cargo.toml with dependencies
3. Create lib.rs with module declarations
4. Create main.rs with basic CLI skeleton
5. Create each module stub (parser, ast, annotation, moder, checker, translator, printer)
6. Create error.rs with basic error types
7. Create placeholder test file
8. Verify crate builds successfully
