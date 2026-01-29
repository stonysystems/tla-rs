# G3: Standalone Output Plan

## Status: COMPLETE

## Goal
Make transpiler output self-contained by generating types inline alongside functions.

## Implementation Summary

### Config Changes
Added to `TranspilerConfig` in `lib.rs`:
```rust
pub struct TranspilerConfig {
    // ... existing fields ...

    /// Whether to generate type definitions inline from the spec file.
    pub generate_inline_types: bool,

    /// Type remapping table for custom type name mappings
    pub type_remapping: HashMap<String, String>,
}
```

Also added to `OutputConfig` in `config.rs`:
```toml
[output]
generate_inline_types = true
```

### Implementation
Modified `Transpiler::transpile_file` and `Transpiler::transpile_source`:

1. When `generate_inline_types` is true:
   - Parse types from spec file using `TypeParser`
   - Build a `TypeRegistry` from parsed types
   - Generate type code using `TypeGenerator` for each struct/enum
   - Insert type code BEFORE function code (inside verus! block)

2. Support for type remapping via `type_remapping` field

### Code Flow
```
transpile_file(spec_path, annotation_path)
  |
  +-> parse_file(spec_path)          // Get spec functions
  +-> parse_annotation_file(...)     // Get annotations
  |
  +-> IF generate_inline_types:
  |     +-> TypeParser::parse_types(spec_content)
  |     +-> build_registry(types)
  |     +-> TypeGenerator::generate_struct for each struct
  |     +-> TypeGenerator::generate_enum for each enum
  |     +-> Insert generated type code
  |
  +-> For each function:
        +-> translate() and print()
  |
  +-> Return combined output
```

## LOC Summary
- Config changes: ~15 LOC
- transpile_file modification: ~50 LOC (both file and source methods)
- Tests: ~80 LOC
- Total: ~145 LOC

## Tests Added
1. `test_inline_type_generation` - Verifies types are generated when enabled
2. `test_inline_type_generation_disabled_by_default` - Verifies backward compatibility

## Completion Date
2026-01-29
