# Code Generation Bug Fixes Plan

## Overview

This document describes the fixes for transpiler code generation bugs identified during Verus integration testing.

## Bugs Identified

### Bug 1: Wrong Struct Name

**Location**: `translator/mod.rs:try_extract_struct_construction()` line 835

**Problem**: When no base input exists, the struct name is derived from the output variable name (`s_` → `s` → `Cs`), instead of from the type information.

**Example**:
- Input: `NodeInit(s, start_with_lock)` with `s` being output of type `LNode`
- Current output: `Cs { held: ..., epoch: ... }`
- Expected: `CNode { held: ..., epoch: ... }`

**Fix**:
- Pass type information through the TransformContext
- Look up the output parameter's type to derive the correct struct name
- Add `output_types: HashMap<String, Type>` to `TransformContext`

### Bug 2: Incomplete If-Branch Expressions

**Location**: `translator/mod.rs:transform_expr()` for Conjunction handling

**Problem**: When a conjunction is inside an if-branch and represents field assignments for a struct, the individual expressions are not properly aggregated.

**Example**:
```rust
// Input spec (if branch):
&&& !s_.held
&&& s_.epoch == s.epoch + 1

// Current output:
!s_.held           // Orphaned expression
(s.epoch + 1)      // Orphaned expression

// Expected output:
CNode { held: false, epoch: s.epoch + 1 }
```

**Fix**:
- Enhance `try_extract_struct_construction` to handle field assignments where the value is a direct expression (not an equality)
- Pattern: `s_.field == expr` should be detected, but also expressions like `!s_.held` need to be recognized as setting `held = false`

### Bug 3: StructUpdate Missing Type Name

**Location**: `printer/mod.rs:print_expr()` for `ExecExpr::StructUpdate`

**Problem**: Struct update syntax requires the type name: `TypeName { fields, ..base }`, but we're outputting `{ fields, ..base }`.

**Example**:
- Current: `{ epoch: transfer_epoch, ..s.clone() }`
- Expected: `CNode { epoch: transfer_epoch, ..s.clone() }`

**Fix**:
- Add struct name to `ExecExpr::StructUpdate`
- Modify `StructUpdate` to include `name: String`
- Update translator to populate the struct name from type information

## Implementation Steps

1. Add type tracking to TransformContext
2. Fix struct name derivation in try_extract_struct_construction
3. Add struct name to StructUpdate enum variant
4. Update printer to output struct name
5. Handle negation patterns like `!s_.held` as field assignments

## Testing

After fixes, regenerate `simple_impl.rs` and verify:
1. All struct names are `CNode` not `Cs`
2. If-branches produce complete struct expressions
3. StructUpdate syntax is valid Rust
