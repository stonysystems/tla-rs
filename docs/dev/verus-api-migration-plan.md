# Verus API Migration Plan

## Overview

This document outlines the migration plan for updating the tla-rs codebase from the old Verus API (using `builtin::*` and `builtin_macros::*`) to the new Verus API (v0.2026.01.14) using `vstd::prelude::*`.

## Current State

- **Current Verus Version**: 0.2026.01.14.88f7396
- **Files Affected**: 107 source files
- **Main Changes Required**: Import statement updates

### Old Import Pattern
```rust
use builtin::*;
use builtin_macros::*;
use vstd::map::*;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::pervasive::*;
use vstd::seq::*;
```

### New Import Pattern
```rust
use vstd::prelude::*;
// Plus any additional specific imports not in prelude
```

## What `vstd::prelude::*` Includes

From analyzing `/home/shuai/tools/verus-x86-linux/vstd/prelude.rs`:

1. **Core Builtins**: Re-exports `verus_builtin::*` (replaces old `builtin::*`)
2. **Macros**: Re-exports key macros from `verus_builtin_macros` including:
   - `verus!`, `proof!`, `fndecl!`
   - `struct_with_invariants!`
   - `Structural`, `StructuralEq`
   - Various other utility macros
3. **Collections**:
   - `Map`, `map!`
   - `Seq`, `seq!`
   - `Set`, `set!`
4. **View Trait**: `super::view::*`
5. **Pervasive Functions**: `affirm`, `arbitrary`, `cloned`, `proof_from_false`, etc.
6. **Additional Spec Functions**:
   - `ArrayAdditionalExecFns`, `ArrayAdditionalSpecFns`
   - `SliceAdditionalSpecFns`
   - `VecAdditionalSpecFns`
   - Token types

## What's NOT in Prelude (May Need Explicit Import)

1. `vstd::modes::*` - Contains `tracked_swap`, `tracked_static_ref`
2. `vstd::multiset::*` - Multiset operations
3. `vstd::seq_lib::*` - Sequence library functions
4. `vstd::set_lib::*` - Set library functions
5. `vstd::map_lib::*` - Map library functions
6. `vstd::hash_map::*` - HashMap with View trait
7. `vstd::hash_set::*` - HashSet with View trait

## Migration Steps

### Step 1: Update Import Statements

For each file, apply these transformations:

```rust
// REMOVE these lines:
use builtin::*;
use builtin_macros::*;

// ENSURE this is present:
use vstd::prelude::*;

// KEEP or ADD specific imports as needed:
use vstd::modes::*;        // if using tracked_swap, tracked_static_ref
use vstd::multiset::*;     // if using Multiset
use vstd::seq_lib::*;      // if using sequence library lemmas
use vstd::set_lib::*;      // if using set library lemmas
use vstd::map_lib::*;      // if using map library lemmas
```

### Step 2: Verify Compilation

After updating imports, verify each file compiles:
```bash
/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs
```

### Step 3: Handle Any API Changes

Check for any renamed functions or changed signatures between Verus versions.

## Automation Strategy

Create a sed/awk script or Rust program to perform the migration:

```bash
# Remove old imports
sed -i 's/use builtin::\*;//g' FILE
sed -i 's/use builtin_macros::\*;//g' FILE

# Ensure vstd::prelude::* is present
# (More complex logic needed to avoid duplicates)
```

## Risk Assessment

1. **Low Risk**: Import statement changes are straightforward
2. **Medium Risk**: Some API functions may have changed signatures
3. **High Risk**: Proof obligations may need adjustment

## Estimated Effort

- **Files to modify**: 107
- **Time estimate**: ~2-4 hours for mechanical changes
- **Testing**: Additional time for verification

## Alternative: Use Older Verus

If migration proves problematic, an alternative is to use Verus v0.2024.09.05.29e4da0 which the codebase was originally tested with.

## Files to Modify

Total: 107 files in `src/` directory

Categories:
- `src/common/` - 19 files
- `src/implementation/` - 38 files
- `src/protocol/` - 36 files
- `src/services/` - 10 files
- `src/verus_extra/` - 2 files
- Root files: `src/lib.rs`, `src/main.rs`
