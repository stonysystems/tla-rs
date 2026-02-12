# Transpiler Configuration Reference

This document describes all TOML configuration options for the Verus spec-to-implementation transpiler.

## Basic Configuration

### `[naming]`

Controls name prefixes and type mappings for spec-to-exec translation.

```toml
[naming]
spec_prefix = "L"           # Prefix for spec types (e.g., LState)
exec_prefix = "C"           # Prefix for exec types (e.g., CState)
int_type = "u64"            # Verus int → Rust concrete type
nat_type = "u64"            # Verus nat → Rust concrete type
```

### `[remapping]`

Maps spec type names to exec type names when the default prefix-swap is insufficient.

```toml
[remapping]
"RslPacket" = "CPacket"     # Spec type → Exec type
"Ballot" = "CBallot"
```

### `[method_calls]`

Maps spec function calls to exec method calls on concrete types.

```toml
[method_calls]
"BalLt" = { receiver = "CBallot", method = "CBalLt" }
```

### `vec_element_ensures`

Per-element ensures predicates for functions returning `Vec<T>` (mapped from `Seq<T>`).
When configured, the transpiler generates `forall` ensures for each element of Vec output parameters.

```toml
vec_element_ensures = ["valid", "abstractable"]
```

Generates for each Vec/Seq output parameter:
```verus
forall |i:int| 0 <= i < result.X@.len() ==> result.X@[i].valid(),
forall |i:int| 0 <= i < result.X@.len() ==> result.X@[i].abstractable(),
```

For single-output functions, uses `result@` instead of `result.X@`.

## Output Configuration

### `[output]`

Controls what the transpiler generates and how.

```toml
[output]
generate_proofs = true                  # Generate proof blocks for ensures
generate_loops_for_verification = true  # Generate while-loops instead of iterators
generate_inline_types = false           # Parse and inline types from spec file
clone_method = "clone_up_to_view"       # Clone method for struct cloning (default: "clone")
validity_predicate_name = "valid"       # Name of the validity predicate
manual_code = "learner_manual.rs"       # File to inject into verus! {} block
```

#### `generate_proofs`

When `true`, the transpiler generates proof blocks after exec code to satisfy `ensures` clauses. Proof blocks include:
- Spec predicate assertions
- Validity assertions
- Collection operation lemma calls
- `broadcast use` statements

#### `generate_loops_for_verification`

When `true`:
- `seq![x]` → manual HashSet/HashMap construction with `insert`
- `set![x]` → `{ let mut hs = HashSet::new(); hs.insert(x); hs }`
- Sequence comprehensions → verified `while` loops with invariants and decreases
- Filter patterns → external-body helper calls

#### `clone_method`

Controls how struct fields are cloned in generated code:
- `"clone"` (default): Uses `.clone()`
- `"clone_up_to_view"`: Uses `.clone_up_to_view()` which has `ensures res@ == self@` in Verus

Three code paths honor this setting: `transform_equality`, `categorize_output_assignments`, and `clone_if_input_ref`.

#### `manual_code`

Path (relative to the TOML file) to a `.rs` file whose contents are injected verbatim into the generated `verus! {}` block. Used for functions too complex for automatic transpilation (e.g., `CLearnerProcess2b` with 5-branch proof blocks).

## Collection Field Configuration

### `collection_fields`

Lists struct fields that are `HashSet` types, requiring `clone_hashset()` instead of `.clone()`.

```toml
collection_fields = ["rm_state", "tm_prepared"]
```

### `vec_fields`

Lists struct fields that are `Vec` types requiring special clone handling.

```toml
vec_fields = ["history"]
```

### `clone_fields`

Lists struct fields with non-Copy enum types that need explicit clone helpers.

```toml
clone_fields = ["role"]
```

### `clone_field_types`

Maps clone_fields to their concrete type names (for generating clone helper signatures).

```toml
[clone_field_types]
role = "CNodeRole"
```

### `struct_vec_fields`

Maps struct fields to `[ExecType, SpecType]` pairs for `Vec<Struct>` fields that need mapped-view ensures.

```toml
[struct_vec_fields]
log = ["CLogEntry", "LLogEntry"]
```

Generates a `clone_log` external-body helper with:
```rust
ensures res@.map(|i: int, e: CLogEntry| e@) =~= v@.map(|i: int, e: CLogEntry| e@)
```

### `[map_fields]`

Configures HashMap fields with deep key+value type conversion for `abstractify_*` proofs.

```toml
[map_fields]
"unexecuted_learner_state" = ["CLearnerState", "clearnerstate", "CLearnerTuple"]
# field_name = [exec_type, abstractify_prefix, value_type]
```

Generates:
1. **Abstractify proof lemmas**: `lemma_abstractify_empty_{prefix}`, `lemma_abstractify_{prefix}_insert`, `lemma_abstractify_{prefix}_remove`, `lemma_abstractify_singleton_{prefix}`
2. **External-body helpers**: `clone_{prefix}()`, `filter_{prefix}()`
3. **Proof block integration**: Auto-calls lemmas when detecting HashMap operations

## Function Control

### `skip_functions`

Functions to skip during transpilation (will not appear in output).

```toml
skip_functions = ["LNext", "LChosen"]
```

### `spec_only_functions`

Functions that remain as spec-only (no exec counterpart generated).

```toml
spec_only_functions = ["LeqUpperBound"]
```

### `[function_paths]`

Maps function names to qualified Rust paths for cross-module calls.

```toml
[function_paths]
"CBroadcastToEveryone" = "crate::generated::RSL::broadcast_gen::CBroadcastToEveryone"
```

### `[extra_requires]`

Additional `requires` clauses injected into specific functions.

```toml
[extra_requires]
"CClientRequest" = ["s.role is CServerRole::Leader"]
```

### `[variant_remapping]`

Maps spec enum variant names to exec enum variant names.

```toml
[variant_remapping]
"Follower" = "CServerRole::Follower"
```

## Type Configuration

### `primitive_types`

Types treated as primitives (use `*param as int` in ensures, not `param@`).

```toml
primitive_types = ["OperationNumber", "NodeIdentity"]
```

### `[view_overrides]`

Custom view expressions for specific types.

```toml
[view_overrides]
"COperationNumber" = "s as int"
```

### `custom_imports`

Lines injected at the top of the generated file.

```toml
custom_imports = [
    "use vstd::prelude::*;",
    "use crate::protocol::RSL::types::*;",
]
```

## Complete Example

```toml
[naming]
spec_prefix = "L"
exec_prefix = "C"
int_type = "u64"
nat_type = "u64"

[remapping]
"LearnerState" = "CLearnerState"
"LearnerTuple" = "CLearnerTuple"

[output]
generate_proofs = true
generate_loops_for_verification = true
generate_inline_types = false
clone_method = "clone_up_to_view"
manual_code = "learner_manual.rs"

collection_fields = []

[map_fields]
"unexecuted_learner_state" = ["CLearnerState", "clearnerstate", "CLearnerTuple"]

skip_functions = ["LLearnerProcess2b"]

custom_imports = [
    "use vstd::prelude::*;",
    "use crate::protocol::RSL::learner::*;",
]
```
