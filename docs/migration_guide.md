# Migration Guide: TLA+ ↔ Verus

This guide helps you migrate specifications between TLA+ and Verus using the tla-rs bidirectional transpiler.

## Prerequisites

- Verus transpiler CLI (`verus-transpile`)
- TLA+ toolbox (optional, for validation)
- Understanding of both TLA+ and Verus syntax

## TLA+ to Verus Migration

### Step 1: Prepare Your TLA+ Specification

Ensure your TLA+ module:
1. Uses standard module structure (`---- MODULE ... ----` / `====`)
2. Declares all CONSTANTS and VARIABLES
3. Avoids unsupported temporal operators (or be prepared to handle them manually)

Example TLA+ (`Counter.tla`):
```tla
---- MODULE Counter ----
EXTENDS Integers

VARIABLE count

Init == count = 0

Increment == count' = count + 1

TypeOK == count \in Nat

====
```

### Step 2: Run the Translator

```bash
# Parse and translate to Verus
verus-transpile tla2verus --input Counter.tla --output counter_s.rs
```

### Step 3: Review Generated Verus Code

The generated code will look like:
```rust
//! Generated from TLA+ module: Counter

use vstd::prelude::*;

verus! {

/// State for Counter module
#[derive(Clone)]
pub struct LState {
    pub count: int,
}

/// Init operator
pub open spec fn LInit(s: LState) -> bool {
    s.count == 0
}

/// Increment operator
pub open spec fn LIncrement(s: LState, s_: LState) -> bool {
    s_.count == s.count + 1
}

/// TypeOK operator
pub open spec fn LTypeOK(s: LState) -> bool {
    s.count >= 0  // nat translated to >= 0 constraint
}

} // verus!
```

### Step 4: Manual Adjustments

You may need to:
1. Add missing type imports
2. Adjust collection operations for Verus idioms
3. Handle temporal operators (if any)
4. Add `ensures`, `requires` clauses for verification

### Common TLA+ → Verus Conversions

| TLA+ Pattern | Verus Pattern |
|--------------|---------------|
| `UNCHANGED x` | `x_ == x` (or exclude from s_) |
| `x' = y` | `s_.x == y` |
| `x \in Nat` | `x >= 0` or `x: nat` |
| `Cardinality(S) = n` | `S.len() == n` |
| `\E x \in S : P` | `exists\|x\| S.contains(x) && P` |

## Verus to TLA+ Migration

### Step 1: Prepare Your Verus Specification

Ensure your Verus file:
1. Contains `verus!` blocks with spec functions
2. Uses supported types (`int`, `nat`, `bool`, `Seq<T>`, `Set<T>`, `Map<K,V>`)
3. Has clear spec function signatures

Example Verus (`counter_s.rs`):
```rust
verus! {
    pub struct LCounter {
        pub value: int,
    }

    pub open spec fn CounterInit(c: LCounter) -> bool {
        c.value == 0
    }

    pub open spec fn CounterIncrement(c: LCounter, c_: LCounter) -> bool {
        c_.value == c.value + 1
    }
}
```

### Step 2: Run the Converter

```bash
# Single file
verus-transpile verus2tla --input counter_s.rs --output Counter.tla

# Batch mode for entire directories
verus-transpile verus2tla --batch --input src/protocol/RSL/ --output src/tla+/RSL/
```

### Step 3: Review Generated TLA+

The generated code will look like:
```tla
---- MODULE counter ----
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY

EXTENDS Integers, Sequences, FiniteSets

Counter == [value: Int]

CounterInit(c) ==
    c.value = 0

CounterIncrement(c, c_) ==
    c_.value = c.value + 1

====
```

### Step 4: Validate with SANY

```bash
java -cp tla2tools.jar tla2sany.SANY Counter.tla
```

### Step 5: Manual Adjustments

You may need to:
1. Add module-level CONSTANTS for type parameters
2. Define type invariants (TypeOK predicates)
3. Add Init/Next definitions for TLC model checking
4. Handle Verus-specific constructs that don't map directly

### Common Verus → TLA+ Conversions

| Verus Pattern | TLA+ Pattern |
|---------------|--------------|
| `Seq::empty()` | `<<>>` |
| `s.len()` | `Len(s)` |
| `s.push(x)` | `Append(s, x)` |
| `m.insert(k, v)` | `[m EXCEPT ![k] = v]` |
| `forall\|x\| ...` | `\A x : ...` |

## Bidirectional Workflow

For maintaining specifications in both formats:

### 1. Choose a Source of Truth

Decide whether TLA+ or Verus is your primary format:
- **TLA+ primary**: Write specs in TLA+, generate Verus for verification
- **Verus primary**: Write specs in Verus, generate TLA+ for TLC model checking

### 2. Generate and Don't Edit

Generated files are marked with:
```
\* Auto-generated from Verus spec by verus2tla
\* DO NOT EDIT MANUALLY
```

If you need changes, edit the source format and regenerate.

### 3. Use Round-Trip Testing

Run the roundtrip tests to verify conversion accuracy:
```bash
cargo test --test roundtrip
```

## Troubleshooting

### "Parser error" in Generated TLA+

Some complex Verus expressions may generate TLA+ that our parser can't round-trip. The TLA+ is still valid (verified by SANY), but may need manual adjustment for further processing.

### "Type mismatch" After Conversion

Check:
1. Integer indexing (TLA+ is 1-indexed, Verus is 0-indexed)
2. Collection types match (Seq vs array, Set vs HashSet)
3. Quantifier bounds are preserved

### "Missing import" in Generated Verus

Add the appropriate `use` statement:
```rust
use vstd::prelude::*;
use vstd::seq::*;
use vstd::set::*;
```

### Temporal Operators

Temporal operators (`[]`, `<>`, `~>`, `WF`, `SF`) in TLA+ are converted to marker functions in Verus since Verus doesn't support temporal reasoning. You'll need to handle liveness properties differently.

## Example: RSL Protocol Migration

The tla-rs project includes a complete example of migrating the RSL (Replicated State Machine) protocol:

```
src/protocol/RSL/     # Original Verus specs
src/tla+/RSL/         # Generated TLA+ specs
```

Key files:
- `types.rs` → `Types.tla`
- `proposer.rs` → `Proposer.tla`
- `acceptor.rs` → `Acceptor.tla`
- `replica.rs` → `Replica.tla`
- etc.

Use these as reference for complex protocol migrations.
