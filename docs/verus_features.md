# Supported Verus Features

This document describes the Verus spec function features supported by the tla-rs bidirectional transpiler.

## Overview

The transpiler extracts spec functions from Verus code and converts them to TLA+ specifications. This enables TLA+ tooling (SANY, TLC) to work with Verus specifications.

## Supported Constructs

### Function Types
| Verus | TLA+ | Status |
|-------|------|--------|
| `spec fn` | Operator definition | ✅ |
| `open spec fn` | Public operator | ✅ |
| `pub spec fn` | Public operator | ✅ |

### Type Annotations
| Verus | TLA+ | Status |
|-------|------|--------|
| `int` | `Int` | ✅ |
| `nat` | `Nat` | ✅ |
| `bool` | `BOOLEAN` | ✅ |
| `Seq<T>` | Sequences | ✅ |
| `Set<T>` | Sets | ✅ |
| `Map<K, V>` | Functions `[K -> V]` | ✅ |
| `Option<T>` | `NONE \| SOME(value)` | ✅ |
| Struct types | Records | ✅ |
| Enum types | Tagged records | ✅ |
| Tuple types | `<<...>>` | ✅ |

### Struct Definitions
```rust
pub struct LState {
    pub field1: int,
    pub field2: bool,
}
```
Translates to TLA+ record type:
```tla
State == [field1: Int, field2: BOOLEAN]
```

### Enum Definitions
```rust
pub enum LMessage {
    Request { value: int },
    Response { result: int },
}
```
Translates to TLA+ union of records with a tag field.

### Literals
| Verus | TLA+ | Status |
|-------|------|--------|
| `true`, `false` | `TRUE`, `FALSE` | ✅ |
| Integer literals | Decimal numbers | ✅ |
| String literals | Strings | ✅ |

### Logical Operators
| Verus | TLA+ | Status |
|-------|------|--------|
| `&&`, `&&&` | `/\` | ✅ |
| `\|\|`, `\|\|\|` | `\/` | ✅ |
| `!` | `~` | ✅ |
| `==>` | `=>` | ✅ |
| `<==>` | `<=>` | ✅ |

### Comparison Operators
| Verus | TLA+ | Status |
|-------|------|--------|
| `==` | `=` | ✅ |
| `!=` | `#` | ✅ |
| `<`, `>`, `<=`, `>=` | Same | ✅ |

### Arithmetic Operators
| Verus | TLA+ | Status |
|-------|------|--------|
| `+`, `-`, `*` | Same | ✅ |
| `/` | `\div` | ✅ |
| `%` | `%` | ✅ |

### Collection Operations

#### Sequences (`Seq<T>`)
| Verus | TLA+ | Status |
|-------|------|--------|
| `Seq::empty()` | `<<>>` | ✅ |
| `seq![a, b, c]` | `<<a, b, c>>` | ✅ |
| `s.len()` | `Len(s)` | ✅ |
| `s[i]` | `s[i+1]` | ✅ (0-indexed → 1-indexed) |
| `s.push(x)` | `Append(s, x)` | ✅ |
| `s.first()` | `Head(s)` | ✅ |
| `s.drop_first()` | `Tail(s)` | ✅ |
| `s.subrange(i, j)` | `SubSeq(s, i+1, j)` | ✅ |

#### Sets (`Set<T>`)
| Verus | TLA+ | Status |
|-------|------|--------|
| `Set::empty()` | `{}` | ✅ |
| `set![a, b, c]` | `{a, b, c}` | ✅ |
| `s.contains(x)` | `x \in s` | ✅ |
| `s.insert(x)` | `s \cup {x}` | ✅ |
| `s.remove(x)` | `s \ {x}` | ✅ |
| `s.union(t)` | `s \cup t` | ✅ |
| `s.intersect(t)` | `s \cap t` | ✅ |
| `s.difference(t)` | `s \ t` | ✅ |
| `s.subset_of(t)` | `s \subseteq t` | ✅ |
| `s.len()` | `Cardinality(s)` | ✅ |

#### Maps (`Map<K, V>`)
| Verus | TLA+ | Status |
|-------|------|--------|
| `Map::empty()` | `<<>>` | ✅ |
| `m[k]` | `m[k]` | ✅ |
| `m.contains_key(k)` | `k \in DOMAIN m` | ✅ |
| `m.insert(k, v)` | `[m EXCEPT ![k] = v]` | ✅ |
| `m.dom()` | `DOMAIN m` | ✅ |

### Quantifiers
| Verus | TLA+ | Status |
|-------|------|--------|
| `forall\|x: T\| P(x)` | `\A x \in T : P(x)` | ✅ |
| `exists\|x: T\| P(x)` | `\E x \in T : P(x)` | ✅ |
| `choose\|x: T\| P(x)` | `CHOOSE x \in T : P(x)` | ✅ |

### Control Flow
| Verus | TLA+ | Status |
|-------|------|--------|
| `if c { t } else { e }` | `IF c THEN t ELSE e` | ✅ |
| `match` expressions | `CASE` | ✅ |
| `let x = e; body` | `LET x == e IN body` | ✅ |

### Record/Struct Operations
| Verus | TLA+ | Status |
|-------|------|--------|
| `s.field` | `s.field` | ✅ |
| `MyStruct { field: v }` | `[field \|-> v]` | ✅ |
| Struct update syntax | `[s EXCEPT !.field = v]` | ✅ |

### Tuple Operations
| Verus | TLA+ | Status |
|-------|------|--------|
| `(a, b, c)` | `<<a, b, c>>` | ✅ |
| `t.0`, `t.1` | `t[1]`, `t[2]` | ✅ (0-indexed → 1-indexed) |

## Features NOT Translated

These Verus features are stripped during conversion to TLA+:

### Proof Annotations
- `requires` clauses
- `ensures` clauses
- `decreases` clauses
- `proof` blocks
- `assert` statements (in proofs)
- `assume` statements (in proofs)

### Verification Hints
- `#[trigger]` annotations
- `#[verifier(external)]` markers
- Ghost code markers

### Execution-Specific Code
- `exec fn` implementations
- `tracked` variables
- Mutable references (`&mut`)

## Naming Conventions

The transpiler uses the following naming conventions:

### Type Prefixes
| Verus Prefix | TLA+ Result | Purpose |
|--------------|-------------|---------|
| `L` | Stripped | Logical/spec types (`LReplica` → `Replica`) |
| `C` | Stripped | Concrete/exec types (`CState` → `State`) |

### Special Cases
- `LearnerTuple` → `LearnerTuple` (L not stripped, followed by lowercase)
- `Length` → `Length` (L not stripped, followed by lowercase)

## Module Generation

When converting a Verus file to TLA+, the transpiler:

1. Creates a TLA+ module with the same name (minus `_s` suffix if present)
2. Adds standard `EXTENDS` based on used types
3. Declares `CONSTANTS` for type parameters and unresolved types
4. Generates operators from each `spec fn`
5. Generates type definitions from structs and enums

### Example

Verus input:
```rust
verus! {
    pub struct LState {
        pub value: int,
        pub active: bool,
    }

    pub open spec fn StateInit(s: LState) -> bool {
        s.value == 0 && s.active
    }
}
```

TLA+ output:
```tla
---- MODULE state ----
EXTENDS Integers, Sequences, FiniteSets

State == [value: Int, active: BOOLEAN]

StateInit(s) ==
    s.value = 0 /\ s.active

====
```

## Round-Trip Preservation

The following are preserved across round-trips:
- Function names (with prefix stripping/restoration)
- Parameter names and order
- Expression structure
- Logical meaning

The following may change:
- Whitespace and formatting
- Comments (stripped)
- Some operator precedence (parentheses added for safety)
- Explicit type annotations (inferred in TLA+)
