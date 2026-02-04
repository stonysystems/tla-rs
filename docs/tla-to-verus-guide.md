# TLA+ to Verus Translation Guide

This guide documents how to translate TLA+ specifications to Verus code using the transpiler.

## Table of Contents

1. [Overview](#overview)
2. [Quick Start](#quick-start)
3. [Supported TLA+ Constructs](#supported-tla-constructs)
4. [Type Annotation Format](#type-annotation-format)
5. [CLI Usage](#cli-usage)
6. [Examples](#examples)
7. [Limitations](#limitations)

---

## Overview

The TLA+ to Verus transpiler converts TLA+ specifications into Verus Rust code. The translation process:

1. **Parses** TLA+ source files (`.tla`)
2. **Infers types** from usage patterns
3. **Generates** Verus `spec fn` declarations
4. **Creates** mode annotations for the spec-to-exec transpiler

### Architecture

```
TLA+ (.tla) → [Parser] → [Type Inference] → [Translator] → Verus spec (.rs)
                                                        → Mode annotations (.automan)
```

---

## Quick Start

### Basic Translation

Translate a TLA+ file to Verus spec:

```bash
cargo run -- translate-tla --input spec.tla --output spec.rs
```

### Full Pipeline

Run the complete pipeline from TLA+ to Verus exec:

```bash
cargo run -- pipeline --tla-input spec.tla --exec-output impl.rs
```

### With Type Annotations

Provide explicit type annotations for better type inference:

```bash
cargo run -- translate-tla --input spec.tla --types spec.tla-types --output spec.rs
```

---

## Supported TLA+ Constructs

### Module Structure

| TLA+ Construct | Verus Output | Notes |
|----------------|--------------|-------|
| `---- MODULE Name ----` | Module comment + imports | |
| `EXTENDS Naturals` | `use vstd::prelude::*;` | Standard module mapping |
| `EXTENDS Sequences` | `use vstd::seq::*;` | |
| `EXTENDS FiniteSets` | `use vstd::set::*;` | |
| `CONSTANT C` | `pub struct LConstants { pub C: Type }` | |
| `VARIABLE x, y` | `pub struct LState { pub x: Type, pub y: Type }` | |
| `Op == expr` | `pub open spec fn LOp(...) -> bool { expr }` | |

### Logical Operators

| TLA+ | Verus | Notes |
|------|-------|-------|
| `/\` | `&&` | Conjunction |
| `\/` | `\|\|` | Disjunction |
| `~` | `!` | Negation |
| `=>` | `==>` | Implication |
| `<=>` | `<==>` | Equivalence |
| `TRUE` | `true` | Boolean literal |
| `FALSE` | `false` | Boolean literal |

### Arithmetic Operators

| TLA+ | Verus | Notes |
|------|-------|-------|
| `+` | `+` | Addition |
| `-` | `-` | Subtraction |
| `*` | `*` | Multiplication |
| `\div` | `/` | Integer division |
| `%` | `%` | Modulo |
| `<` | `<` | Less than |
| `<=` | `<=` | Less than or equal |
| `>` | `>` | Greater than |
| `>=` | `>=` | Greater than or equal |
| `=` | `==` | Equality |
| `#` or `/=` | `!=` | Inequality |

### Set Operations

| TLA+ | Verus | Notes |
|------|-------|-------|
| `x \in S` | `S.contains(x)` | Membership |
| `x \notin S` | `!S.contains(x)` | Non-membership |
| `S \cup T` | `S.union(T)` | Union |
| `S \cap T` | `S.intersect(T)` | Intersection |
| `S \ T` | `S.difference(T)` | Set difference |
| `S \subseteq T` | `S.subset_of(T)` | Subset |
| `{}` | `Set::empty()` | Empty set |
| `{a, b, c}` | `set![a, b, c]` | Set enumeration |
| `{x \in S : P(x)}` | `S.filter(\|x\| P(x))` | Set filter |
| `{f(x) : x \in S}` | `S.map(\|x\| f(x))` | Set map |

### Sequence Operations

| TLA+ | Verus | Notes |
|------|-------|-------|
| `<<a, b, c>>` | `seq![a, b, c]` | Sequence literal |
| `Len(s)` | `s.len()` | Length |
| `Head(s)` | `s[0]` | First element |
| `Tail(s)` | `s.skip(1)` | All but first |
| `Append(s, x)` | `s.push(x)` | Append |
| `s \o t` | `s + t` | Concatenation |
| `s[i]` | `s[i as int]` | Index access |
| `SubSeq(s, m, n)` | `s.subrange(m, n)` | Subsequence |

### Function Operations

| TLA+ | Verus | Notes |
|------|-------|-------|
| `[x \in S \|-> e]` | `Map::new(\|x\| e)` | Function construction |
| `f[x]` | `f[x]` | Function application |
| `DOMAIN f` | `f.dom()` | Function domain |
| `[f EXCEPT ![a] = b]` | `f.insert(a, b)` | Function update |

### Records

| TLA+ | Verus | Notes |
|------|-------|-------|
| `[field1 \|-> v1, field2 \|-> v2]` | Struct construction | |
| `r.field` | `r.field` | Field access |
| `[r EXCEPT !.field = v]` | Struct update | |

### Quantifiers

| TLA+ | Verus | Notes |
|------|-------|-------|
| `\A x \in S : P(x)` | `forall \|x\| S.contains(x) ==> P(x)` | Universal |
| `\E x \in S : P(x)` | `exists \|x\| S.contains(x) && P(x)` | Existential |
| `CHOOSE x \in S : P(x)` | `choose \|x\| S.contains(x) && P(x)` | Choice |

### Control Flow

| TLA+ | Verus | Notes |
|------|-------|-------|
| `IF c THEN e1 ELSE e2` | `if c { e1 } else { e2 }` | Conditional |
| `CASE p1 -> e1 [] p2 -> e2` | Match expression | |
| `LET x == e IN body` | `{ let x = e; body }` | Let binding |

### Action Operators

| TLA+ | Verus | Notes |
|------|-------|-------|
| `x'` | `x_` | Primed (next-state) variable |
| `UNCHANGED <<x, y>>` | `x_ == x && y_ == y` | Unchanged variables |

---

## Type Annotation Format

Type annotations are stored in `.tla-types` files with the following format:

```
# Comments start with #

[variables]
counter: Nat
buffer: Seq[Int]
cache: Map[String, Int]

[constants]
MaxSize: Nat
Servers: Set[ServerId]

[operators]
Init: Bool
Next: Bool
TypeOK: Bool

[records]
Message {
    sender: ServerId
    receiver: ServerId
    payload: Int
}
```

### Supported Types

| Type Syntax | Description |
|-------------|-------------|
| `Int` | Integer |
| `Nat` | Natural number (non-negative integer) |
| `Bool` | Boolean |
| `String` | String |
| `Set[T]` | Set of type T |
| `Seq[T]` | Sequence of type T |
| `Map[K, V]` | Map from K to V |
| `(T1, T2, ...)` | Tuple |
| `T1 -> T2` | Function type |

---

## CLI Usage

### translate-tla Subcommand

```
verus-transpile translate-tla [OPTIONS] --input <INPUT>

Options:
  -i, --input <INPUT>              Input TLA+ file (.tla)
  -o, --output <OUTPUT>            Output Verus file (.rs)
  -t, --types <TYPES>              Type annotations file (.tla-types)
      --gen-modes                  Generate mode annotations file (.automan)
      --spec-prefix <PREFIX>       Spec function prefix (default: "L")
      --state-name <NAME>          State struct name (default: "State")
```

### pipeline Subcommand

```
verus-transpile pipeline [OPTIONS] --tla-input <INPUT> --exec-output <OUTPUT>

Options:
      --tla-input <INPUT>          Input TLA+ file (.tla)
      --exec-output <OUTPUT>       Output Verus exec file (.rs)
      --types <TYPES>              Type annotations file (.tla-types)
      --keep-intermediate          Keep intermediate spec and automan files
      --spec-output <FILE>         Custom path for intermediate spec file
      --spec-prefix <PREFIX>       Spec function prefix (default: "L")
      --exec-prefix <PREFIX>       Exec function prefix (default: "C")
      --state-name <NAME>          State struct name (default: "State")
  -c, --config <FILE>              Transpiler configuration file (TOML)
```

---

## Examples

### Example 1: Simple Counter

**TLA+ (Counter.tla):**
```tla
---------------------------- MODULE Counter ----------------------------
EXTENDS Naturals

CONSTANT MaxCount

VARIABLE count

TypeOK == count \in Nat /\ count <= MaxCount

Init == count = 0

Increment == count < MaxCount /\ count' = count + 1

Decrement == count > 0 /\ count' = count - 1

Next == Increment \/ Decrement

========================================================================
```

**Generated Verus:**
```rust
use vstd::prelude::*;

verus! {

pub struct LState {
    pub count: nat,
}

pub struct LConstants {
    pub MaxCount: nat,
}

pub open spec fn LTypeOK(s: LState) -> bool {
    (nat.contains(s.count) && (s.count <= MaxCount))
}

pub open spec fn LInit(s: LState) -> bool {
    (s.count == 0)
}

pub open spec fn LIncrement(s: LState, s_: LState) -> bool {
    ((s.count < MaxCount) && (s_.count == (s.count + 1)))
}

pub open spec fn LDecrement(s: LState, s_: LState) -> bool {
    ((s.count > 0) && (s_.count == (s.count - 1)))
}

pub open spec fn LNext(s: LState, s_: LState) -> bool {
    (LIncrement(s, s_) || LDecrement(s, s_))
}

} // verus!
```

### Example 2: Two-Phase Commit (Simplified)

**TLA+ (TwoPhase.tla):**
```tla
------------------------------ MODULE TwoPhase ------------------------------
EXTENDS Naturals

CONSTANT RM

VARIABLE rmState, tmState, tmPrepared

Init == rmState = {} /\ tmState = "init" /\ tmPrepared = {}

TMCommit == tmState = "init" /\ tmPrepared = RM /\ tmState' = "committed"
            /\ rmState' = rmState /\ tmPrepared' = tmPrepared

TMAbort == tmState = "init" /\ tmState' = "aborted"
           /\ rmState' = rmState /\ tmPrepared' = tmPrepared

Next == TMCommit \/ TMAbort

================================================================================
```

---

## Limitations

### Unsupported TLA+ Features

The following TLA+ features are **not currently supported**:

1. **Temporal Operators**
   - `[]` (always)
   - `<>` (eventually)
   - `~>` (leads-to)
   - `WF_vars(Action)` (weak fairness)
   - `SF_vars(Action)` (strong fairness)

2. **Multi-line Conjunctions**
   - The parser requires conjunctions on a single line
   - Use `a /\ b /\ c` instead of:
     ```
     /\ a
     /\ b
     /\ c
     ```

3. **Range Operator**
   - `1..10` is not supported
   - Use `x \in Nat /\ x >= 1 /\ x <= 10` instead

4. **Complex EXCEPT Syntax**
   - Nested EXCEPT updates
   - Multiple path updates in single EXCEPT

5. **Module Instances**
   - `INSTANCE ModuleName WITH ...`

6. **ASSUME Statements**
   - Assumption declarations

7. **THEOREM and PROOF**
   - Proof constructs

### Type Inference Limitations

1. **Polymorphic Functions**
   - Type inference may produce overly general types
   - Use type annotations for precise types

2. **Recursive Functions**
   - Limited support for type inference in recursive definitions

3. **Higher-Order Operators**
   - Type inference for operators that take operators as arguments

### Best Practices

1. **Use Simple Conjunctions**
   - Keep logical expressions on single lines when possible

2. **Provide Type Annotations**
   - For complex specifications, provide `.tla-types` files

3. **Test Incrementally**
   - Translate small modules first to verify syntax support

4. **Review Generated Code**
   - Always review generated Verus code for correctness

---

## See Also

- [Verus Documentation](https://verus-lang.github.io/verus/)
- [TLA+ Language Manual](https://lamport.azurewebsites.net/tla/tla.html)
- [Transpiler README](../transpiler/README.md)
