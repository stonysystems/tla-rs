# Supported TLA+ Features

This document describes the TLA+ features supported by the tla-rs bidirectional transpiler.

## Overview

The transpiler supports converting TLA+ specifications to Verus spec functions and vice versa. This enables formal verification of TLA+-style specifications using Verus's deductive verification.

## Module Structure

### Supported
- `---- MODULE ModuleName ----` / `====` delimiters
- `EXTENDS` clause for module imports
- `CONSTANT` / `CONSTANTS` declarations
- `VARIABLE` / `VARIABLES` declarations
- `ASSUME` statements
- Operator definitions (with and without parameters)
- `LOCAL` operator definitions
- `RECURSIVE` operator declarations

### Not Supported
- `THEOREM` declarations (parsed but not translated)
- `INSTANCE` with substitution (partial support)
- Module composition operators

## Expressions

### Literals
| TLA+ | Verus | Status |
|------|-------|--------|
| `TRUE`, `FALSE` | `true`, `false` | ✅ |
| Decimal numbers (`42`) | `42` | ✅ |
| Hex numbers (`\hFF`) | `0xFF` | ✅ |
| Binary numbers (`\b101`) | `0b101` | ✅ |
| Octal numbers (`\o77`) | `0o77` | ✅ |
| Strings (`"hello"`) | `"hello"` | ✅ |

### Logical Operators
| TLA+ | Verus | Status |
|------|-------|--------|
| `/\` (conjunction) | `&&` | ✅ |
| `\/` (disjunction) | `\|\|` | ✅ |
| `~` (negation) | `!` | ✅ |
| `=>` (implication) | `==>` | ✅ |
| `<=>` (equivalence) | `<==>` | ✅ |

### Comparison Operators
| TLA+ | Verus | Status |
|------|-------|--------|
| `=` | `==` | ✅ |
| `#` or `/=` | `!=` | ✅ |
| `<`, `>`, `<=`, `>=` | Same | ✅ |

### Arithmetic Operators
| TLA+ | Verus | Status |
|------|-------|--------|
| `+`, `-`, `*` | Same | ✅ |
| `\div` or `/` | `/` | ✅ |
| `%` (modulo) | `%` | ✅ |
| `^` (exponentiation) | `.pow()` | ✅ |
| `..` (integer range) | `Set::new(\|x\| ...)` | ✅ |

### Set Operators
| TLA+ | Verus | Status |
|------|-------|--------|
| `\in` | `.contains()` | ✅ |
| `\notin` | `!.contains()` | ✅ |
| `\subseteq` | `.subset_of()` | ✅ |
| `\cup` | `.union()` | ✅ |
| `\cap` | `.intersect()` | ✅ |
| `\` (set minus) | `.difference()` | ✅ |
| `\X` (cartesian product) | `.cartesian_product()` | ✅ |
| `SUBSET` (power set) | `.powerset()` | ✅ |
| `UNION` (flatten) | `.flatten()` | ✅ |
| `{a, b, c}` (set enum) | `set![a, b, c]` | ✅ |
| `{x \in S : P(x)}` (filter) | `.filter(\|x\| P(x))` | ✅ |
| `{f(x) : x \in S}` (map) | `.map(\|x\| f(x))` | ✅ |

### Sequence Operators
| TLA+ | Verus | Status |
|------|-------|--------|
| `<<a, b, c>>` (tuple) | `seq![a, b, c]` | ✅ |
| `Append(s, x)` | `.push(x)` | ✅ |
| `Head(s)` | `[0]` | ✅ |
| `Tail(s)` | `.drop_first()` | ✅ |
| `Len(s)` | `.len()` | ✅ |
| `SubSeq(s, m, n)` | `.subrange(m-1, n)` | ✅ |
| `s[i]` | `s[i]` | ✅ (1-indexed → 0-indexed) |

### Function/Map Operators
| TLA+ | Verus | Status |
|------|-------|--------|
| `DOMAIN f` | `.dom()` | ✅ |
| `f[x]` | `f[x]` | ✅ |
| `[x \in S \|-> e]` | `Map::new(S, \|x\| e)` | ✅ |
| `[f EXCEPT ![i] = v]` | `.insert(i, v)` | ✅ |

### Record Operators
| TLA+ | Verus | Status |
|------|-------|--------|
| `[field1 \|-> v1, ...]` | `{ field1: v1, ... }` | ✅ |
| `r.field` | `r.field` | ✅ |
| Record type `[f1: T1, ...]` | Struct definition | ✅ |

### Quantifiers
| TLA+ | Verus | Status |
|------|-------|--------|
| `\A x \in S : P(x)` | `forall \|x\| S.contains(x) ==> P(x)` | ✅ |
| `\E x \in S : P(x)` | `exists \|x\| S.contains(x) && P(x)` | ✅ |
| `CHOOSE x \in S : P(x)` | `choose \|x\| S.contains(x) && P(x)` | ✅ |

### Control Flow
| TLA+ | Verus | Status |
|------|-------|--------|
| `IF c THEN t ELSE e` | `if c { t } else { e }` | ✅ |
| `CASE` | `if/else if/else` chain | ✅ |
| `LET ... IN ...` | `{ let ...; ... }` | ✅ |

### Action Operators
| TLA+ | Verus | Description | Status |
|------|-------|-------------|--------|
| `x'` (primed) | `x_` | Next-state variable | ✅ |
| `UNCHANGED <<x, y>>` | `x_ == x && y_ == y` | Variables unchanged | ✅ |
| `ENABLED A` | `exists \|_\| A` | Action enabled | ⚠️ Partial |

### Temporal Operators
| TLA+ | Verus | Status |
|------|-------|--------|
| `[]P` (always) | `always(P)` | ⚠️ Marker only |
| `<>P` (eventually) | `eventually(P)` | ⚠️ Marker only |
| `P ~> Q` (leads-to) | `leads_to(P, Q)` | ⚠️ Marker only |
| `WF_v(A)` | `weak_fairness(v, A)` | ⚠️ Marker only |
| `SF_v(A)` | `strong_fairness(v, A)` | ⚠️ Marker only |

Note: Temporal operators are translated to marker functions since Verus doesn't have native temporal logic support.

## Standard Modules

### EXTENDS Support
| Module | Support Level |
|--------|--------------|
| `Naturals` | ✅ Built-in |
| `Integers` | ✅ Built-in |
| `Sequences` | ✅ `vstd::seq::*` |
| `FiniteSets` | ✅ `vstd::set::*` |
| `TLC` | ⚠️ Partial |

## Limitations

1. **Temporal Logic**: Verus is not a temporal logic prover, so temporal operators are translated to markers only.
2. **Higher-Order Operators**: Limited support for operators that take operators as parameters.
3. **Module Composition**: `INSTANCE WITH` substitution has partial support.
4. **Recursive Functions**: Supported but requires `RECURSIVE` declaration.
5. **Complex Type Constraints**: Some advanced TLA+ type idioms may not translate cleanly.

## Round-Trip Consistency

The transpiler maintains semantic equivalence for:
- Basic expressions (literals, operators, variables)
- Quantified expressions
- Set/sequence/function operations
- Records and tuples
- Control flow (IF-THEN-ELSE, CASE, LET-IN)

Known non-preservable constructs:
- Comments (stripped during parsing)
- Whitespace/formatting
- Some operator associativity may change
- Temporal operators (converted to markers)
