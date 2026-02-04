# TLA+ to Verus Transpiler Limitations

This document details the known limitations of the TLA+ to Verus transpiler, including unsupported features, type inference constraints, and patterns that require manual intervention.

## Table of Contents

1. [Unsupported TLA+ Features](#unsupported-tla-features)
2. [Parser Limitations](#parser-limitations)
3. [Type Inference Limitations](#type-inference-limitations)
4. [Translation Limitations](#translation-limitations)
5. [Patterns Requiring Manual Intervention](#patterns-requiring-manual-intervention)
6. [Workarounds](#workarounds)

---

## Unsupported TLA+ Features

### Temporal Logic Operators

The transpiler focuses on safety specifications and does not support temporal operators:

| Operator | TLA+ Syntax | Status |
|----------|-------------|--------|
| Always | `[]P` | ❌ Not supported |
| Eventually | `<>P` | ❌ Not supported |
| Leads-to | `P ~> Q` | ❌ Not supported |
| Until | `P \U Q` | ❌ Not supported |

**Reason**: Verus verifies program correctness at compile time using SMT solvers. Temporal properties require model checking or runtime verification, which are outside Verus's scope.

**Workaround**: Express safety invariants as state predicates that hold at each step. For liveness properties, consider using external model checkers like TLC.

### Fairness Conditions

| Feature | TLA+ Syntax | Status |
|---------|-------------|--------|
| Weak Fairness | `WF_vars(Action)` | ❌ Not supported |
| Strong Fairness | `SF_vars(Action)` | ❌ Not supported |

**Reason**: Fairness conditions constrain infinite execution traces, which Verus cannot directly verify.

### Module System Features

| Feature | TLA+ Syntax | Status |
|---------|-------------|--------|
| Module Instantiation | `INSTANCE M WITH ...` | ❌ Not supported |
| Parameterized Modules | `MODULE M(params)` | ❌ Not supported |
| LOCAL definitions | `LOCAL Op == ...` | ⚠️ Partial (translated as private) |

**Workaround**: Manually inline module instances or refactor as a single module.

### Proof Constructs

| Feature | TLA+ Syntax | Status |
|---------|-------------|--------|
| Theorems | `THEOREM` | ❌ Not supported |
| Proofs | `PROOF` | ❌ Not supported |
| Assumptions | `ASSUME` | ❌ Not supported |
| Assertions | `ASSERT` | ❌ Not supported |

**Reason**: Verus has its own proof system using `proof fn` and `ensures`/`requires` clauses.

---

## Parser Limitations

### Multi-line Conjunctions

The parser does not support TLA+'s multi-line conjunction/disjunction format:

```tla
(* NOT SUPPORTED *)
Init ==
    /\ x = 0
    /\ y = 1
    /\ z = 2

(* SUPPORTED - single line *)
Init == x = 0 /\ y = 1 /\ z = 2
```

**Workaround**: Rewrite multi-line conjunctions as single-line expressions.

### Range Operator

The `..` range operator is not supported:

```tla
(* NOT SUPPORTED *)
TypeOK == x \in 1..10

(* SUPPORTED - explicit bounds *)
TypeOK == x \in Nat /\ x >= 1 /\ x <= 10
```

### Recursive Operator Definitions

```tla
(* NOT SUPPORTED *)
Factorial[n \in Nat] ==
    IF n = 0 THEN 1 ELSE n * Factorial[n-1]
```

**Workaround**: Use iterative specifications or define recursive functions in Verus directly.

### Complex EXCEPT Syntax

Nested or multiple-path EXCEPT updates are not fully supported:

```tla
(* NOT SUPPORTED *)
f' = [f EXCEPT ![a][b] = v, ![c] = w]

(* SUPPORTED - single update *)
f' = [f EXCEPT ![a] = v]
```

### String Escape Sequences

Limited support for escape sequences in strings:

```tla
(* May not work correctly *)
msg == "line1\nline2"
```

---

## Type Inference Limitations

### Polymorphic Operators

The type inference engine may produce overly general types for polymorphic operations:

```tla
(* Type inference may be imprecise *)
EmptySeq == << >>  (* Type: Seq[T0] where T0 is unknown *)
```

**Solution**: Provide explicit type annotations in a `.tla-types` file.

### Higher-Order Operators

Operators that take other operators as parameters have limited type inference:

```tla
(* Type inference may fail *)
Apply(Op(_), x) == Op(x)
```

### Recursive Type Structures

Self-referential types may not be properly inferred:

```tla
(* May require manual annotation *)
Tree == [val: Int, children: Seq(Tree)]
```

### Union Types

TLA+ allows values of different types in the same context, which Verus doesn't support:

```tla
(* Problematic - heterogeneous set *)
S == {1, "two", TRUE}
```

### Type Variables in Quantifiers

Quantifiers with complex type constraints may not infer correctly:

```tla
(* May need type annotation *)
\A x, y \in S : x # y => P(x, y)
```

---

## Translation Limitations

### Infinite Sets

TLA+ allows reasoning about infinite sets, but Verus sets must be finite:

```tla
(* TLA+ allows infinite domain *)
f \in [Nat -> Nat]  (* Function from all naturals *)

(* Verus requires finite domains *)
```

### Untyped Equality

TLA+ equality can compare values of different types, returning FALSE:

```tla
(* Valid TLA+ - returns FALSE *)
1 = "one"
```

Verus requires type-compatible operands for equality.

### Choose Semantics

The `CHOOSE` operator in TLA+ is deterministic but unspecified. Verus's `choose` is similar but may have different semantics:

```tla
CHOOSE x \in S : P(x)  (* Picks the same x every time in TLA+ *)
```

### Non-Determinism

TLA+ actions can be non-deterministic:

```tla
Next == x' \in {1, 2, 3}  (* Non-deterministic choice *)
```

Verus exec functions must be deterministic. The transpiler generates spec functions only.

---

## Patterns Requiring Manual Intervention

### 1. State Machine Initialization

The transpiler generates spec functions, but initialization of exec state requires manual implementation:

```rust
// Generated spec
pub open spec fn LInit(s: LState) -> bool { ... }

// Manual implementation needed
pub exec fn create_initial_state() -> (s: CState)
    ensures s@.satisfies_init()
{ ... }
```

### 2. Action Handlers

Exec implementations of actions require manual intervention for I/O and side effects:

```rust
// Generated spec
pub open spec fn LHandleRequest(s: LState, s_: LState, req: Request) -> bool { ... }

// Manual implementation needed for actual I/O
pub exec fn handle_request(s: &mut CState, req: &CRequest) -> CResponse { ... }
```

### 3. Collection Bounds

TLA+ doesn't require explicit bounds on collections. Verus needs capacity hints:

```tla
(* TLA+ - unbounded *)
buffer' = Append(buffer, msg)
```

```rust
// Verus - needs capacity
let mut buffer: Vec<CMessage> = Vec::with_capacity(MAX_BUFFER_SIZE);
```

### 4. Concurrency Patterns

TLA+ interleaving semantics differ from Rust's memory model:

```tla
(* TLA+ - atomic action *)
Process(p) == x' = x + 1 /\ y' = y + 1
```

In Rust, this may require explicit synchronization (mutexes, atomics).

### 5. Message Serialization

TLA+ messages are abstract. Concrete implementations need serialization:

```tla
(* TLA+ - abstract message *)
Send(m) == msgs' = msgs \cup {m}
```

```rust
// Manual implementation needed
impl Marshalable for CMessage {
    fn marshal(&self) -> Vec<u8> { ... }
    fn unmarshal(bytes: &[u8]) -> Self { ... }
}
```

### 6. Error Handling

TLA+ typically doesn't model errors. Verus implementations need error handling:

```rust
// Manual error handling needed
pub exec fn process(s: &mut CState, input: &CInput) -> Result<COutput, Error> { ... }
```

---

## Workarounds

### For Multi-line Conjunctions

Convert multi-line format to single-line:

```tla
(* Before *)
Init ==
    /\ x = 0
    /\ y = 1

(* After *)
Init == x = 0 /\ y = 1
```

### For Range Operator

Replace `a..b` with explicit predicates:

```tla
(* Before *)
x \in 1..10

(* After *)
x \in Nat /\ x >= 1 /\ x <= 10
```

### For Recursive Definitions

Use iterative specifications or helper lemmas:

```tla
(* Instead of recursive definition *)
Sum(S) == (* Use quantifiers or external lemma *)
```

### For Type Inference Issues

Create a `.tla-types` file:

```
[variables]
counter: Nat
buffer: Seq[Message]

[constants]
MaxSize: Nat
Servers: Set[ServerId]

[records]
Message {
    sender: ServerId
    payload: Seq[Int]
}
```

### For Complex EXCEPT

Chain multiple updates:

```tla
(* Instead of *)
f' = [f EXCEPT ![a] = v1, ![b] = v2]

(* Use *)
temp == [f EXCEPT ![a] = v1]
f' = [temp EXCEPT ![b] = v2]
```

---

## Getting Help

If you encounter a pattern that isn't covered here:

1. Check the [TLA+ to Verus Translation Guide](./tla-to-verus-guide.md) for supported constructs
2. Review the test examples in `transpiler/tests/tla_examples/`
3. Consider filing an issue on the project repository

## See Also

- [TLA+ to Verus Translation Guide](./tla-to-verus-guide.md)
- [Verus Documentation](https://verus-lang.github.io/verus/)
- [TLA+ Language Manual](https://lamport.azurewebsites.net/tla/tla.html)
