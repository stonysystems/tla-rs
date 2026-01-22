# Supported Patterns and Templates

This document describes the spec patterns that the transpiler can automatically convert to executable code.

## Quantifier Templates

### SeqComprehension

Constructs a sequence from an index expression.

**Spec Pattern:**
```rust
forall |i: int| 0 <= i < len ==> seq[i] == f(i)
```

**Generated Code:**
```rust
(0..len).map(|i| f(i)).collect()
```

**Example:**
```rust
// Spec
forall |i: int| 0 <= i < n ==> result[i] == init_value
// Exec
let result: Vec<T> = (0..n).map(|_| init_value.clone()).collect();
```

### MapComprehension

Constructs a map from domain and value expressions.

**Spec Pattern:**
```rust
forall |k| k in domain ==> map[k] == f(k)
```

**Generated Code:**
```rust
domain.iter().map(|k| (k.clone(), f(k))).collect()
```

### SetComprehension

Constructs a set from a predicate.

**Spec Pattern:**
```rust
forall |x| x in set <==> predicate(x)
```

**Generated Code:**
```rust
source.iter().filter(|x| predicate(x)).cloned().collect()
```

## Assignment Patterns

### StructConstruction

Detects field-by-field struct construction in conjunctions.

**Spec Pattern:**
```rust
s_.field1 == value1 &&& s_.field2 == value2 &&& s_.field3 == value3
```

**Generated Code:**
```rust
SType {
    field1: value1,
    field2: value2,
    field3: value3,
}
```

### SimpleAssignment (Copy)

Direct assignment of one value to another.

**Spec Pattern:**
```rust
s_ == expr
```

**Generated Code:**
```rust
expr.clone()
```

### Identity Copy

When output equals input directly.

**Spec Pattern:**
```rust
s_ == s
```

**Generated Code:**
```rust
s.clone()
```

### Struct Update

Partial modification of a struct.

**Spec Pattern:**
```rust
s_.field1 == new_value &&& s_.field2 == s.field2 &&& ...
```

**Generated Code:**
```rust
SType {
    field1: new_value,
    ..s.clone()
}
```

## Conditional Patterns

### If-Then-Else

**Spec Pattern:**
```rust
if condition {
    s_.field == value_a
} else {
    s_.field == value_b
}
```

**Generated Code:**
```rust
if condition {
    SType { field: value_a, ..s.clone() }
} else {
    SType { field: value_b, ..s.clone() }
}
```

### Conditional with Identity

**Spec Pattern:**
```rust
if condition {
    s_.field == new_value &&& s_.other == s.other
} else {
    s_ == s
}
```

**Generated Code:**
```rust
if condition {
    SType { field: new_value, ..s.clone() }
} else {
    s.clone()
}
```

## Collection Operations

### Empty Sequence

**Spec:** `sent_packets == Seq::empty()`
**Exec:** `vec![]`

### Singleton Sequence

**Spec:** `sent_packets == seq![packet]`
**Exec:** `vec![packet]`

### Sequence Length

**Spec:** `seq.len()`
**Exec:** `vec.len()`

### Sequence Index

**Spec:** `seq[i]`
**Exec:** `vec[i as usize]` (with bounds checking)

## View Operator

The view operator `@` is used to convert exec types to spec types for verification.

**In ensures:**
```rust
ensures
    result.0.well_formed(),
    LAcceptorProcess1a(s@, result.0@, inp@, result.1@),
```

**Generated call:**
```rust
// s@ becomes the ghost/spec view of s
// Used only in proof context, not in executable code
```

## Unsupported Patterns

The transpiler will report an error for patterns it cannot handle:

1. **Complex quantifiers with multiple variables:**
   ```rust
   forall |i: int, j: int| 0 <= i < j < n ==> ...
   ```

2. **Existential quantifiers:**
   ```rust
   exists |i: int| 0 <= i < n ==> ...
   ```

3. **Recursive predicates**

4. **Non-deterministic assignments**

## Listing Templates

To see all supported templates:
```bash
verus-transpile list-templates
```
