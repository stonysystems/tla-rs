# Supported Patterns and Templates

The transpiler recognizes specific patterns in spec function bodies and generates corresponding exec code. This document describes the supported patterns.

## Assignment Patterns

### Simple Assignment

**Spec Pattern:**
```rust
s_ == expr
```

**Generated Code:**
```rust
expr.clone()
```

### Copy (Identity)

**Spec Pattern:**
```rust
s_ == s
```

**Generated Code:**
```rust
s.clone()
```

### Field Assignment

**Spec Pattern:**
```rust
s_.field1 == expr1
&&& s_.field2 == expr2
```

**Generated Code:**
```rust
Struct {
    field1: expr1_impl,
    field2: expr2_impl,
}
```

### Struct Update

**Spec Pattern:**
```rust
s_.field == expr &&& /* other fields same as input */
```

**Generated Code:**
```rust
Struct {
    field: expr_impl,
    ..s.clone()
}
```

## Conditional Patterns

### If-Then-Else

**Spec Pattern:**
```rust
if cond {
    s_ == value_a
} else {
    s_ == value_b
}
```

**Generated Code:**
```rust
if cond_impl {
    value_a_impl
} else {
    value_b_impl
}
```

### Conditional with Copy

**Spec Pattern:**
```rust
if cond {
    s_.field == new_value
    &&& s_.other == s.other
} else {
    s_ == s
}
```

**Generated Code:**
```rust
if cond_impl {
    Struct { field: new_value_impl, ..s.clone() }
} else {
    s.clone()
}
```

## Quantifier Templates

### Sequence Comprehension

**Spec Pattern:**
```rust
forall |i: int| 0 <= i < len ==> seq[i] == f(i)
```

**Generated Code:**
```rust
(0..len).map(|i| f_impl(i)).collect::<Vec<_>>()
```

### Map Value Comprehension

**Spec Pattern:**
```rust
forall |k| k in domain ==> map[k] == f(k)
```

**Generated Code:**
```rust
domain.iter()
    .map(|k| (k.clone(), f_impl(k)))
    .collect::<HashMap<_, _>>()
```

### Set Comprehension

**Spec Pattern:**
```rust
forall |x| x in set <==> predicate(x)
```

**Generated Code:**
```rust
source.iter()
    .filter(|x| predicate_impl(x))
    .cloned()
    .collect::<HashSet<_>>()
```

## Expression Transformations

### View Operator

**Spec:** `expr@` (view/abstraction)
**Exec:** `expr.view()` or removed in spec context

### Arrow Operator

**Spec:** `packet.msg->bal_1a` (enum variant field access)
**Exec:** `packet.msg.get_bal_1a()` (generated getter)

### Method Calls

**Spec:** `seq.len()`, `map.contains_key(k)`
**Exec:** Same method calls on exec types

### Literals

| Spec | Exec |
|------|------|
| `Seq::empty()` | `Vec::new()` |
| `Set::empty()` | `HashSet::new()` |
| `Map::empty()` | `HashMap::new()` |
| `seq![a, b, c]` | `vec![a, b, c]` |

## Type Translations

| Spec Type | Exec Type |
|-----------|-----------|
| `int` | `i64` |
| `nat` | `u64` |
| `bool` | `bool` |
| `Seq<T>` | `Vec<T>` |
| `Set<T>` | `HashSet<T>` |
| `Map<K, V>` | `HashMap<K, V>` |
| `Option<T>` | `Option<T>` |
| `LAcceptor` | `CAcceptor` |

## Limitations

1. **Nested Quantifiers**: Not supported - flatten to single quantifier
2. **Complex Predicates**: May not match known templates
3. **Recursive Definitions**: Limited support
4. **Arbitrary Arithmetic**: May need explicit bounds

## Tips for Writing Transpilable Specs

1. Structure output assignments as conjunctions of field assignments
2. Use recognizable quantifier patterns for collections
3. Ensure all branches assign the same output fields
4. Avoid using output parameters before they are assigned
5. Keep quantifier bodies simple and recognizable
