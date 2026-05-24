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

## Arc-Wrapping for O(1) Clone (Phase 40)

The transpiler can wrap non-scalar struct fields in `Arc<T>` so that cloning
the struct is O(1) (refcount increment) instead of O(n) (deep copy). This
eliminates the major performance bottleneck of spec→exec translation where
every state transition clones the full state.

### Configuration

In the protocol's `_transpile.toml`:

```toml
# Structs whose non-scalar fields should be Arc-wrapped
arc_wrap_types = ["CState"]

# Fine-grained: only wrap specific fields (overrides arc_wrap_types)
[arc_wrap_fields]
CState = ["votes_granted", "match_index", "next_index"]
```

**`arc_wrap_types`** wraps ALL non-scalar fields of the listed structs.
**`arc_wrap_fields`** gives fine-grained control — only listed fields are
wrapped. When both are specified, `arc_wrap_fields` takes precedence for
structs that appear in both.

### What changes

| Without Arc | With Arc |
|-------------|----------|
| `pub field: Vec<T>` | `pub field: Arc<Vec<T>>` |
| `field: v.clone()` (deep copy) | `field: v.clone()` (Arc refcount bump) |
| `field: HashSet::new()` | `field: Arc::new(HashSet::new())` |
| `CState { field: x, ..s.clone() }` | `CState { field: Arc::new(x), ..s.clone() }` |

### Struct update syntax

When a function modifies only a few fields via `CState { field: val, ..s.clone() }`,
unchanged Arc-wrapped fields get `Arc::clone` (O(1)), and only explicitly set
Arc-wrapped fields get `Arc::new(value)`.

### Limitations

- **Vec indexing**: Verus does not support `[]` indexing on `Arc<Vec<T>>`.
  If a field is indexed in exec code, exclude it from `arc_wrap_fields`.
  The `log` field in Raft is an example — it must remain `Vec<CLogEntry>`.
- **Struct match patterns**: The transpiler appends `..` to struct patterns
  in match arms to handle partial field binding gracefully.
- **Helper call field access**: Expressions like `Chelper(&s).field` where
  `field` is Arc-wrapped are NOT double-wrapped — the transpiler detects
  this pattern and skips the outer `Arc::new`.

### Performance impact

**Note**: Struct-level Arc wrapping (Phase 40) showed **no measured benefit** on
re-bench (Raft: 3,613 vs 3,612 ops/s, within noise). The original "+12%" claim
was trial-1 variance. See EFFICIENT_EMIT.md for details.

## Field-Level Arc-Wrapping for Collection Fields (Phase 41)

The **effective** Arc-wrapping strategy wraps individual collection fields
(`HashMap`, `HashSet`, `Vec`) inside sub-component structs. This targets the
actual hot spots: large collections that are cloned O(n) on every dispatch but
change only on specific code paths.

### Configuration

In the protocol's `_transpile.toml`, use `arc_wrap_fields` with inline table syntax:

```toml
arc_wrap_fields = { CProposer = ["highest_seqno_requested_by_client_this_view", "request_queue", "received_1b_packets"] }
```

### What changes

| Without Arc | With Arc |
|-------------|----------|
| `pub field: HashMap<K, V>` | `pub field: Arc<HashMap<K, V>>` |
| `let mut f = clone_map(&s.field);` | `let mut f = clone_map(&s.field);` (auto-deref) |
| `SType { field: new_map, .. }` | `SType { field: Arc::new(new_map), .. }` |
| `proof fn lemma(m: MapType)` | `proof fn lemma(m: &MapType)` |
| `lemma(s.field)` | `lemma(&s.field)` |

### Proof lemma signatures

When a field is Arc-wrapped, proof lemmas that take the field's type as a parameter
must use `&T` instead of `T` so that Rust's auto-deref from `&Arc<T>` to `&T` works
at call sites. The transpiler handles this automatically:

```rust
// Generated for Arc-wrapped CLearnerState field:
proof fn lemma_abstractify_empty_clearnerstate(m: &CLearnerState)  // &T, not T
proof fn lemma_abstractify_clearnerstate_insert(
    old_m: &CLearnerState,    // &T for auto-deref from &Arc<T>
    m2: &CLearnerState,
    k: COperationNumber,
    v: CLearnerTuple,
)

// Call site in generated exec function:
proof {
    lemma_abstractify_clearnerstate_remove(
        &s.unexecuted_learner_state,      // &Arc<T> auto-derefs to &T
        &result.unexecuted_learner_state,
        (*opn)
    )
}
```

### Spec helper signatures

Hand-written spec helpers (`_is_valid`, `_is_abstractable`, `abstractify_*`) must
also take `&T` instead of `T` for auto-deref to work:

```rust
// In types_i.rs:
pub open spec fn clearnerstate_is_valid(m: &CLearnerState) -> bool { ... }
pub open spec fn abstractify_clearnerstate(m: &CLearnerState) -> LearnerState { ... }
```

### Hand-written struct support

Each Arc-wrapped field requires coordinated changes in `*Impl.rs`:

```rust
use std::sync::Arc;

pub struct CLearner {
    pub constants: CReplicaConstants,
    pub unexecuted_learner_state: Arc<CLearnerState>,  // Arc-wrapped
}

impl CLearner {
    pub fn clone_up_to_view(&self) -> Self {
        CLearner {
            constants: self.constants.clone(),
            unexecuted_learner_state: clone_arc_learner_state(&self.unexecuted_learner_state),
        }
    }
}

// Arc-backed shallow clone helper
#[verifier::external_body]
pub fn clone_arc_learner_state(v: &Arc<CLearnerState>) -> (res: Arc<CLearnerState>)
    ensures res@ == v@,
{ Arc::clone(v) }
```

### Performance impact

Measured on RSL (zoo-002, 32 threads x 30s x 2 trials, 5 Arc-wrapped fields):
- Pre-Arc baseline: 16,341 ops/s, 2.39 ms latency, 36% decay
- Post-Arc (5 fields): **32,663 ops/s avg**, 1.12 ms latency, 5% decay
- Improvement: **+100% throughput** (2x), latency halved
- Exceeds wasiq hand-tuned reference (28,449) by 14.8%

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
