# Translation Rules for Verus Spec-to-Exec Transpiler

Based on manual corrections in `election_gen.rs`, this document summarizes the translation rules needed for generating correct executable code.

## 1. Type Mappings

### Basic Types
- `int` → `u64` (for indices, counts) or `i64` (for general integers)
- `bool` → `bool` (no change)
- `nat` → `u64`

### Collection Types
- `Seq<T>` → `Vec<T>`
- `Set<int>` → `HashSet<u64>` (requires casting in view)
- `Set<T>` → `HashSet<T>` (for non-primitive types)
- `Map<K,V>` → `HashMap<K,V>` (or BTreeMap)

### Custom Types
- `Ballot` → `CBallot`
- `Request` → `CRequest`
- `UpperBound` → `CUpperBound`
- `AbstractEndPoint` → `EndPoint`
- `LConfiguration` → `CConfiguration`
- Pattern: `L*` → `C*` (spec prefix to exec prefix)

## 2. View Function Generation

### For Struct with Collections
```rust
impl View for CElectionState {
    type V = ElectionState;

    open spec fn view(&self) -> ElectionState {
        ElectionState {
            // Simple types: cast to int
            epoch_end_time: self.epoch_end_time as int,

            // Vec<CRequest>: map each element's view
            requests_received_this_epoch: self.requests_received_this_epoch@.map(|i, r:CRequest| r@),

            // HashSet<u64>: map and cast
            current_view_suspectors: self.current_view_suspectors@.map(|x:u64| x as int),

            // Nested types: use their view
            constants: self.constants@,
        }
    }
}
```

### Rules:
- **Vec<T> where T: View**: `vec@.map(|i, elem: T| elem@)`
- **HashSet<u64>**: `set@.map(|x: u64| x as int)`
- **Primitive numeric types**: `value as int`
- **Struct types with View trait**: `struct_field@`

## 3. Valid Predicates

### For Structs with Collections
```rust
impl CElectionState {
    pub open spec fn valid(&self) -> bool {
        // Nested structs
        &&& self.constants.valid()
        &&& self.current_view.valid()

        // Vectors: forall items valid
        &&& (forall |i:int| 0 <= i < self.requests_received_this_epoch@.len()
            ==> self.requests_received_this_epoch@[i].valid())

        // HashSet/HashMap: usually no validity check needed
    }
}
```

### Rules:
- For **Vec<T>** fields: Add `forall |i:int| 0 <= i < vec@.len() ==> vec@[i].valid()`
- For **nested struct** fields: Add `field.valid()`
- For **primitive** fields: Usually no check needed
- Skip validity for **HashSet<primitive>** (like `HashSet<u64>`)

## 4. Function Parameter Requires Clauses

### For Vector Parameters
```rust
pub exec fn CBoundRequestSequence(s: &Vec<CRequest>, lengthBound: &CUpperBound) -> (result: Vec<CRequest>)
requires
    // Each element must be valid
    forall |i: int| 0 <= i < s@.len() ==> s@[i].valid(),
    lengthBound.valid(),
ensures
    // Result elements valid
    forall |i: int| 0 <= i < result@.len() ==> result@[i].valid(),
    // Spec linkage with mapped views
    result@.map(|i, r: CRequest| r@) == BoundRequestSequence(s@.map(|i, r: CRequest| r@), lengthBound@),
{
    // ...
}
```

### Rules:
- **Vector parameters**: Add `forall |i: int| 0 <= i < param@.len() ==> param@[i].valid()`
- **Vector return values**: Same forall check in ensures
- **Spec linkage for vectors**: Use `.map(|i, elem: T| elem@)` on both sides

## 5. Enum Pattern Matching

### Spec Code with `is` operator
```rust
if lengthBound is UpperBoundFinite && 0 <= lengthBound->n < s.len() {
    s.subrange(0, lengthBound->n)
} else {
    s
}
```

### Generated Exec Code - Need Match
```rust
match lengthBound {
    CUpperBound::CUpperBoundFinite { n } => {
        if 0 <= *n && (*n as usize) < s.len() {
            // construct new vec
            let mut result = Vec::new();
            let mut i = 0;
            while i < *n as usize {
                result.push(s[i].clone());
                i += 1;
            }
            result
        } else {
            s.clone()
        }
    }
    CUpperBound::CUpperBoundInfinite => s.clone(),
}
```

### Rules:
- **`enum_val is Variant`** → `match enum_val { Variant { fields } => ... }`
- **`enum_val->field`** → Access `field` directly in match arm
- Cannot use `is` operator in exec code - must use match
- Enum field access requires pattern matching

## 6. EndPoint Comparisons

### Spec Code
```rust
r1.client == r2.client
```

### Generated Exec Code
```rust
do_end_points_match(&r1.client, &r2.client)
```

### Rules:
- **Never use `==` for EndPoint comparison** in exec code
- Always use `do_end_points_match(&ep1, &ep2)`
- Import: `use crate::common::collections::seq_is_unique_v::do_end_points_match;`

## 7. Type Refinement Checks (Remove in Exec)

### Spec Code
```rust
r1 is Request && r2 is Request && r1.client == r2.client && r1.seqno == r2.seqno
```

### Generated Exec Code
```rust
// Remove "r1 is Request" checks - always true in exec with typed parameters
do_end_points_match(&r1.client, &r2.client) && r1.seqno == r2.seqno
```

### Rules:
- **Remove all `expr is Type` checks** in exec code
- These are spec-level refinement types, not needed in strongly-typed exec code
- Parameters already have concrete types (CRequest, not Request?)

## 8. Vector Operations

### Spec: Subrange
```rust
s.subrange(0, n)
```

### Exec: While Loop
```rust
let mut result = Vec::new();
let mut i = 0;
while i < n
    invariant
        0 <= i <= n,
        i <= s@.len(),
        result@.len() == i,
        forall |j: int| 0 <= j < i ==> result@[j] == s@[j],
{
    result.push(s[i].clone());
    i += 1;
}
result
```

### Spec: Concatenation
```rust
v1 + v2
```

### Exec: Clone and Extend
```rust
let mut result = v1.clone();
result.extend(v2.iter().cloned());
result
```

### Spec: Empty Sequence
```rust
Seq::empty()
```

### Exec: Empty Vector
```rust
vec![]
// or
Vec::new()
```

### Rules:
- **No `.subrange()` in exec** - use while loop with invariants
- **No `+` operator for vectors** - use `.extend()` or loops
- **Pass vectors by value or explicitly clone** when returning
- Consider whether to take `&Vec<T>` or `Vec<T>` based on whether cloning is needed

## 9. Integer Conversions and Casts

### Length Comparisons
```rust
// Spec: b.proposer_id + 1 < c.config.replica_ids.len()
// Exec: need to cast len() to u64
(b.proposer_id + 1) < c.config.replica_ids.len() as u64
```

### View Conversions
```rust
// int fields become u64/i64, need to cast in view
epoch_end_time: self.epoch_end_time as int,
```

### Rules:
- **Always cast `.len()` to `u64`** when comparing with u64 variables
- **Cast numeric types to `int`** in view functions: `value as int`
- Watch for potential overflow in arithmetic operations
- Consider using checked arithmetic for safety

## 10. Quantifiers (Spec Only, Not in Exec)

Quantifiers (`forall`, `exists`) remain in spec code (requires, ensures, invariants) and are not translated to exec code bodies.

### In Spec (Predicate Body)
```rust
exists |earlier_req: Request| es.requests_received_this_epoch.contains(earlier_req)
    && RequestsMatch(earlier_req, req)
```

### In Exec (Function Body)
```rust
let mut found = false;
let mut i = 0;
while i < es.requests_received_this_epoch.len()
    invariant
        found ==> exists |j: int| 0 <= j < i && CRequestsMatch(&es.requests_received_this_epoch[j], req),
{
    if CRequestsMatch(&es.requests_received_this_epoch[i], req) {
        found = true;
        break;
    }
    i += 1;
}
```

### Rules:
- **`exists` with contains**: Loop with early break when found
- **`forall` with predicate**: Loop checking all elements
- Quantifiers stay in invariants and ensures clauses
- Need to maintain loop invariants linking to quantifiers

## 11. Struct Construction from Field Updates

### All Fields Specified (Common)
```rust
CElectionState {
    constants: es.constants.clone(),
    current_view: new_view,
    current_view_suspectors: new_set,
    epoch_end_time: new_time,
    epoch_length: es.epoch_length,
    requests_received_this_epoch: vec![],
    requests_received_prev_epochs: es.requests_received_prev_epochs.clone(),
}
```

### Struct Update Syntax (Can't Use with Clone)
```rust
// Doesn't work well because of cloning requirements
// MyStruct { field1: new_val, ..old_struct }
// Better to list all fields explicitly
```

### Rules:
- **List all fields explicitly** in struct construction
- **Clone fields that aren't being updated**: `field: es.field.clone()`
- **New values without clone**: `field: new_value`
- Struct update syntax (`..*`) has issues with borrow checker in complex cases

## Summary of Major Issues to Fix in Transpiler

1. **Vector view functions**: Generate `.map(|i, elem: T| elem@)` for Vec<T>
2. **Vector valid predicates**: Generate forall checks for Vec<T> fields
3. **Enum matching**: Convert `is` operator to match statements
4. **EndPoint comparisons**: Use `do_end_points_match()` instead of `==`
5. **Remove type refinement**: Strip `expr is Type` checks in exec code
6. **Vector operations**: Generate while loops for subrange, extend for concatenation
7. **Integer casts**: Add `as u64` for `.len()` comparisons with u64
8. **Quantifier translation**: Generate loops for exists/forall in function bodies

## Next Steps

See `TODO.md` section "Phase 9: Fix Code Generation for Compilation" for implementation tasks.
