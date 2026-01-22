# Template Matching for Collection Operations

## Overview

Implement pattern matching to recognize quantifier expressions that correspond to known collection comprehension patterns. This enables code generation for sequences, sets, and maps.

## Patterns to Match

### 1. Sequence Comprehension

**Spec pattern:**
```rust
forall |i: int| 0 <= i < n ==> seq[i] == f(i)
```

**Matches:**
- Forall with single integer index variable
- Body is implication
- LHS of implication: bounds check `0 <= i < n`
- RHS of implication: `seq[i] == expr(i)` or `expr(i) == seq[i]`

**Exec generation:**
```rust
(0..n).map(|i| f(i)).collect()
```

### 2. Map Comprehension (Domain + Value)

**Spec patterns:**
```rust
// Domain constraint
forall |k| k in map' <==> k in source && pred(k)
// or just:
forall |k| k in map' <==> pred(k)

// Value constraint
forall |k| k in map' ==> map'[k] == f(k)
```

**Matches domain:**
- Forall with single key variable
- Body is biconditional (`<==>`)
- LHS: `k in map'` (membership check)
- RHS: predicate over k

**Matches value:**
- Forall with single key variable
- Body is implication
- LHS: `k in map'`
- RHS: `map'[k] == expr(k)`

### 3. Set Comprehension

**Spec pattern:**
```rust
forall |x| x in set' <==> pred(x)
```

**Matches:**
- Forall with single element variable
- Body is biconditional
- LHS: `x in set'`
- RHS: predicate

## Implementation Structure

```rust
pub struct TemplateMatcher;

impl TemplateMatcher {
    /// Main entry point - try all templates
    pub fn match_template(expr: &Expr) -> Option<QuantifierTemplate> {
        if let Expr::Forall { vars, body, .. } = expr {
            if vars.len() == 1 {
                let var = &vars[0];
                // Try each pattern
                if let Some(t) = Self::try_seq_comprehension(var, body) {
                    return Some(t);
                }
                if let Some(t) = Self::try_map_comprehension(var, body) {
                    return Some(t);
                }
                if let Some(t) = Self::try_set_comprehension(var, body) {
                    return Some(t);
                }
            }
        }
        None
    }

    fn try_seq_comprehension(var: &Binding, body: &Expr) -> Option<QuantifierTemplate>;
    fn try_map_comprehension(var: &Binding, body: &Expr) -> Option<QuantifierTemplate>;
    fn try_set_comprehension(var: &Binding, body: &Expr) -> Option<QuantifierTemplate>;
}
```

## Helper Functions

```rust
/// Extract bounds from `0 <= i < n` pattern
fn extract_int_bounds(expr: &Expr, var_name: &str) -> Option<(Expr, Expr)>;

/// Check if expr is `x in collection`
fn is_membership_check(expr: &Expr, var_name: &str) -> Option<&Expr>;

/// Check if expr is `collection[x]`
fn is_index_access(expr: &Expr, collection: &str, var_name: &str) -> bool;

/// Check if expr is `collection[x] == value` or `value == collection[x]`
fn extract_indexed_assignment(expr: &Expr, collection: &str, var_name: &str) -> Option<&Expr>;
```

## Error Reporting

Add `TemplateMatchError` variants for:
- Unrecognized quantifier pattern
- Multiple variables (not single)
- Missing bounds
- Incompatible body structure

## Test Cases

1. Simple seq comprehension: `forall |i| 0 <= i < 5 ==> result[i] == i * 2`
2. Seq from source: `forall |i| 0 <= i < src.len() ==> result[i] == src[i] + 1`
3. Map domain filter: `forall |k| k in result <==> k in src && k > 0`
4. Map value transform: `forall |k| k in result ==> result[k] == src[k] * 2`
5. Set comprehension: `forall |x| x in result <==> x > 0 && x < 10`
6. Negative cases: patterns that don't match

## Estimated LOC

- Template matcher implementation: ~200 LOC
- Helper functions: ~100 LOC
- Error reporting: ~50 LOC
- Tests: ~150 LOC
- Total: ~500 LOC
