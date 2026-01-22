# Fix: Parser support for path syntax (`::`)

## Issue
The parser fails to parse expressions like `LState::default()` which use Rust's path syntax with `::` separators.

## Failing Tests
1. `test_parse_view_operator` - Contains `s@ == LState::default()`
2. `test_parse_spec_fn_with_forall` - Contains path expressions

## Root Cause
The `parse_primary_expr` method only parses single identifiers and doesn't handle path segments separated by `::`.

## Fix Approach

### 1. Modify `parse_primary_expr` to parse paths
After parsing an identifier, check if `::` follows and continue parsing path segments.

### 2. Handle path function calls
When a path like `LState::default` is followed by `()`, it should be parsed as a `Call` expression with a multi-segment path.

## Changes Required

In `src/parser/mod.rs`:

1. After parsing initial identifier (line ~767), check for `::` and parse additional segments
2. Update `parse_postfix_ops` to handle function calls on path expressions (not just single identifiers)

## Code Change

```rust
// In parse_primary_expr, replace lines 766-773:

// Parse identifier or path, then handle postfix operations
let ident = self.parse_identifier()?;
let mut path_segments = vec![ident];

// Check for path continuation (::)
while self.peek_str(2) == Some("::") {
    self.pos += 2; // consume ::
    self.skip_whitespace();
    let segment = self.parse_identifier()?;
    path_segments.push(segment);
}

let mut expr = if path_segments.len() == 1 {
    Expr::Ident(path_segments.into_iter().next().unwrap())
} else {
    // Multi-segment path - check for function call
    self.skip_whitespace();
    if self.peek() == Some('(') {
        self.advance();
        let args = self.parse_call_args()?;
        self.expect(')')?;
        Expr::Call {
            func: Path::new(path_segments),
            args,
        }
    } else {
        // Just a path reference (rare in expressions)
        Expr::Ident(path_segments.join("::"))
    }
};

// Handle postfix operations
expr = self.parse_postfix_ops(expr)?;
```

## Testing
After the fix, run:
```bash
cargo test test_parse_view_operator
cargo test test_parse_spec_fn_with_forall
```
