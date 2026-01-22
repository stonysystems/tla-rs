# Expression Mode Analysis Plan

## Overview

The expression analyzer traverses spec function bodies to determine which output variables
are assigned and how. This is crucial for:
1. Populating the `AssignmentTracker` with assigned paths
2. Detecting mode conflicts (using outputs before assignment)
3. Enabling the saturation/harmony/obligation validation checks

## Key Patterns to Handle

### 1. Equality Assignments

In spec predicates, equality (`==`) is used to define output values:
```rust
s_.max_bal == new_bal
```

The analyzer must determine which side is the "output" (assignment target) and which
is the "expression" (value being assigned).

Rules:
- If left side starts with an output parameter name, it's an assignment to that output
- If right side is an output parameter, swap and treat left as value

### 2. Struct Field Assignments

Track field assignments on outputs:
```rust
s_.max_bal == bal
s_.votes == s.votes
```

Should record:
- `s_` → `MemberPath::Field(Root, "max_bal")`
- `s_` → `MemberPath::Field(Root, "votes")`

### 3. Whole Variable Assignments

When the output is assigned as a whole:
```rust
s_ == s
```

Records:
- `s_` → `MemberPath::Root`

### 4. Conditional Branches

Both branches of if/else must assign the same outputs:
```rust
if cond {
    &&& s_ == new_state
    &&& packets == new_packets
} else {
    &&& s_ == s
    &&& packets == Seq::empty()
}
```

### 5. Conjunction Chains (`&&&`)

Each clause may contain an assignment:
```rust
&&& s_.max_bal == bal
&&& s_.votes == s.votes
&&& sent_packets == seq![make_reply(s)]
```

## Implementation

```rust
impl ModeAnalyzer {
    pub fn analyze_expression(
        &mut self,
        expr: &Expr,
        tracker: &mut AssignmentTracker,
        output_params: &HashSet<String>,
    ) {
        match expr {
            Expr::Conjunction(clauses) => {
                for clause in clauses {
                    self.analyze_expression(clause, tracker, output_params);
                }
            }
            Expr::Eq(left, right) => {
                self.analyze_equality(left, right, tracker, output_params);
            }
            Expr::If { then_, else_, .. } => {
                // Analyze both branches
                self.analyze_expression(then_, tracker, output_params);
                if let Some(else_expr) = else_ {
                    self.analyze_expression(else_expr, tracker, output_params);
                }
            }
            // ... other cases
            _ => {}
        }
    }

    fn analyze_equality(
        &mut self,
        left: &Expr,
        right: &Expr,
        tracker: &mut AssignmentTracker,
        output_params: &HashSet<String>,
    ) {
        // Check if left is an output path
        if let Some((var, path)) = self.extract_output_path(left, output_params) {
            tracker.record_assignment(&var, path);
        } else if let Some((var, path)) = self.extract_output_path(right, output_params) {
            // Output on right side (less common but valid)
            tracker.record_assignment(&var, path);
        }
    }

    fn extract_output_path(
        &self,
        expr: &Expr,
        output_params: &HashSet<String>,
    ) -> Option<(String, MemberPath)> {
        match expr {
            Expr::Ident(name) if output_params.contains(name) => {
                Some((name.clone(), MemberPath::Root))
            }
            Expr::Field(base, field) => {
                if let Some((var, path)) = self.extract_output_path(base, output_params) {
                    Some((var, path.field(field.clone())))
                } else {
                    None
                }
            }
            _ => None
        }
    }
}
```
