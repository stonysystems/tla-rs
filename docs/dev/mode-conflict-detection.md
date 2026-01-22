# Mode Conflict Detection Plan

## Overview

Mode conflict detection identifies three categories of issues during expression analysis:
1. Output variable used before assignment
2. Input variable being assigned
3. Conflicting assignments in branches

## Conflict Types

### 1. Use-Before-Assignment

When an output parameter is referenced (read) before it's been assigned:

```rust
// Invalid: s_ used before assignment
&&& packets == make_packet(s_)  // s_ read here
&&& s_ == compute_new_state()   // s_ assigned here
```

Detection: Track which output variables have been assigned so far during left-to-right analysis.

### 2. Input Assignment

When an input parameter appears on the left side of an equality (being assigned):

```rust
// Invalid: s is input, cannot be assigned
&&& s.max_bal == new_bal  // Error: assigning to input 's'
```

Detection: When extracting output paths, if we find an input variable, report it.

### 3. Branch Conflict

When different branches assign different outputs or same outputs inconsistently:

```rust
// Invalid: different outputs in each branch
if cond {
    &&& s_ == state1      // assigns s_
} else {
    &&& packets == seq![] // assigns packets, missing s_
}
```

Detection: After analyzing both branches, verify they assign the same set of outputs.

## Implementation

Add to ModeAnalyzer:
- `input_params: HashSet<String>` to track inputs
- `assigned_before_use: Vec<ModeConflict>` to collect errors
- Helper method `check_read_before_write()`

```rust
#[derive(Debug, Clone)]
pub enum ModeConflict {
    UseBeforeAssignment {
        var: String,
        used_at: Option<Span>,
        context: String,
    },
    InputAssignment {
        var: String,
        assigned_at: Option<Span>,
    },
    BranchMismatch {
        branch1_assigns: HashSet<String>,
        branch2_assigns: HashSet<String>,
    },
}
```
