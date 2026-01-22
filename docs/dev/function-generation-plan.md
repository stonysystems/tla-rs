# Function Generation Plan (Section 6.2)

## Overview

Transform Verus spec predicates into executable functions. The spec predicate expresses constraints; the exec function computes values that satisfy those constraints.

## Key Transformations

### 1. Function Signature

**Input (spec):**
```rust
pub open spec fn LAcceptorProcess1a(
    s: LAcceptor,       // Input (+)
    s_: LAcceptor,      // Output (-)
    inp: RslPacket,     // Input (+)
    sent: Seq<RslPacket> // Output (-)
) -> bool
```

**Output (exec):**
```rust
pub exec fn CAcceptorProcess1a(
    s: &CAcceptor,
    inp: &CRslPacket,
) -> (CAcceptor, Vec<CRslPacket>)
    requires
        s.well_formed(),
        inp.well_formed(),
    ensures
        result.0.well_formed(),
        result.1.iter().all(|p| p.well_formed()),
        LAcceptorProcess1a(s@, result.0@, inp@, result.1@),
```

### 2. Expression Transformation

| Spec Pattern | Exec Generation |
|--------------|-----------------|
| `s_.field == expr` | `field_val = expr_impl;` |
| `s_ == s` | `s.clone()` |
| `s_ == s.(field := v)` | `Struct { field: v, ..s }` |
| `&&& e1 &&& e2 &&& e3` | Block with all assignments |
| `if c { e1 } else { e2 }` | `if c_impl { e1_impl } else { e2_impl }` |
| `forall |i| 0 <= i < n ==> ...` | Use template matching |

### 3. Expression Context

```rust
pub struct TransformContext {
    /// Output variables being constructed
    pub outputs: HashMap<String, OutputState>,
    /// Input variables (read-only)
    pub inputs: HashSet<String>,
    /// Type registry for lookups
    pub types: Arc<TypeRegistry>,
    /// Naming config
    pub config: NamingConfig,
}

pub struct OutputState {
    /// Type of the output
    pub ty: Type,
    /// Fields that have been assigned
    pub assigned_fields: HashMap<String, ExecExpr>,
}
```

### 4. Exec Expression AST

```rust
pub enum ExecExpr {
    /// Variable reference
    Ident(String),
    /// Literal value
    Literal(ExecLiteral),
    /// Field access: expr.field
    Field(Box<ExecExpr>, String),
    /// Method call: expr.method(args)
    MethodCall {
        receiver: Box<ExecExpr>,
        method: String,
        args: Vec<ExecExpr>,
    },
    /// Function call
    Call {
        func: String,
        args: Vec<ExecExpr>,
    },
    /// Struct construction
    Struct {
        name: String,
        fields: Vec<(String, ExecExpr)>,
    },
    /// Conditional
    If {
        cond: Box<ExecExpr>,
        then_branch: Box<ExecExpr>,
        else_branch: Option<Box<ExecExpr>>,
    },
    /// Let binding
    Let {
        name: String,
        value: Box<ExecExpr>,
        body: Box<ExecExpr>,
    },
    /// Clone call
    Clone(Box<ExecExpr>),
    /// Block of statements
    Block(Vec<ExecExpr>),
    /// Binary operation
    Binary(Box<ExecExpr>, BinOp, Box<ExecExpr>),
    /// Index: expr[idx]
    Index(Box<ExecExpr>, Box<ExecExpr>),
    /// Vec construction from iter
    VecFromIter {
        len: Box<ExecExpr>,
        element: Box<ExecExpr>,
        index_var: String,
    },
}
```

## Implementation Steps

1. **ExecExpr and TransformContext types** (~100 LOC)
   - Define exec expression AST
   - Define transform context

2. **Basic transform_expr** (~150 LOC)
   - Handle Ident, Literal, Field
   - Handle Binary operations
   - Handle MethodCall

3. **Assignment detection** (~100 LOC)
   - Detect `output.field == expr` patterns
   - Track assigned fields in context
   - Handle `output == input` copy

4. **Conjunction handling** (~50 LOC)
   - Collect assignments from all conjuncts
   - Build struct from collected fields

5. **Conditional handling** (~50 LOC)
   - Transform condition
   - Transform both branches
   - Verify branch compatibility

6. **Struct construction** (~100 LOC)
   - Collect all field assignments
   - Generate struct literal
   - Handle unchanged fields (clone from input)

7. **ExecExpr to code** (~100 LOC)
   - Printer for ExecExpr -> Rust code

8. **Tests** (~150 LOC)
   - Simple assignment
   - Field-wise construction
   - Conditional branches
   - Clone patterns

## Estimated Total: ~800 LOC

Breaking this down further:
- Part 1: ExecExpr types and TransformContext (~150 LOC)
- Part 2: Basic expression transformer (~200 LOC)
- Part 3: Assignment and struct construction (~200 LOC)
- Part 4: Printer and function wrapper (~150 LOC)
- Part 5: Tests (~150 LOC)

Since this is ~500 LOC for core implementation, we can do it in one task.
