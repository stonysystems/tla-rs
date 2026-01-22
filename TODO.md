# TODO: Verus Spec-to-Implementation Transpiler

A comprehensive plan to implement a transpiler that converts Rust/Verus TLA-style specifications into verified executable implementations.

## Reference

This plan is based on [AutoMan](https://github.com/stonysystems/automan), which performs similar transformations for Dafny. Our transpiler adapts these concepts for Rust/Verus.

---

## Table of Contents

1. [Overview](#1-overview)
2. [Phase 1: Foundation](#2-phase-1-foundation)
3. [Phase 2: Parser & AST](#3-phase-2-parser--ast)
4. [Phase 3: Mode Analysis](#4-phase-3-mode-analysis)
5. [Phase 4: Validation](#5-phase-4-validation)
6. [Phase 5: Code Generation](#6-phase-5-code-generation)
7. [Phase 6: Runtime Support](#7-phase-6-runtime-support)
8. [Phase 7: Testing & Validation](#8-phase-7-testing--validation)
9. [Phase 8: Integration & Tooling](#9-phase-8-integration--tooling)
10. [Milestones](#10-milestones)

---

## 1. Overview

### 1.1 Goal

Transform Verus `spec fn` predicates (TLA-style Init/Next specifications) into verified `exec fn` implementations that:
- Are executable Rust code
- Maintain proof linkage to original specifications
- Generate abstraction functions connecting spec and exec layers

### 1.2 Transformation Example

**Input (spec):**
```rust
verus! {
    pub open spec fn LAcceptorProcess1a(
        s: LAcceptor,
        s_: LAcceptor,
        inp: RslPacket,
        sent_packets: Seq<RslPacket>
    ) -> bool {
        let bal = inp.msg->bal_1a;
        if BalLt(s.max_bal, bal) {
            &&& s_.max_bal == bal
            &&& s_.votes == s.votes
            &&& sent_packets == seq![make_1b_reply(s, bal, inp.src)]
        } else {
            &&& s_ == s
            &&& sent_packets == Seq::empty()
        }
    }
}
```

**Output (exec):**
```rust
verus! {
    pub exec fn CAcceptorProcess1a(
        s: &CAcceptor,
        inp: &CRslPacket,
    ) -> (result: (CAcceptor, Vec<CRslPacket>))
        requires
            s.well_formed(),
            inp.well_formed(),
            inp.msg is CRslMessage1a,
        ensures
            result.0.well_formed(),
            LAcceptorProcess1a(s@, result.0@, inp@, result.1@),
    {
        let bal = inp.msg.get_bal_1a();
        if ballot_lt(&s.max_bal, &bal) {
            let s_ = CAcceptor {
                max_bal: bal.clone(),
                votes: s.votes.clone(),
                ..s.clone()
            };
            let packets = vec![make_1b_reply_impl(s, &bal, &inp.src)];
            (s_, packets)
        } else {
            (s.clone(), vec![])
        }
    }
}
```

### 1.3 Architecture Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                        Transpiler Pipeline                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  .rs (Verus spec)  +  .automan (mode annotations)               │
│         │                      │                                │
│         ▼                      ▼                                │
│  ┌─────────────┐        ┌─────────────┐                        │
│  │   Parser    │        │  Annotation │                        │
│  │  (syn-based)│        │   Parser    │                        │
│  └──────┬──────┘        └──────┬──────┘                        │
│         │                      │                                │
│         ▼                      ▼                                │
│  ┌─────────────────────────────────────┐                       │
│  │         Annotated AST               │                       │
│  │   (spec fns with mode metadata)     │                       │
│  └──────────────┬──────────────────────┘                       │
│                 │                                               │
│                 ▼                                               │
│  ┌─────────────────────────────────────┐                       │
│  │         Mode Analyzer               │                       │
│  │   - Input/Output classification     │                       │
│  │   - Dependency analysis             │                       │
│  └──────────────┬──────────────────────┘                       │
│                 │                                               │
│                 ▼                                               │
│  ┌─────────────────────────────────────┐                       │
│  │         Validator                   │                       │
│  │   - Saturation check                │                       │
│  │   - Harmony check                   │                       │
│  │   - Obligation check                │                       │
│  └──────────────┬──────────────────────┘                       │
│                 │                                               │
│                 ▼                                               │
│  ┌─────────────────────────────────────┐                       │
│  │         Code Generator              │                       │
│  │   - Exec fn generation              │                       │
│  │   - Abstraction functions           │                       │
│  │   - Proof linkage (ensures)         │                       │
│  └──────────────┬──────────────────────┘                       │
│                 │                                               │
│                 ▼                                               │
│         .rs (Verus exec + proofs)                              │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 2. Phase 1: Foundation

### 2.1 Project Setup

- [x] **Create transpiler crate structure** [26:01:22, 14:48]
  ```
  transpiler/
  ├── Cargo.toml
  ├── src/
  │   ├── lib.rs
  │   ├── main.rs           # CLI entry point
  │   ├── parser/           # Verus parsing
  │   ├── ast/              # AST definitions
  │   ├── annotation/       # Mode annotation handling
  │   ├── moder/            # Mode analysis
  │   ├── checker/          # Validation passes
  │   ├── translator/       # Code generation
  │   ├── printer/          # Output formatting
  │   └── error.rs          # Error types
  └── tests/
  ```

- [x] **Define dependencies** [26:01:22, 14:48]
  - `syn` + `quote` + `proc-macro2` for Rust parsing
  - `proc-macro2` for token manipulation
  - `serde` + `serde_json` for configuration
  - `clap` for CLI
  - `miette` for error reporting

- [x] **Design error handling strategy** [26:01:22, 14:48]
  - Span-aware errors pointing to source locations
  - Multiple error accumulation (don't stop at first error)
  - Warning vs error distinction

### 2.2 Configuration System

- [x] **Define configuration file format** (JSON/TOML) [26:01:22, 15:01] (see config.rs)
  ```toml
  [naming]
  spec_prefix = "L"
  exec_prefix = "C"

  [remapping]
  "LAcceptor" = "CAcceptor"
  "Ballot" = "CBallot"

  [output]
  generate_abstraction_fns = true
  generate_validity_predicates = true
  ```
  Implemented in `transpiler/src/config.rs` with serde TOML support.
  Added `NamingConfig`, `OutputConfig`, `ModuleConfig` with sensible defaults.

- [x] **Define mode annotation format** (`.automan` file) [26:01:22, 15:21] (see annotation/mod.rs)
  ```
  module RSL::Acceptor {
      LAcceptorInit(-, +);           // (out, in) - a is output, c is input
      LAcceptorProcess1a(+, -, +, -); // (in, out, in, out)
      LAcceptorProcess2a(+, -, +, -);
  }
  ```
  Implemented `AnnotationParser::parse()` method supporting:
  - Module declarations with `module Path::Name { ... }` syntax
  - Function annotations with `FuncName(+, -, +);` syntax
  - Comments (lines starting with `//`)

---

## 3. Phase 2: Parser & AST

### 3.1 Verus AST Definitions

- [x] **Define core AST types** (`ast/mod.rs`) [26:01:22, 14:48]
  ```rust
  pub struct SpecFunction {
      pub name: Ident,
      pub generics: Generics,
      pub params: Vec<Parameter>,
      pub return_type: Type,
      pub recommends: Vec<Expr>,
      pub body: Expr,
      pub span: Span,
  }

  pub struct Parameter {
      pub name: Ident,
      pub ty: Type,
      pub mode: Option<ParameterMode>, // Filled by annotator
  }

  pub enum ParameterMode {
      Input,   // Read-only (+)
      Output,  // Must be computed (-)
  }
  ```

- [x] **Define expression AST** supporting Verus constructs [26:01:22, 14:48]
  ```rust
  pub enum Expr {
      // Logical operators
      Conjunction(Vec<Expr>),        // &&&
      Disjunction(Vec<Expr>),        // |||
      Implies(Box<Expr>, Box<Expr>), // ==>

      // Quantifiers
      Forall { vars: Vec<Binding>, triggers: Vec<Trigger>, body: Box<Expr> },
      Exists { vars: Vec<Binding>, body: Box<Expr> },

      // Control flow
      If { cond: Box<Expr>, then_: Box<Expr>, else_: Option<Box<Expr>> },
      Match { scrutinee: Box<Expr>, arms: Vec<MatchArm> },
      Let { binding: Binding, value: Box<Expr>, body: Box<Expr> },

      // Comparisons (key for mode analysis)
      Eq(Box<Expr>, Box<Expr>),      // ==

      // Field/member access
      Field(Box<Expr>, Ident),        // expr.field
      Index(Box<Expr>, Box<Expr>),    // expr[idx]

      // Struct construction
      Struct { name: Path, fields: Vec<(Ident, Expr)> },
      StructUpdate { base: Box<Expr>, fields: Vec<(Ident, Expr)> },

      // Collections
      Seq(Vec<Expr>),
      Set(Vec<Expr>),
      Map(Vec<(Expr, Expr)>),

      // Calls
      Call { func: Path, args: Vec<Expr> },
      MethodCall { receiver: Box<Expr>, method: Ident, args: Vec<Expr> },

      // Verus-specific
      View(Box<Expr>),               // expr@
      Arrow(Box<Expr>, Ident),       // expr->field (enum variant access)

      // Primitives
      Ident(Ident),
      Literal(Literal),
      Binary(Box<Expr>, BinOp, Box<Expr>),
      Unary(UnaryOp, Box<Expr>),
  }
  ```

- [x] **Define type AST** [26:01:22, 14:48]
  ```rust
  pub enum Type {
      Named(Path),
      Generic(Path, Vec<Type>),
      Tuple(Vec<Type>),
      Seq(Box<Type>),
      Set(Box<Type>),
      Map(Box<Type>, Box<Type>),
      Reference(Box<Type>, Mutability),
  }
  ```

### 3.2 Parser Implementation

- [x] **Implement Verus parser using `syn`** [26:01:22, 14:48] (see docs/dev/verus-parser-plan.md)
  - Parse `verus! { ... }` macro blocks
  - Extract `spec fn` declarations
  - Handle Verus-specific syntax (`&&&`, `|||`, `==>`, `@`, `->`)
  - Key findings: Need to check `==>` before `==`, and `&&&` before `&&` to avoid prefix matching issues

- [x] **Handle Verus extensions** [26:01:22, 16:15]
  - `recommends` clauses (basic support added)
  - `decreases` clauses - added to SpecFunction AST and parser
  - `requires`/`ensures` clauses - added to SpecFunction AST and parser
  - Trigger annotations - parser now handles `#![trigger]`, `#![auto]`, `#[trigger]`
  - Ghost/tracked modes - added VariableMode enum and parameter parsing

- [x] **Implement annotation file parser** [26:01:22, 15:35]
  - Simple grammar for mode declarations
  - Module scoping support
  - Implemented in `annotation/mod.rs` with full tests

### 3.3 Type Table Builder

- [x] **Build global type information** [26:01:22, 16:45]
  - Collect all struct/enum definitions - `TypeParser::try_parse_struct/enum`
  - Track field types and names - `StructDef`, `FieldDef`, `VariantDef`
  - Handle generic type parameters - `Generics` in struct/enum defs
  - Type alias support - `TypeAlias`
  - Implemented in `types/mod.rs`

- [x] **Track predicate signatures** [26:01:22, 16:45]
  - Parameter types - `FunctionSig`, `ParamSig`
  - Return types (always bool for spec predicates)
  - `TypeRegistry::register_spec_function()` for spec fn registration

---

## 4. Phase 3: Mode Analysis

### 4.1 Annotation Processing

- [x] **Parse and validate mode annotations** [26:01:22, 15:35]
  - Match annotations to spec function parameters
  - Validate parameter count matches
  - Report missing/extra annotations
  - Implemented in `moder/mod.rs:ModeAnalyzer::annotate()`

- [x] **Merge annotations with AST** [26:01:22, 15:35]
  ```rust
  pub struct AnnotatedFunction {
      pub spec_fn: SpecFunction,
      pub param_modes: Vec<ParameterMode>,
      pub is_functionalized: bool, // Can this be converted to exec?
  }
  ```
  - Implemented in `moder/mod.rs:AnnotatedFunction`

### 4.2 Mode Propagation

- [x] **Implement mode inference within expressions** [26:01:22, 16:01]
  - Equality `a == b`: one side must be output, other is expression
  - Struct fields: track which fields of output vars are assigned
  - Conditionals: both branches must assign same output variables
  - Implemented in `moder/mod.rs:ModeAnalyzer::analyze_expression()`

- [x] **Track output variable assignments** [26:01:22, 15:35]
  ```rust
  pub struct AssignmentTracker {
      // Maps output var to set of assigned members
      pub assignments: HashMap<Ident, HashSet<MemberPath>>,
  }

  pub enum MemberPath {
      Root,                          // The variable itself
      Field(Box<MemberPath>, Ident), // .field
      Index(Box<MemberPath>),        // [idx] (for sequences)
  }
  ```
  - Implemented in `moder/mod.rs:AssignmentTracker`

- [x] **Detect mode conflicts** [26:01:22, 16:55]
  - Output var used before assignment - `ModeConflict::UseBeforeAssignment`
  - Input var being assigned - `ModeConflict::InputAssignment`
  - Conflicting assignments in branches - `ModeConflict::BranchMismatch`
  - Implemented in `moder/mod.rs:ModeAnalyzer::detect_conflicts()`

### 4.3 Predicate Classification

- [x] **Classify predicates for translation** [26:01:22, 15:35]
  ```rust
  pub enum PredicateKind {
      // Can be fully functionalized
      Functional {
          inputs: Vec<Parameter>,
          outputs: Vec<Parameter>,
      },
      // Cannot functionalize, generate stub
      Stub { reason: String },
      // Pure predicate, no functionalization needed
      Pure,
  }
  ```
  - Implemented in `moder/mod.rs:ModeAnalyzer::classify_predicate()`

---

## 5. Phase 4: Validation

### 5.1 Saturation Check

- [x] **Verify all output members are assigned** [26:01:22, 15:35]
  - For each output parameter, traverse its type structure
  - Verify every field/member has exactly one assignment
  - Handle nested structs recursively

  ```rust
  fn check_saturation(
      func: &AnnotatedFunction,
      tracker: &AssignmentTracker,
  ) -> Result<(), SaturationError> {
      for (param, mode) in func.params.iter().zip(&func.param_modes) {
          if *mode == ParameterMode::Output {
              let required = get_all_members(&param.ty);
              let assigned = tracker.assignments.get(&param.name);
              let missing = required.difference(assigned);
              if !missing.is_empty() {
                  return Err(SaturationError { param, missing });
              }
          }
      }
      Ok(())
  }
  ```

  - Implemented in `checker/mod.rs:SaturationChecker`

### 5.2 Harmony Check

- [x] **Verify no double assignments** [26:01:22, 15:35] (stub implementation)
  - Track assignment order left-to-right
  - Detect if same member assigned twice
  - Handle branch merging (both branches must agree)
  - Implemented in `checker/mod.rs:HarmonyChecker` (needs full implementation)

### 5.3 Obligation Check

- [x] **Verify output vars used only after assignment** [26:01:22, 15:35] (stub implementation)
  - Build dependency graph within expression
  - Topologically sort assignments
  - Detect cycles (impossible to execute)
  - Implemented in `checker/mod.rs:ObligationChecker` (needs full implementation)

### 5.4 Template Matching for Collections

- [ ] **Define supported quantifier templates**
  ```rust
  pub enum QuantifierTemplate {
      // seq![...] or Seq::new(|i| ...)
      SeqComprehension {
          length_expr: Expr,
          element_expr: Expr,  // as function of index
      },

      // Set::new(|x| ...)
      SetComprehension {
          domain_predicate: Expr,
      },

      // Map::new(|k| ..., |k| ...)
      MapComprehension {
          domain_predicate: Expr,
          value_expr: Expr,
      },
  }
  ```

- [ ] **Implement template matchers**
  - Match `forall |i| 0 <= i < len ==> seq[i] == expr` → SeqComprehension
  - Match `forall |k| k in map' <==> pred` → MapComprehension domain
  - Match `forall |k| k in map' ==> map'[k] == expr` → MapComprehension value

- [ ] **Report template matching failures with suggestions**

---

## 6. Phase 5: Code Generation

### 6.1 Type Generation

- [ ] **Generate concrete types for each spec type**
  ```rust
  // Input (spec)
  pub struct LAcceptor {
      pub max_bal: Ballot,
      pub votes: Votes,
  }

  // Output (exec) - auto-generated
  pub struct CAcceptor {
      pub max_bal: CBallot,
      pub votes: CVotes,
  }
  ```

- [ ] **Generate validity predicates**
  ```rust
  impl CAcceptor {
      pub open spec fn well_formed(&self) -> bool {
          &&& self.max_bal.well_formed()
          &&& self.votes.well_formed()
      }
  }
  ```

- [ ] **Generate View trait implementations**
  ```rust
  impl View for CAcceptor {
      type V = LAcceptor;

      open spec fn view(&self) -> LAcceptor {
          LAcceptor {
              max_bal: self.max_bal@,
              votes: self.votes@,
          }
      }
  }
  ```

### 6.2 Function Generation

- [ ] **Transform spec predicates to exec functions**
  - Convert parameter types (L* → C*)
  - Convert return type (bool → tuple of outputs)
  - Generate requires/ensures clauses

- [ ] **Transform expressions**
  ```rust
  fn transform_expr(expr: &Expr, ctx: &TransformContext) -> ExecExpr {
      match expr {
          // Equality assignment: s_.field == expr
          // → let field_value = transform(expr); ...
          Expr::Eq(lhs, rhs) if is_output_access(lhs, ctx) => {
              let value = transform_expr(rhs, ctx);
              ExecExpr::Assignment(extract_path(lhs), value)
          }

          // Conjunction: collect assignments
          Expr::Conjunction(exprs) => {
              let assignments = exprs.iter()
                  .map(|e| transform_expr(e, ctx))
                  .collect();
              ExecExpr::Block(assignments)
          }

          // Conditional: both branches produce same outputs
          Expr::If { cond, then_, else_ } => {
              ExecExpr::If {
                  cond: transform_expr(cond, ctx),
                  then_: transform_expr(then_, ctx),
                  else_: else_.map(|e| transform_expr(e, ctx)),
              }
          }

          // Quantifier: apply template
          Expr::Forall { .. } => {
              match match_template(expr) {
                  Some(SeqComprehension { len, elem }) => {
                      // Generate: (0..len).map(|i| elem(i)).collect()
                  }
                  None => {
                      // Cannot functionalize, report error
                  }
              }
          }

          // ... other cases
      }
  }
  ```

- [ ] **Generate struct construction**
  ```rust
  // From assignments: s_.max_bal == bal, s_.votes == s.votes
  // Generate:
  CAcceptor {
      max_bal: bal.clone(),
      votes: s.votes.clone(),
      constants: s.constants.clone(),  // Unchanged fields
  }
  ```

### 6.3 Proof Linkage

- [ ] **Generate ensures clauses linking to spec**
  ```rust
  ensures
      result.0.well_formed(),
      // Link to original spec predicate
      LAcceptorProcess1a(
          old(s)@,      // Pre-state (spec)
          result.0@,    // Post-state (spec)
          inp@,         // Input (spec)
          result.1@,    // Sent packets (spec)
      ),
  ```

- [ ] **Generate proof helpers for complex transformations**
  - Lemmas for sequence comprehension equivalence
  - Lemmas for map construction equivalence

### 6.4 Collection Operations

- [ ] **Implement seq generation**
  ```rust
  // Spec: forall |i| 0 <= i < n ==> result[i] == f(i)
  // Exec:
  let mut result = Vec::with_capacity(n);
  for i in 0..n {
      result.push(f_impl(i));
  }
  result
  ```

- [ ] **Implement map generation**
  ```rust
  // Spec: forall |k| k in result <==> k in src && pred(k)
  //       forall |k| k in result ==> result[k] == f(src[k])
  // Exec:
  let mut result = HashMap::new();
  for (k, v) in src.iter() {
      if pred_impl(k) {
          result.insert(k.clone(), f_impl(v));
      }
  }
  result
  ```

---

## 7. Phase 6: Runtime Support

### 7.1 Standard Library Extensions

- [ ] **Extend Verus collections with exec operations**
  - `Vec<T>` with View to `Seq<T>`
  - `HashMap<K,V>` with View to `Map<K,V>`
  - `HashSet<T>` with View to `Set<T>`

- [ ] **Provide clone/copy helpers**
  ```rust
  pub trait DeepClone: Sized {
      fn deep_clone(&self) -> Self;
  }
  ```

### 7.2 Networking Runtime

- [ ] **Define packet/message traits**
  ```rust
  pub trait Marshalable: Sized {
      spec fn ghost_serialize(&self) -> Seq<u8>;
      exec fn serialize(&self) -> Vec<u8>
          ensures result@ == self.ghost_serialize();
      exec fn deserialize(data: &[u8]) -> Option<Self>;
  }
  ```

- [ ] **Integrate with existing C# I/O framework**
  - FFI bindings for network operations
  - Packet send/receive interfaces

### 7.3 Generated Code Runtime

- [ ] **Provide base traits for generated types**
  ```rust
  pub trait SpecType: View {
      spec fn well_formed(&self) -> bool;
  }

  pub trait ExecType: SpecType + Clone {
      type Spec: View<V = Self::Spec>;
  }
  ```

---

## 8. Phase 7: Testing & Validation

### 8.1 Unit Tests

- [ ] **Parser tests**
  - Parse individual Verus constructs
  - Handle edge cases (nested generics, complex expressions)

- [ ] **Mode analysis tests**
  - Correct mode propagation
  - Conflict detection

- [ ] **Validation tests**
  - Saturation check positive/negative cases
  - Harmony check positive/negative cases
  - Template matching cases

### 8.2 Integration Tests

- [ ] **End-to-end transformation tests**
  - Simple predicates → exec functions
  - Complex predicates with conditionals
  - Collection operations

- [ ] **Verify generated code compiles with Verus**
  - Run Verus on generated output
  - Check proofs discharge

### 8.3 Real Protocol Tests

- [ ] **Test with Lock service**
  - Transform `NodeInit`, `NodeGrant`, `NodeAccept`
  - Verify generated code maintains proofs

- [ ] **Test with RSL (Paxos) components**
  - Transform Acceptor predicates
  - Transform Proposer predicates
  - Transform Learner predicates

### 8.4 Negative Tests

- [ ] **Test error reporting**
  - Missing mode annotations
  - Saturation failures
  - Unsupported quantifier patterns
  - Circular dependencies

---

## 9. Phase 8: Integration & Tooling

### 9.1 CLI Tool

- [ ] **Implement command-line interface**
  ```bash
  tla-transpile \
      --input src/protocol/RSL/acceptor.rs \
      --annotations src/protocol/RSL/acceptor.automan \
      --config transpile.toml \
      --output src/implementation/RSL/acceptor_gen.rs
  ```

- [ ] **Support batch processing**
  ```bash
  tla-transpile --project . --output-dir src/generated/
  ```

### 9.2 Build Integration

- [ ] **Integrate with scons build system**
  - Add transpiler as build step
  - Dependency tracking (re-transpile on spec change)

- [ ] **Cargo build script integration**
  ```rust
  // build.rs
  fn main() {
      tla_transpile::generate("src/protocol", "src/generated");
  }
  ```

### 9.3 IDE Support

- [ ] **LSP integration considerations**
  - Jump from generated code to spec
  - Error highlighting in spec files

### 9.4 Documentation

- [ ] **Document annotation format**
- [ ] **Document supported patterns/templates**
- [ ] **Document limitations and workarounds**
- [ ] **Provide migration guide from manual implementations**

---

## 10. Milestones

### Milestone 1: Proof of Concept (4-6 weeks)
- [ ] Basic parser for Verus spec functions
- [ ] Simple mode annotation processing
- [ ] Transform trivial predicates (no collections, no quantifiers)
- [ ] Generate compilable Verus exec functions

**Deliverable**: Transform `NodeInit` from Lock service

### Milestone 2: Core Functionality (6-8 weeks)
- [ ] Full expression transformation
- [ ] Saturation/Harmony/Obligation checks
- [ ] Conditional handling (if-then-else)
- [ ] Simple collection operations (fixed-size sequences)

**Deliverable**: Transform Lock service completely

### Milestone 3: Collection Support (4-6 weeks)
- [ ] Quantifier template matching
- [ ] Sequence comprehension generation
- [ ] Map/Set operations
- [ ] Nested structure handling

**Deliverable**: Transform RSL Acceptor module

### Milestone 4: Full RSL (6-8 weeks)
- [ ] Handle all RSL protocol predicates
- [ ] Complex nested updates
- [ ] Multi-predicate call chains
- [ ] Runtime integration

**Deliverable**: Full RSL transpilation with working proofs

### Milestone 5: Production Ready (4-6 weeks)
- [ ] Robust error handling and reporting
- [ ] Performance optimization
- [ ] Documentation and examples
- [ ] CI/CD integration

**Deliverable**: Stable release with documentation

---

## Appendix A: Supported Patterns

### A.1 Assignment Patterns

| Spec Pattern | Exec Generation |
|--------------|-----------------|
| `s_.field == expr` | `let field = expr_impl;` |
| `s_ == s.(field := expr)` | `Struct { field: expr_impl, ..s.clone() }` |
| `s_ == s` | `s.clone()` |

### A.2 Quantifier Templates

| Spec Pattern | Exec Generation |
|--------------|-----------------|
| `forall \|i\| 0 <= i < n ==> s[i] == f(i)` | `(0..n).map(\|i\| f(i)).collect()` |
| `forall \|k\| k in m' <==> k in m && p(k)` | `m.iter().filter(\|(k,_)\| p(k))` |
| `forall \|k\| k in m' ==> m'[k] == f(m[k])` | `.map(\|(k,v)\| (k, f(v))).collect()` |

### A.3 Conditional Patterns

| Spec Pattern | Exec Generation |
|--------------|-----------------|
| `if cond { s_ == a } else { s_ == b }` | `if cond { a } else { b }` |
| `if cond { ... } else { s_ == s }` | `if cond { ... } else { s.clone() }` |

---

## Appendix B: Known Limitations

1. **Generic type instantiation in expressions** - May require manual annotation
2. **Recursive predicates** - Need termination proofs, limited support
3. **Complex triggers** - May not translate efficiently
4. **Dependent types** - Limited support for value-dependent typing
5. **External function calls** - Must be marked and handled specially
6. **Infinite collections** - Must have finite bounds for exec code

---

## Appendix C: Comparison with AutoMan

| Aspect | AutoMan (Dafny) | tla-rs Transpiler (Verus) |
|--------|-----------------|---------------------------|
| Input Language | Dafny | Rust/Verus |
| Output Language | Dafny | Rust/Verus |
| Parser | Menhir (OCaml) | syn (Rust) |
| Implementation | OCaml | Rust |
| Mode Annotation | `.automan` files | `.automan` files (same format) |
| Validation | Saturation/Harmony/Obligation | Same approach |
| Collection Templates | Strict matching | Same approach |
| Proof Linkage | ensures clauses | ensures clauses |
