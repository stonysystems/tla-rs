# verus2tla Module Design

## Overview

The `verus2tla` module provides the reverse direction translation capability for the transpiler, converting Verus spec functions (from tla-rs protocol definitions) to TLA+ specifications.

## Module Structure

```
transpiler/src/verus2tla/
├── mod.rs          # Module exports and public API
├── extractor.rs    # Extract spec functions from Verus source files
├── converter.rs    # Convert Verus AST to TLA+ AST
├── printer.rs      # Pretty-print TLA+ AST to text
└── types.rs        # Type mapping utilities
```

## Component Responsibilities

### 1. `extractor.rs` - Verus Spec Extractor

**Purpose:** Parse Verus source files and extract spec-level constructs that should be translated to TLA+.

**Key Types:**
```rust
pub struct VerusExtractor;

pub struct ExtractedModule {
    pub name: String,
    pub structs: Vec<ExtractedStruct>,
    pub type_aliases: Vec<ExtractedTypeAlias>,
    pub spec_functions: Vec<ExtractedSpecFn>,
}

pub struct ExtractedStruct {
    pub name: String,
    pub fields: Vec<(String, VerusType)>,
}

pub struct ExtractedSpecFn {
    pub name: String,
    pub params: Vec<(String, VerusType)>,
    pub return_type: Option<VerusType>,
    pub body: VerusExpr,
    pub recommends: Option<VerusExpr>,
}
```

**Key Methods:**
- `extract_module(source: &str) -> Result<ExtractedModule>` - Extract from a single Verus file
- `extract_directory(path: &Path) -> Result<Vec<ExtractedModule>>` - Extract from all files in a directory

**Extraction Rules:**
1. Only extract content within `verus! { ... }` blocks
2. Extract `pub struct` definitions (spec-level types)
3. Extract `pub type` aliases
4. Extract `pub open spec fn` definitions
5. Skip `proof fn` and `exec fn` declarations
6. Skip `#[verifier(external)]` items

### 2. `converter.rs` - Verus to TLA+ Converter

**Purpose:** Transform extracted Verus AST into TLA+ AST.

**Key Types:**
```rust
pub struct Verus2TlaConverter {
    config: ConverterConfig,
}

pub struct ConverterConfig {
    pub strip_prefix: Option<String>,  // Strip "L" prefix from names
    pub module_name_style: NamingStyle,
}

pub enum NamingStyle {
    PascalCase,  // TLA+ convention
    Original,    // Keep as-is
}
```

**Key Methods:**
- `convert_module(&self, module: ExtractedModule) -> TlaModule`
- `convert_struct(&self, s: ExtractedStruct) -> Vec<TlaOperator>` - Generate type operators
- `convert_spec_fn(&self, f: ExtractedSpecFn) -> TlaOperator`
- `convert_expr(&self, expr: VerusExpr) -> TlaExpr`
- `convert_type(&self, ty: VerusType) -> TlaExpr`

**Mapping Table - Expressions:**

| Verus | TLA+ |
|-------|------|
| `&&`/`&&&` | `/\` (TlaBinOp::And) |
| `\|\|`/`\|\|\|` | `\/` (TlaBinOp::Or) |
| `!` | `~` (TlaUnaryOp::Not) |
| `==>` | `=>` (TlaBinOp::Implies) |
| `<==>` | `<=>` (TlaBinOp::Iff) |
| `==` | `=` (TlaBinOp::Eq) |
| `!=` | `#` (TlaBinOp::Neq) |
| `forall\|x: T\| P(x)` | `\A x \in T : P(x)` (TlaExpr::Forall) |
| `exists\|x: T\| P(x)` | `\E x \in T : P(x)` (TlaExpr::Exists) |
| `choose\|x: T\| P(x)` | `CHOOSE x \in T : P(x)` (TlaExpr::Choose) |
| `if c { a } else { b }` | `IF c THEN a ELSE b` (TlaExpr::IfThenElse) |
| `seq![a, b]` | `<<a, b>>` (TlaExpr::Tuple) |
| `set![a, b]` | `{a, b}` (TlaExpr::SetEnum) |
| `s.len()` | `Len(s)` (TlaExpr::OpApply) |
| `s[i]` | `s[i]` (TlaExpr::FnApply) - Note: TLA+ is 1-indexed |
| `s.push(x)` | `Append(s, x)` (TlaExpr::OpApply) |
| `m.insert(k, v)` | `[m EXCEPT ![k] = v]` (TlaExpr::FnExcept) |
| `m[k]` | `m[k]` (TlaExpr::FnApply) |
| `m.contains_key(k)` | `k \in DOMAIN m` (TlaExpr::BinOp) |
| `Struct { f: v, ... }` | `[f \|-> v, ...]` (TlaExpr::Record) |
| `s.field` | `s.field` (TlaExpr::RecordAccess) |

**Mapping Table - Types:**

| Verus | TLA+ |
|-------|------|
| `int` | `Int` |
| `nat` | `Nat` |
| `bool` | `BOOLEAN` |
| `Seq<T>` | `Seq(T)` |
| `Set<T>` | `SUBSET T` |
| `Map<K, V>` | `[K -> V]` |
| struct | Record type `[field1: Type1, ...]` |
| enum | Tagged union (discriminated record) |

### 3. `printer.rs` - TLA+ Pretty Printer

**Purpose:** Convert TLA+ AST to properly formatted TLA+ text output.

**Key Types:**
```rust
pub struct TlaPrinter {
    config: PrinterConfig,
}

pub struct PrinterConfig {
    pub indent_width: usize,      // Default: 4
    pub max_line_width: usize,    // Default: 80
    pub use_unicode: bool,        // Use ∈ vs \in
}
```

**Key Methods:**
- `print_module(&self, module: &TlaModule) -> String`
- `print_operator(&self, op: &TlaOperator) -> String`
- `print_expr(&self, expr: &TlaExpr) -> String`

**Output Format:**
```tla
---- MODULE ModuleName ----
EXTENDS Integers, Sequences, FiniteSets

\* Type definitions
TypeName == [field1: Type1, field2: Type2]

\* Constants
CONSTANT ConstantName

\* Variables (if any)
VARIABLE varName

\* Operators
OperatorName(param1, param2) ==
    /\ condition1
    /\ condition2

====
```

### 4. `types.rs` - Type Mapping Utilities

**Purpose:** Handle type conversion between Verus and TLA+.

**Key Types:**
```rust
pub enum VerusType {
    Int,
    Nat,
    Bool,
    Seq(Box<VerusType>),
    Set(Box<VerusType>),
    Map(Box<VerusType>, Box<VerusType>),
    Named(String),
    Generic(String, Vec<VerusType>),
    Tuple(Vec<VerusType>),
    Reference(Box<VerusType>),
}

pub struct TypeMapper {
    custom_mappings: HashMap<String, String>,
}
```

**Key Methods:**
- `parse_verus_type(s: &str) -> VerusType`
- `to_tla_type(ty: &VerusType) -> TlaExpr`
- `register_mapping(verus_name: &str, tla_name: &str)`

## Public API (`mod.rs`)

```rust
pub mod extractor;
pub mod converter;
pub mod printer;
pub mod types;

use crate::tla::ast::TlaModule;
use std::path::Path;

pub struct Verus2Tla {
    extractor: extractor::VerusExtractor,
    converter: converter::Verus2TlaConverter,
    printer: printer::TlaPrinter,
}

impl Verus2Tla {
    pub fn new() -> Self;
    pub fn with_config(config: Verus2TlaConfig) -> Self;

    /// Translate a single Verus file to TLA+
    pub fn translate_file(&self, path: &Path) -> Result<String>;

    /// Translate a Verus source string to TLA+
    pub fn translate_source(&self, source: &str, module_name: &str) -> Result<String>;

    /// Translate a directory of Verus files to TLA+
    pub fn translate_directory(&self, input_dir: &Path, output_dir: &Path) -> Result<()>;
}

pub struct Verus2TlaConfig {
    pub strip_l_prefix: bool,
    pub use_unicode_operators: bool,
    pub indent_width: usize,
}
```

## CLI Integration

Add new subcommand to `main.rs`:

```rust
#[derive(Parser)]
enum Commands {
    // ... existing commands ...

    /// Convert Verus spec to TLA+
    #[command(name = "verus2tla")]
    Verus2Tla(Verus2TlaArgs),
}

#[derive(Args)]
struct Verus2TlaArgs {
    /// Input Verus file or directory
    #[arg(short, long)]
    input: PathBuf,

    /// Output TLA+ file or directory
    #[arg(short, long)]
    output: PathBuf,

    /// Strip 'L' prefix from type/function names
    #[arg(long, default_value = "true")]
    strip_prefix: bool,

    /// Use Unicode operators (∈, ∀, etc.)
    #[arg(long, default_value = "false")]
    unicode: bool,
}
```

## Translation Pipeline

```
┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐
│   Verus Source  │ ──▶ │    Extractor    │ ──▶ │    Converter    │ ──▶ │     Printer     │
│      (.rs)      │     │ (ExtractedModule)│     │   (TlaModule)   │     │   (.tla text)   │
└─────────────────┘     └─────────────────┘     └─────────────────┘     └─────────────────┘
```

## Example Translation

### Input (Verus - types.rs)

```rust
verus! {
    pub struct Ballot {
        pub seqno: int,
        pub proposer_id: int,
    }

    pub open spec fn BalLt(ba: Ballot, bb: Ballot) -> bool {
        ||| ba.seqno < bb.seqno
        ||| (ba.seqno == bb.seqno && ba.proposer_id < bb.proposer_id)
    }
}
```

### Output (TLA+)

```tla
---- MODULE Types ----
EXTENDS Integers

\* Type definitions
Ballot == [seqno: Int, proposer_id: Int]

\* Operators
BalLt(ba, bb) ==
    \/ ba.seqno < bb.seqno
    \/ (ba.seqno = bb.seqno /\ ba.proposer_id < bb.proposer_id)

====
```

## Error Handling

The module uses `miette` for error reporting (consistent with existing codebase):

```rust
#[derive(Debug, thiserror::Error, miette::Diagnostic)]
pub enum Verus2TlaError {
    #[error("Failed to parse Verus source: {message}")]
    ParseError { message: String, span: Option<Span> },

    #[error("Unsupported Verus construct: {construct}")]
    UnsupportedConstruct { construct: String, span: Option<Span> },

    #[error("Type mapping not found for: {type_name}")]
    UnknownType { type_name: String },

    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),
}
```

## Testing Strategy

1. **Unit tests** for each component:
   - `extractor_tests.rs` - Test parsing of various Verus constructs
   - `converter_tests.rs` - Test AST conversion
   - `printer_tests.rs` - Test output formatting

2. **Integration tests**:
   - Translate RSL protocol files and verify output
   - Round-trip tests (where possible)

3. **Snapshot tests**:
   - Store expected TLA+ output for RSL modules
   - Compare generated output against snapshots

## Implementation Order

1. **Phase 1**: Basic infrastructure
   - [ ] Create module structure files
   - [ ] Implement `types.rs` (type mapping)
   - [ ] Implement `printer.rs` (TLA+ output)

2. **Phase 2**: Extraction and conversion
   - [ ] Implement `extractor.rs` (Verus parsing)
   - [ ] Implement `converter.rs` (AST conversion)

3. **Phase 3**: Integration
   - [ ] Add CLI subcommand
   - [ ] Add tests
   - [ ] Generate RSL TLA+ specs
