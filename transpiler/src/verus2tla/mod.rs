//! Verus to TLA+ transpiler module.
//!
//! This module provides functionality to convert Verus spec functions (tla-rs)
//! to TLA+ specifications. This is the reverse direction of the `tla` module.
//!
//! # Overview
//!
//! The verus2tla pipeline:
//! 1. **Extractor** - Parse Verus source and extract spec-only content
//! 2. **Converter** - Convert Verus AST to TLA+ AST
//! 3. **Printer** - Pretty-print TLA+ AST to text
//!
//! # Example
//!
//! ```ignore
//! use verus_transpiler::verus2tla::{Verus2TlaConverter, TlaPrinter};
//!
//! let converter = Verus2TlaConverter::new();
//! let tla_module = converter.convert_file("src/protocol/RSL/acceptor.rs")?;
//!
//! let printer = TlaPrinter::new();
//! let tla_text = printer.print_module(&tla_module);
//! ```

pub mod converter;
pub mod printer;
pub mod types;

pub use converter::{ConverterConfig, Verus2TlaConverter};
pub use printer::TlaPrinter;
pub use types::{TypeMapper, VerusType};
