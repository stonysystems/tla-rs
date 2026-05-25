//! Runtime value types for native-codegen model checking.
//!
//! This crate provides the core value representation (`RuntimeValue`,
//! `NamedFields`, `SetRepr`, `SmallIntSet`, `Symbol`) used by both the
//! transpiler's evaluator and by natively compiled spec functions.
//!
//! Keeping these types in a separate, thin crate lets generated code
//! depend only on `transpiler-runtime` instead of the full transpiler
//! dependency tree (syn, quote, clap, miette, …).

pub mod small_int_set;
pub mod symbol;
pub mod value;

pub use small_int_set::{SmallIntSet, SmallIntSetIter};
pub use symbol::{Symbol, SymbolStr};
pub use value::{
    FingerprintCache, NamedFields, RuntimeCollectionBounds, RuntimeError, RuntimeResult,
    RuntimeValue, SetRepr, SetReprIter,
};
