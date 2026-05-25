//! Runtime value types for native-codegen model checking.
//!
//! This crate provides the core value representation (`RuntimeValue`,
//! `NamedFields`, `SetRepr`, `SmallIntSet`, `Symbol`) used by both the
//! transpiler's evaluator and by natively compiled spec functions.
//!
//! Keeping these types in a separate, thin crate lets generated code
//! depend only on `transpiler-runtime` instead of the full transpiler
//! dependency tree (syn, quote, clap, miette, …).

pub mod helpers;
pub mod small_int_set;
pub mod symbol;
pub mod value;

pub use small_int_set::{SmallIntSet, SmallIntSetIter};
pub use symbol::{Symbol, SymbolStr};
pub use value::{
    FingerprintCache, NamedFields, RuntimeCollectionBounds, RuntimeError, RuntimeResult,
    RuntimeValue, SetRepr, SetReprIter,
};

// Re-export helpers for use in generated code
pub use helpers::{
    rt_binop, rt_call, rt_error, rt_expect_bool, rt_expect_int, rt_field, rt_field_val, rt_index,
    rt_is_struct, rt_is_variant, rt_match_fallthrough, rt_method_call, rt_negate,
    rt_quantifier_domain, rt_struct_update, rt_struct_update_named, rt_tuple_field,
    rt_variant_field, BinOp,
};
