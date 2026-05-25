//! Re-export from `transpiler-runtime`.
//!
//! The canonical implementation lives in `transpiler_runtime::small_int_set`.
//! This module re-exports everything so that existing
//! `crate::modelcheck::small_int_set::*` imports continue to work.

pub use transpiler_runtime::small_int_set::*;
