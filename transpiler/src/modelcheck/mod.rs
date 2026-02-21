//! Model checking support for source-first Phase 22 workflows.
//!
//! This module currently provides:
//! - `model.toml` parsing + validation
//! - normalized transition IR extraction from `LNext`
//! - runtime value modeling for evaluator + state exploration
//! - expression evaluation for model-check execution semantics

pub mod config;
pub mod evaluator;
pub mod ir;
pub mod value;
