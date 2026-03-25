//! DPOR-based model checker prototype for tla-rs specifications.
//!
//! This crate implements a Dynamic Partial Order Reduction (DPOR) explorer
//! for translated TLA+ specifications. It is an isolated prototype that
//! does NOT modify `transpiler/src/modelcheck/`.
//!
//! See `design.md` for architecture, type definitions, and the
//! prototype-to-mainline integration gate.

pub mod baseline;
pub mod types;

/// Re-export shared types from the transpiler for convenience.
pub use verus_transpiler::modelcheck::value::RuntimeValue;
