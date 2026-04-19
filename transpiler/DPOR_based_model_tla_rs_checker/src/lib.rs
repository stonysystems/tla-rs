//! DPOR-based model checker prototype for tla-rs specifications.
//!
//! Phase 38.18.10 (the integration step): the algorithm now lives
//! in `transpiler/src/modelcheck/dpor/` so the main
//! `verus-transpile model-check` path can invoke it. This crate's
//! library is now a thin re-export of those modules so the existing
//! `dpor-checker` CLI binary keeps working without code changes.
//!
//! See `design.md` for architecture notes from when this was an
//! isolated prototype.

pub use verus_transpiler::modelcheck::dpor::baseline;
pub use verus_transpiler::modelcheck::dpor::enabled;
pub use verus_transpiler::modelcheck::dpor::explore as dpor;
pub use verus_transpiler::modelcheck::dpor::types;
pub use verus_transpiler::modelcheck::dpor::witness as explorer;

/// Re-export shared types from the transpiler for convenience.
pub use verus_transpiler::modelcheck::value::RuntimeValue;
