//! Phase 38.18.10: DPOR sleep-set explorer integrated into the
//! mainline `verus-transpile model-check` path.
//!
//! This module is the in-place relocation of the prototype DPOR
//! algorithm that previously lived under
//! `transpiler/DPOR_based_model_tla_rs_checker/src/`. Moving it into
//! `transpiler/src/modelcheck/` resolves the cyclic dependency that
//! had blocked the main path from invoking DPOR (the prototype crate
//! depends on `verus-transpiler`, so `verus-transpiler` could not
//! depend on it in turn).
//!
//! The four sub-modules:
//! - `types`     — DporConfig, ProcessId, StateFingerprint, etc.
//! - `enabled`   — SpecContext: spec-loading + transition extraction.
//! - `explore`   — `explore_dpor`: the DFS + sleep-set algorithm.
//! - `witness`   — execution-graph export helpers (for shadow-compare).
//!
//! The original `dpor-checker` binary still works unchanged; its
//! library now re-exports these modules so its callers keep working.

pub mod baseline;
pub mod enabled;
pub mod explore;
pub mod types;
pub mod witness;

pub use explore::{
    explore_dpor, explore_dpor_parallel, DporConfig, DporResult, RuntimeConflictStats,
    RuntimeIndependenceOverrides, SleepDepthStats, SleepIndependenceBlockers, ViolationWitness,
    WitnessStep,
};
pub use types::{
    ActionId, BacktrackInfo, EnabledTransition, Event, ExecutionPrefix, ProcessId,
    StateFingerprint, TransitionFootprint, VectorClock,
};
