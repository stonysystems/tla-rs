// Optimized RSL module — copy of generated/RSL/ with P3.x hot-path optimizations applied.
// Phase 46: in-place mutation, Vec preallocate, single-pass loop fusion.

// All 7 function modules are enabled.
// election_gen contains standalone election functions (Phase 19.5).
pub mod acceptor_gen;
pub mod broadcast_gen;
pub mod election_gen;
pub mod executor_gen;
pub mod learner_gen;
pub mod proposer_gen;
pub mod replica_gen;
pub mod types_gen;
