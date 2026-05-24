//! Model checking support for source-first Phase 22 workflows.
//!
//! This module currently provides:
//! - `model.toml` parsing + validation
//! - normalized transition IR extraction from `LNext`
//! - runtime value modeling for evaluator + state exploration
//! - expression evaluation for model-check execution semantics
//! - finite-domain expansion for existential branch variables
//! - branch-constraint solving into concrete successor states
//! - canonical-key successor deduplication
//! - optional stuttering vs deadlock empty-successor semantics
//! - bounded BFS/DFS state-space exploration
//! - `LInit`-based initial-state construction over finite candidate sets
//! - user-selected invariant evaluation on reached states
//! - optional deadlock detection while exploring reached states
//! - counterexample trace emission with action branches + state diffs

pub mod bytecode;
pub mod config;
pub mod domain;
pub mod dpor;
pub mod evaluator;
pub mod explorer;
pub mod field_schema;
pub mod graph;
pub mod helpers;
pub mod init;
pub mod invariant;
pub mod ir;
pub mod liveness;
pub mod parity;
pub mod por;
pub mod solver;
pub mod symbol;
pub mod value;
