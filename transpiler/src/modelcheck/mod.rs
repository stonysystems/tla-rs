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

pub mod config;
pub mod domain;
pub mod evaluator;
pub mod explorer;
pub mod graph;
pub mod init;
pub mod invariant;
pub mod ir;
pub mod por;
pub mod solver;
pub mod value;
