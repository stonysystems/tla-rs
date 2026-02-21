//! Model checking support for source-first Phase 22 workflows.
//!
//! This module currently provides:
//! - `model.toml` parsing + validation
//! - normalized transition IR extraction from `LNext`

pub mod config;
pub mod ir;
