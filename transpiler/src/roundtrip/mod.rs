//! Round-trip consistency testing for bidirectional transpilation.
//!
//! This module provides utilities for testing that TLA+ ↔ Verus transpilation
//! maintains semantic equivalence across round-trips.
//!
//! # Round-trip Testing
//!
//! There are two directions to test:
//! 1. **Verus → TLA+ → Verus**: Convert Verus spec to TLA+, then back to Verus
//! 2. **TLA+ → Verus → TLA+**: Convert TLA+ to Verus, then back to TLA+
//!
//! # Canonical Forms
//!
//! Since exact text matching is not feasible (due to formatting, naming conventions,
//! etc.), we compare ASTs after converting them to canonical forms.

pub mod canonical;
pub mod compare;

pub use canonical::{canonicalize_tla_expr, canonicalize_tla_module, CanonicalConfig};
pub use compare::{compare_tla_expr, compare_tla_modules, CompareResult, Difference};
