//! EPaxos* — the corrected Egalitarian Paxos (OPODIS 2025).
//!
//! Distinct from `crate::protocol::EPaxos`, which models the 2013 protocol
//! whose published specification is unsafe. See `types.rs` for the full note.
pub mod chosen;
pub mod distributed_system;
pub mod epaxos_star;
pub mod invariants;
pub mod refinement;
pub mod types;
