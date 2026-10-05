//! CausalMesh (PVLDB 17(13), 2024; arXiv 2508.15647v2): model, safety proof, and a
//! single-round counterexample. See docs/causalmesh-proof.md.
pub mod vc;
pub mod ring;
pub mod types;
pub mod model;
pub mod behavior;
pub mod properties;
pub mod scenarios;
pub mod invariants;
pub mod lemmas;
pub mod integration;
pub mod channels;
pub mod frame;
pub mod step_tail;
pub mod step_forward;
pub mod step_write;
pub mod step_read;
pub mod step_misc;
pub mod past;
pub mod safety;
