// Standalone Verus crate for the Jetpack Figure 14 recovery audit.
// It reuses the live recovery model and adds only Figure 14's literal rules.
// See docs/jetpack-recovery-audit.md. Not part of the main crate.
#[path = "../Jetpack/recovery.rs"]
pub mod recovery;
pub mod figure14;
