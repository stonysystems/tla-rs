/// Simplified PBFT (Practical Byzantine Fault Tolerance) types.
///
/// Models the core PBFT phases from a single node's perspective:
/// Pre-prepare -> Prepare -> Commit -> Reply, with view changes on timeout.
/// Byzantine fault tolerance requires 3f+1 replicas to tolerate f faults.
use vstd::prelude::*;

verus! {

/// PBFT protocol phase
pub enum LPhase {
    PrePrepare,
    Prepare,
    Commit,
    Replied,
}

/// State of a single PBFT replica
pub struct LState {
    /// Current view number (incremented on view change)
    pub view: int,
    /// Current protocol phase
    pub phase: LPhase,
    /// Number of prepare messages received for current request
    pub prepare_count: int,
    /// Number of commit messages received for current request
    pub commit_count: int,
    /// Current sequence number (incremented after each committed request)
    pub seq_num: int,
    /// Whether this node is the primary for current view
    pub is_primary: bool,
}

/// Protocol constants
pub struct LConstants {
    /// Number of faulty nodes tolerated (f)
    pub f: int,
    /// Total number of replicas (must be >= 3f+1)
    pub n: int,
}

} // verus!
