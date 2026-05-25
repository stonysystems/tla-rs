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

/// PBFT protocol network messages (spec-level).
pub enum LPBFTMessage {
    PrePrepare { view: int, seq: int, digest: int },
    /// Reply sent to client after executing a committed request
    ClientReply { digest: int },
}

/// State of a single PBFT replica
pub struct LState {
    /// Current view number (incremented on view change)
    pub view: int,
    /// Current protocol phase
    pub phase: LPhase,
    /// Set of replicas that sent prepare messages for current request
    pub prepare_senders: Set<int>,
    /// Set of replicas that sent commit messages for current request
    pub commit_senders: Set<int>,
    /// Current sequence number (incremented after each committed request)
    pub seq_num: int,
    /// Whether this node is the primary for current view
    pub is_primary: bool,
    /// Request digest for the current request being processed
    pub request_digest: int,
    // Checkpoint support
    /// Sequence number of the last stable checkpoint
    pub checkpoint_seq: int,
    /// Digest of the last stable checkpoint
    pub checkpoint_digest: int,
    // Watermark tracking
    /// Low watermark: sequence numbers below this are already committed
    pub low_watermark: int,
    /// High watermark: upper bound on accepted sequence numbers
    pub high_watermark: int,
}

/// Protocol constants
pub struct LConstants {
    /// Number of faulty nodes tolerated (f)
    pub f: int,
    /// Total number of replicas (must be >= 3f+1)
    pub n: int,
    /// This replica's ID
    pub node_id: int,
    /// Checkpoint interval (create checkpoint every K requests)
    pub checkpoint_interval: int,
}

} // verus!
