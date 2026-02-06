/// Simplified EPaxos (Egalitarian Paxos) types.
///
/// Models the core EPaxos concepts from a single replica's perspective:
/// - Leaderless: any replica can propose commands
/// - Commands go through phases: PreAccepted -> Accepted -> Committed -> Executed
/// - Fast path (1 RTT) when quorum agrees on dependencies
/// - Slow path (2 RTT) when dependency conflict detected
/// - Dependency tracking via sequence numbers and dependency counts
///
/// Simplified from the full EPaxos TLA+ spec by abstracting dependency sets
/// to counts and sequence numbers, similar to how PBFT uses message counts.
use vstd::prelude::*;

verus! {

/// Phase of a command instance in the EPaxos protocol
pub enum LInstancePhase {
    /// Empty slot, no command proposed yet
    Empty,
    /// Fast path: proposed with deps, waiting for quorum agreement
    PreAccepted,
    /// Slow path: running Paxos-like accept phase with resolved deps
    Accepted,
    /// Command is committed (deps are final)
    Committed,
    /// Command has been executed
    Executed,
}

/// State of a single EPaxos replica
pub struct LState {
    /// Ballot number for this replica's current leadership epoch
    pub ballot: int,
    /// Current command instance phase
    pub phase: LInstancePhase,
    /// The command value for the current instance
    pub cmd: int,
    /// Sequence number assigned to current instance (for ordering)
    pub seq: int,
    /// Number of dependency conflicts detected for current instance
    pub dep_count: int,
    /// Number of pre-accept acknowledgments received (fast path)
    pub preaccept_count: int,
    /// Number of accept acknowledgments received (slow path)
    pub accept_count: int,
    /// Whether this replica initiated the current proposal
    pub is_leader: bool,
    /// Total number of instances committed by this replica
    pub committed_count: int,
    /// Total number of instances executed by this replica
    pub executed_count: int,
}

/// Protocol constants
pub struct LConstants {
    /// Total number of replicas (must be odd, >= 3)
    pub num_replicas: int,
    /// Fast-path quorum size: floor(n/2) + floor((n/2 + 1)/2)
    /// For n=5: floor(5/2) + floor(3/2) = 2 + 1 = 3 (fast quorum = n-1 for n=5)
    /// Simplified: fast quorum needs n - 1 agreement for n = 2f+1
    pub fast_quorum_size: int,
    /// Slow-path quorum size: majority (n/2 + 1)
    pub quorum_size: int,
    /// This replica's ID
    pub my_id: int,
}

} // verus!
