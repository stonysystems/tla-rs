/// EPaxos (Egalitarian Paxos) types.
///
/// Models the core EPaxos concepts from a single replica's perspective:
/// - Leaderless: any replica can propose commands
/// - Commands go through phases: PreAccepted -> Accepted -> Committed -> Executed
/// - Fast path (1 RTT) when quorum agrees on dependencies
/// - Slow path (2 RTT) when dependency conflict detected
/// - Set-based quorum tracking for pre-accept and accept phases
/// - Messages modeled as sent_packets output parameter
/// - Dependency tracking via dep_count and sequence numbers
use vstd::prelude::*;
use vstd::set::*;

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
    /// Whether this replica initiated the current proposal
    pub is_leader: bool,
    /// Total number of instances committed by this replica
    pub committed_count: int,
    /// Total number of instances executed by this replica
    pub executed_count: int,
    /// Set of replicas that sent PreAcceptOk (fast path quorum tracking)
    pub preaccept_senders: Set<int>,
    /// Set of replicas that sent AcceptOk (slow path quorum tracking)
    pub accept_senders: Set<int>,
    /// Whether any PreAcceptOk disagreed on deps (conflict flag)
    pub has_conflict: bool,
    /// Maximum sequence number seen from PreAcceptOk responses
    pub max_resp_seq: int,
}

/// Protocol constants
pub struct LConstants {
    /// Total number of replicas (must be odd, >= 3)
    pub num_replicas: int,
    /// Fast-path quorum size: floor(n/2) + floor((n/2 + 1)/2)
    pub fast_quorum_size: int,
    /// Slow-path quorum size: majority (n/2 + 1)
    pub quorum_size: int,
    /// This replica's ID
    pub my_id: int,
}

/// EPaxos protocol messages.
pub enum LEPaxosMessage {
    PreAccept { ballot: int, cmd: int, seq: int },
    PreAcceptOk { sender: int, seq: int, conflict: bool },
    Accept { ballot: int, cmd: int, seq: int },
    AcceptOk { sender: int },
    Commit { cmd: int, seq: int },
}

} // verus!
