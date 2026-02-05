use vstd::prelude::*;

verus! {
    /// Message types in the Paxos protocol
    pub enum LMsgType {
        Phase1a,
        Phase1b,
        Phase2a,
        Phase2b,
    }

    /// Single-Decree Paxos protocol state
    /// Uses a simplified set-based representation:
    /// - max_bal: set of ballot numbers that have been seen (promised)
    /// - max_v_bal: set of ballot numbers for which votes have been cast
    /// - max_val: set of values that have been accepted
    /// - msg_count: count of messages sent (monotonically increasing)
    pub struct LState {
        pub max_bal: Set<int>,
        pub max_v_bal: Set<int>,
        pub max_val: Set<int>,
        pub msg_count: int,
    }

    /// Protocol constants
    pub struct LConstants {
        pub acceptors: Set<int>,      // The set of all acceptors
        pub quorum_size: int,         // Minimum quorum size for consensus
    }
}
