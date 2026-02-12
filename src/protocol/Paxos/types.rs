use vstd::prelude::*;

verus! {
    /// Phase of the protocol from this node's perspective
    pub enum LPhase {
        Idle,
        Phase1,
        Phase2,
        Decided,
    }

    /// Single-Decree Paxos protocol state
    /// Models a single acceptor + proposer combined node perspective.
    /// Ballot numbers are plain integers (higher = more recent).
    pub struct LState {
        // Acceptor state
        pub promised_bal: int,            // Highest ballot number promised
        pub accepted_bal: int,            // Ballot number of last accepted value
        pub accepted_val: int,            // Last accepted value (valid when accepted_bal > 0)

        // Proposer state
        pub proposer_bal: int,            // This proposer's current ballot
        pub phase: LPhase,               // Current protocol phase
        pub promises_rcvd: Set<int>,      // Set of acceptors that sent promises
        pub highest_accepted_bal: int,    // Highest accepted ballot seen in promises
        pub highest_accepted_val: int,    // Value from highest accepted ballot in promises
        pub proposed_val: int,            // Value proposed in Phase 2

        // Learner state
        pub accepts_rcvd: Set<int>,       // Set of acceptors that accepted current value
        pub decided_val: int,             // Decided value (valid when phase is Decided)
    }

    /// Protocol constants
    pub struct LConstants {
        pub acceptors: Set<int>,          // The set of all acceptors
        pub quorum_size: int,             // Minimum quorum size for consensus
        pub node_id: int,                 // This node's identifier
    }
}
