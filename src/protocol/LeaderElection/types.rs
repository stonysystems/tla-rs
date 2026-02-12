use vstd::prelude::*;

verus! {
    /// Node state in the Bully Leader Election protocol
    pub enum LNodeState {
        Normal,      // Not participating in election
        Election,    // Currently running an election
        Leader,      // Elected as leader
    }

    /// Global protocol state for Bully Leader Election
    /// Uses boolean flags for messages and state tracking
    pub struct LState {
        pub electing: Set<int>,       // Set of nodes currently in election
        pub has_leader: bool,         // Whether there is a current leader
        pub leader: int,              // Current leader ID (valid only if has_leader)
        pub alive: Set<int>,          // Set of alive nodes
        pub has_highest: bool,        // Whether any node has been heard
        pub highest_heard: int,       // Highest node ID heard (valid only if has_highest)
        // Message flags for Bully algorithm
        pub msgs_election: bool,      // An Election message is pending
        pub msgs_election_sender: int, // Sender of the Election message
        pub msgs_answer: bool,        // An Answer message is pending
        pub msgs_answer_responder: int, // Responder in the Answer message
        pub msgs_coordinator: bool,   // A Coordinator message is pending
        pub msgs_coordinator_leader: int, // Leader announced in Coordinator
        // Election timeout tracking
        pub waiting_answer: bool,     // Node is waiting for an Answer
        pub waiting_node: int,        // Which node is waiting for Answer
    }

    /// Protocol constants
    pub struct LConstants {
        pub nodes: Set<int>,          // The set of all node IDs
        pub num_nodes: int,           // Total number of nodes
    }
}
