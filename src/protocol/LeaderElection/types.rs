use vstd::prelude::*;

verus! {
    /// Node state in the Bully Leader Election protocol
    pub enum LNodeState {
        Normal,      // Not participating in election
        Election,    // Currently running an election
        Leader,      // Elected as leader
    }

    /// Global protocol state for Bully Leader Election
    /// Uses boolean flags (has_leader, has_highest) to avoid sentinel values
    pub struct LState {
        pub electing: Set<int>,       // Set of nodes currently in election
        pub has_leader: bool,         // Whether there is a current leader
        pub leader: int,              // Current leader ID (valid only if has_leader)
        pub alive: Set<int>,          // Set of alive nodes
        pub has_highest: bool,        // Whether any node has been heard
        pub highest_heard: int,       // Highest node ID heard (valid only if has_highest)
    }

    /// Protocol constants
    pub struct LConstants {
        pub nodes: Set<int>,          // The set of all node IDs
        pub num_nodes: int,           // Total number of nodes
    }
}
