use vstd::prelude::*;

verus! {
    /// Reconfigurable Paxos (Vertical Paxos) state.
    ///
    /// Extends single-decree Paxos with a configuration number
    /// that tracks the current configuration (set of acceptors).
    /// Reconfiguration is modeled as moving to a higher config number,
    /// requiring the old config's quorum to agree on the transition.
    pub struct LState {
        pub config_num: int,          // Current configuration number
        pub max_bal: int,             // Highest ballot promised
        pub max_v_bal: int,           // Highest ballot voted for
        pub max_val: int,             // Value voted for at max_v_bal
        pub has_voted: bool,          // Whether this node has voted
        pub is_active: bool,          // Whether this node is active in current config
        // Quorum and commit tracking
        pub promises_rcvd: Set<int>,  // Set of nodes that sent promises
        pub accepts_rcvd: Set<int>,   // Set of nodes that accepted
        pub committed: bool,          // Whether value is committed
        pub committed_val: int,       // Committed value
        // Witness/sync state
        pub witness_val: int,         // Value carried by witness from old config
        pub has_witness: bool,        // Whether a witness value has been received
        // Message flags
        pub msgs_prepare: bool,       // A prepare message is pending
        pub msgs_prepare_bal: int,    // Ballot of prepare message
        pub msgs_promise: bool,       // A promise message is pending
        pub msgs_promise_bal: int,    // Ballot of promise
        pub msgs_promise_v_bal: int,  // Accepted ballot in promise
        pub msgs_promise_val: int,    // Accepted value in promise
        pub msgs_accept: bool,        // An accept message is pending
        pub msgs_accept_bal: int,     // Ballot of accept
        pub msgs_accept_val: int,     // Value of accept
    }

    /// Protocol constants
    pub struct LConstants {
        pub quorum_size: int,         // Quorum size for current configuration
        pub num_nodes: int,           // Total number of nodes in cluster
        pub node_id: int,             // This node's ID
    }
}
