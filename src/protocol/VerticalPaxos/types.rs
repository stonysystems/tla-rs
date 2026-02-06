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
    }

    /// Protocol constants
    pub struct LConstants {
        pub quorum_size: int,         // Quorum size for current configuration
        pub num_nodes: int,           // Total number of nodes in cluster
    }
}
