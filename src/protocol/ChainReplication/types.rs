use vstd::prelude::*;

verus! {
    /// Role of a node in the chain
    pub enum LNodeRole {
        Head,           // Receives client writes, forwards to successor
        Middle,         // Receives from predecessor, forwards to successor
        Tail,           // Receives from predecessor, commits and serves reads
    }

    /// State of a single node in the chain replication protocol.
    /// Models one server's perspective: its local history, pending
    /// forwarded updates, and knowledge of committed state.
    pub struct LState {
        pub role: LNodeRole,            // This node's position in the chain
        pub history: Seq<int>,          // Sequence of values applied at this node
        pub pending_sent: Set<int>,     // Values forwarded to successor but not yet acked
        pub committed_count: int,       // Number of operations known to be committed
        pub obj_value: int,             // Last committed value (tail's view)
    }

    /// Protocol constants
    pub struct LConstants {
        pub node_id: int,               // This node's position index in the chain
        pub chain_len: int,             // Total number of nodes in the chain
    }
}
