use vstd::prelude::*;

verus! {
    /// Role of a node in the CRAQ chain
    pub enum LNodeRole {
        Head,           // Receives client writes, forwards to successor, serves clean reads or queries tail
        Middle,         // Receives from predecessor, forwards to successor, serves clean reads or queries tail
        Tail,           // Receives from predecessor, commits, serves reads and version queries
    }

    /// CRAQ network messages
    pub enum LCraqMessage {
        Forward { version: int, value: int },
        Ack { version: int, value: int },
        VersionQuery { requester: int },
        VersionReply { requester: int, version: int },
    }

    /// State of a single node in the CRAQ protocol.
    /// Unlike standard Chain Replication, CRAQ nodes store multiple versions
    /// (clean and dirty) and allow reads from any node in the chain.
    pub struct LState {
        pub role: LNodeRole,            // This node's position in the chain
        pub history: Seq<int>,          // Sequence of values applied at this node (version i is at index i - 1)
        pub pending_sent: Set<int>,     // Dirty versions forwarded/stored but not yet acked by tail
        pub clean_version: int,         // Highest version known to be clean (committed by tail)
        pub latest_version: int,        // Latest version stored at this node (== history.len())
        pub obj_value: int,             // Value at clean_version
        // Topology fields
        pub has_predecessor: bool,      // Whether this node has a predecessor
        pub predecessor: int,           // Predecessor node ID (valid when has_predecessor)
        pub has_successor: bool,        // Whether this node has a successor
        pub successor: int,             // Successor node ID (valid when has_successor)
        pub alive: bool,                // Whether this node is alive
    }

    /// Protocol constants
    pub struct LConstants {
        pub node_id: int,               // This node's position index in the chain
        pub chain_len: int,             // Total number of nodes in the chain
    }
}
