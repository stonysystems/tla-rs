use vstd::prelude::*;

verus! {
    /// Server role in the Raft protocol
    pub enum LServerRole {
        Follower,
        Candidate,
        Leader,
    }

    /// A log entry: term in which the entry was created, and the command value
    pub struct LLogEntry {
        pub term: int,
        pub value: int,
    }

    /// Raft protocol messages
    pub enum LRaftMessage {
        RequestVote { term: int, candidate: int, last_log_index: int, last_log_term: int },
        VoteResponse { term: int, granted: bool, voter: int },
        AppendEntries { term: int, leader: int, prev_index: int, prev_term: int, value: int, has_entry: bool, leader_commit: int },
        AppendResponse { term: int, success: bool, match_index: int, follower: int },
    }

    /// Raft protocol state (single-server perspective)
    /// Models the core state needed for leader election + log replication.
    /// Per-server state variables from the TLA+ spec are represented as
    /// properties of a single server interacting with abstract vote/append responses.
    pub struct LState {
        // Persistent state (on all servers)
        pub current_term: int,          // Latest term this server has seen
        pub role: LServerRole,          // Current role: Follower, Candidate, or Leader
        pub has_voted: bool,            // Whether this server has voted in current term
        pub voted_for: int,             // CandidateId that received vote (valid if has_voted)
        pub log: Seq<LLogEntry>,        // Log entries

        // Volatile state (on all servers)
        pub commit_index: int,          // Index of highest log entry known to be committed

        // Candidate state
        pub votes_granted: Set<int>,    // Set of servers that granted vote to this candidate

        // Leader state (u64 keys/values match HashMap<u64, u64> View)
        pub match_index: Map<u64, u64>, // For each server, index of highest known replicated entry
        pub next_index: Map<u64, u64>,  // For each server, index of next log entry to send
    }

    /// Protocol constants
    pub struct LConstants {
        pub servers: Set<int>,          // The set of all server IDs
        pub quorum_size: int,           // Majority threshold: |servers|/2 + 1
        pub my_id: int,                 // This server's own ID
    }
}
