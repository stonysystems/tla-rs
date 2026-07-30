use vstd::prelude::*;

verus! {
    /// Server role in the Raft protocol
    pub enum LServerRole {
        Follower,
        Candidate,
        Leader,
    }

    /// Executable representation of a Raft server configuration.
    ///
    /// The sequence can be converted to a mathematical set for
    /// quorum reasoning in refinement proofs.
    pub struct LMembershipConfig {
        pub servers: Seq<int>,
    }

    /// Executable representation of a membership phase.
    ///
    /// Stable uses one configuration. Joint temporarily carries
    /// both the old and new configurations.
    pub enum LMembershipPhase {
        Stable {
            config: LMembershipConfig,
        },
        Joint {
            old_config: LMembershipConfig,
            new_config: LMembershipConfig,
        },
    }

    /// Mathematical membership phase used by quorum and provenance
    /// proofs. It lives with the dependency-neutral Raft datatypes so
    /// protocol state can remember the phase used for an election.
    pub enum MembershipPhase {
        Stable {
            config: Set<int>,
        },
        Joint {
            old_config: Set<int>,
            new_config: Set<int>,
        },
    }

    /// Mathematical set view of the executable membership sequence.
    pub open spec fn membership_config_view(
        config: LMembershipConfig,
    ) -> Set<int> {
        config.servers.to_set()
    }

    /// Interpret an executable configuration as a stable proof phase.
    pub open spec fn stable_phase_from_config(
        config: LMembershipConfig,
    ) -> MembershipPhase {
        MembershipPhase::Stable {
            config: membership_config_view(config),
        }
    }

    /// Convert an executable membership phase into the mathematical
    /// phase used by quorum and provenance proofs.
    pub open spec fn membership_phase_view(
        phase: LMembershipPhase,
    ) -> MembershipPhase {
        match phase {
            LMembershipPhase::Stable {
                config,
            } => {
                MembershipPhase::Stable {
                    config: membership_config_view(config),
                }
            },
            LMembershipPhase::Joint {
                old_config,
                new_config,
            } => {
                MembershipPhase::Joint {
                    old_config: membership_config_view(old_config),
                    new_config: membership_config_view(new_config),
                }
            },
        }
    }

    /// A value that can be replicated through the Raft log.
    ///
    /// Ordinary data commands retain their integer value, while
    /// configuration entries carry a membership phase.
    pub enum LLogValue {
        Data {
            value: int,
        },
        Configuration {
            phase: LMembershipPhase,
        },
    }

    /// A replicated Raft log entry.
    ///
    /// `value` preserves the existing application-level refinement,
    /// while `payload` distinguishes ordinary data from membership
    /// configurations as the protocol is extended.
    pub struct LLogEntry {
        pub term: int,
        pub value: int,
        pub payload: LLogValue,
    }

    /// Raft protocol messages
    pub enum LRaftMessage {
        RequestVote { term: int, candidate: int, last_log_index: int, last_log_term: int },
        VoteResponse { term: int, granted: bool, voter: int, voter_last_log_index: int, voter_last_log_term: int },
        AppendEntries {
            term: int,
            leader: int,
            prev_index: int,
            prev_term: int,
            value: int,
            payload: LLogValue,
            has_entry: bool,
            leader_commit: int,
        },
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

        // Configuration whose quorum elected the current leader.
        // None before this server has completed an election.
        pub election_membership_phase: Option<MembershipPhase>,

        // Leader state (u64 keys/values match HashMap<u64, u64> View)
        pub match_index: Map<u64, u64>, // For each server, index of highest known replicated entry
        pub next_index: Map<u64, u64>,  // For each server, index of next log entry to send
    }

    /// A routed Raft message with sender and receiver information.
    /// Used in the distributed-level network model (RaftDistributedState.network)
    /// to track message provenance for safety proofs.
    pub struct LRaftPacket {
        pub src: int,           // Sending server ID
        pub dst: int,           // Destination server ID
        pub msg: LRaftMessage,  // The message payload
    }

    /// Protocol constants
    pub struct LConstants {
        pub servers: Set<int>,          // The set of all server IDs
        pub quorum_size: int,           // Majority threshold: |servers|/2 + 1
        pub my_id: int,                 // This server's own ID
    }
}
