use vstd::prelude::*;

verus! {
    /// A command. Corresponds to jetpack.tla's `Commands == [cmd_id |-> id, key |-> k]`.
    pub struct Command {
        pub cmd_id: int,
        pub key: int,
    }

    /// Recovery-state-machine phase for this replica.
    ///
    /// Slice (jstate option B): relative to the original 6 states, the trailing
    /// `AfterResubmit` is dropped (it pulls in client/execution, out of slice);
    /// `AfterAccept` returns directly to `Ready`.
    ///
    ///   Ready -> Recovery -> AfterBeginRecovery -> AfterPrepare -> AfterAccept -> (back to Ready)
    pub enum LJState {
        Ready,               // Normal operation, not in recovery
        Recovery,            // Recovery triggered, BeginRecovery issued
        AfterBeginRecovery,  // BeginRecovery responses collected
        AfterPrepare,        // Prepare phase done (promise quorum reached)
        AfterAccept,         // Accept phase done (accept quorum reached), then back to Ready
    }

    /// Local state of a single Jetpack replica during recovery (single-process
    /// view, no `[i]`).
    ///
    /// Slice boundary: fixed membership + single value + base as a contract +
    /// no client/execution. Every field is "this replica's own"; cross-replica
    /// information only arrives via messages (action parameters).
    pub struct LState {
        // ---- Recovery state machine ----
        pub jstate: LJState,              // Current recovery phase
        pub jepoch: int,                  // Ballot this replica uses to drive recovery (proposer side)

        // ---- Acceptor triple (corresponds to jetpack.tla's jpool fields) ----
        pub max_seen_ballot: int,         // jpool.max_seen_ballot: highest ballot promised
        pub accepted_ballot: int,         // jpool.accepted_ballot: ballot of last accept (0 if none)
        pub accepted_value: Set<Command>, // jpool.accepted_value: last accepted value

        // ---- Proposer / recovery-coordinator side ----
        pub recovery_set: Set<int>,       // Replica ids participating in this recovery
        pub prep_rcvd: Set<int>,          // Replica ids that returned a Prepare response (for counting)
        pub accept_rcvd: Set<int>,        // Replica ids that returned an Accept response (for counting)
        pub chosen_value: Set<Command>,   // Value selected / to be proposed in the Accept phase

        // ---- Prepare-phase value selection (online aggregation, Paxos-style) ----
        pub highest_seen_ballot: int,         // Highest accepted_ballot seen across Prepare responses
        pub highest_seen_value: Set<Command>, // Value from that highest-ballot promise
    }

    /// Protocol constants (fixed-membership slice).
    pub struct LConstants {
        pub replicas: Set<int>,           // All replica ids (fixed membership, unchanging)
        pub quorum_size: int,             // Majority threshold (count-based, not SUBSET powerset)
        pub my_id: int,                   // This replica's id
    }
}
