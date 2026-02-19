use vstd::prelude::*;

verus! {
    /// Two-Phase Commit protocol message types
    pub enum LTPCMessage {
        Prepare,
        PreparedVote { rm: int },
        Commit,
        Abort,
    }

    /// Transaction Manager state
    pub enum LTMState {
        Init,
        Committed,
        Aborted,
    }

    /// Resource Manager state
    pub enum LRMState {
        Working,
        Prepared,
        Committed,
        Aborted,
    }

    /// Global Two-Phase Commit protocol state
    pub struct LState {
        pub tm_state: LTMState,           // Transaction manager state
        pub tm_prepared: Set<int>,        // Set of RMs the TM knows have prepared
        pub rm_prepared: Set<int>,        // RMs that have entered Prepared state
        pub rm_committed: Set<int>,       // RMs that have committed
        pub rm_aborted: Set<int>,         // RMs that have aborted
    }

    /// Protocol constants
    pub struct LConstants {
        pub rm: Set<int>,                 // The set of all resource managers
    }
}
