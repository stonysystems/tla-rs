use vstd::prelude::*;

verus! {
    /// Transaction Manager state
    pub enum LTMState {
        Init,
        Committed,
        Aborted,
    }

    /// Global Two-Phase Commit protocol state
    pub struct LState {
        pub rm_state: Set<int>,       // Set of resource managers that have prepared
        pub tm_state: LTMState,       // Transaction manager state
        pub tm_prepared: Set<int>,    // Set of RMs the TM knows have prepared
    }

    /// Protocol constants
    pub struct LConstants {
        pub rm: Set<int>,             // The set of all resource managers
    }
}
