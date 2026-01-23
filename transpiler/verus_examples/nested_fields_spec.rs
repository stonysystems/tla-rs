// Test nested field assignment translation
// Uses a.max_bal.seqno == 0 style (nested field assignments)

use vstd::prelude::*;

verus! {
    pub struct Ballot {
        pub seqno: int,
        pub proposer_id: int,
    }

    pub struct LReplicaConstants {
        pub my_index: int,
    }

    pub struct LAcceptor {
        pub constants: LReplicaConstants,
        pub max_bal: Ballot,
        pub log_truncation_point: int,
    }

    // Init predicate using NESTED field assignments
    pub open spec fn LAcceptorInit(a: LAcceptor, c: LReplicaConstants) -> bool
    {
        &&& a.constants == c
        &&& a.max_bal.seqno == 0
        &&& a.max_bal.proposer_id == 0
        &&& a.log_truncation_point == 0
    }
}
