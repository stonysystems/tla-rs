// Acceptor Init spec with nested Ballot struct
// Testing parser struct construction support

use vstd::prelude::*;

verus! {
    // Simplified types for testing
    pub struct Ballot {
        pub seqno: int,
        pub proposer_id: int,
    }

    pub struct LReplicaConstants {
        pub my_index: int,
        pub num_replicas: int,
    }

    pub struct LAcceptor {
        pub constants: LReplicaConstants,
        pub max_bal: Ballot,
        pub log_truncation_point: int,
    }

    // Init predicate using struct construction
    pub open spec fn LAcceptorInit(a: LAcceptor, c: LReplicaConstants) -> bool
    {
        &&& a.constants == c
        &&& a.max_bal == Ballot { seqno: 0, proposer_id: 0 }
        &&& a.log_truncation_point == 0
    }
}
