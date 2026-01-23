// Simplified Acceptor Init spec for transpiler testing
// Using flat struct (no nested fields) to work with current transpiler

use vstd::prelude::*;

verus! {
    pub struct LReplicaConstants {
        pub my_index: int,
        pub num_replicas: int,
    }

    // Flattened acceptor struct (no nested Ballot struct)
    pub struct LAcceptor {
        pub my_index: int,
        pub max_bal_seqno: int,
        pub max_bal_proposer_id: int,
        pub log_truncation_point: int,
    }

    // Simple init predicate with flat struct
    pub open spec fn LAcceptorInit(a: LAcceptor, c: LReplicaConstants) -> bool
    {
        &&& a.my_index == c.my_index
        &&& a.max_bal_seqno == 0
        &&& a.max_bal_proposer_id == 0
        &&& a.log_truncation_point == 0
    }
}
