// Complete Acceptor Init example with both spec and exec
// Transpiler-generated exec code verified by Verus

use vstd::prelude::*;

verus! {
    // === SPEC TYPES AND PREDICATES ===

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

    // === EXEC TYPES ===

    pub struct CReplicaConstants {
        pub my_index: i64,
        pub num_replicas: i64,
    }

    impl CReplicaConstants {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.my_index >= 0
            &&& self.num_replicas > 0
        }
    }

    impl View for CReplicaConstants {
        type V = LReplicaConstants;

        open spec fn view(&self) -> LReplicaConstants {
            LReplicaConstants {
                my_index: self.my_index as int,
                num_replicas: self.num_replicas as int,
            }
        }
    }

    pub struct CAcceptor {
        pub my_index: i64,
        pub max_bal_seqno: i64,
        pub max_bal_proposer_id: i64,
        pub log_truncation_point: i64,
    }

    impl CAcceptor {
        pub open spec fn well_formed(&self) -> bool {
            true  // Could add bounds checks
        }
    }

    impl View for CAcceptor {
        type V = LAcceptor;

        open spec fn view(&self) -> LAcceptor {
            LAcceptor {
                my_index: self.my_index as int,
                max_bal_seqno: self.max_bal_seqno as int,
                max_bal_proposer_id: self.max_bal_proposer_id as int,
                log_truncation_point: self.log_truncation_point as int,
            }
        }
    }

    // === EXEC FUNCTION (transpiler-generated, manually verified) ===

    pub fn c_acceptor_init(c: &CReplicaConstants) -> (result: CAcceptor)
        requires
            c.well_formed(),
        ensures
            result.well_formed(),
            LAcceptorInit(result@, c@),
    {
        CAcceptor {
            my_index: c.my_index,
            max_bal_seqno: 0,
            max_bal_proposer_id: 0,
            log_truncation_point: 0,
        }
    }
}

fn main() {}
