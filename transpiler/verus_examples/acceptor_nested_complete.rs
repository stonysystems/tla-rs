// Complete Acceptor Init with nested Ballot struct
// Tests transpiler's struct construction support

use vstd::prelude::*;

verus! {
    // === SPEC TYPES ===

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

    // Init predicate with nested struct construction
    pub open spec fn LAcceptorInit(a: LAcceptor, c: LReplicaConstants) -> bool
    {
        &&& a.constants == c
        &&& a.max_bal == Ballot { seqno: 0, proposer_id: 0 }
        &&& a.log_truncation_point == 0
    }

    // === EXEC TYPES ===

    pub struct CBallot {
        pub seqno: i64,
        pub proposer_id: i64,
    }

    impl CBallot {
        pub open spec fn well_formed(&self) -> bool {
            true
        }
    }

    impl View for CBallot {
        type V = Ballot;
        open spec fn view(&self) -> Ballot {
            Ballot {
                seqno: self.seqno as int,
                proposer_id: self.proposer_id as int,
            }
        }
    }

    pub struct CReplicaConstants {
        pub my_index: i64,
        pub num_replicas: i64,
    }

    impl CReplicaConstants {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.my_index >= 0
            &&& self.num_replicas > 0
        }

        pub fn clone_for_view(&self) -> (result: CReplicaConstants)
            ensures result@ == self@
        {
            CReplicaConstants {
                my_index: self.my_index,
                num_replicas: self.num_replicas,
            }
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
        pub constants: CReplicaConstants,
        pub max_bal: CBallot,
        pub log_truncation_point: i64,
    }

    impl CAcceptor {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.constants.well_formed()
            &&& self.max_bal.well_formed()
        }
    }

    impl View for CAcceptor {
        type V = LAcceptor;
        open spec fn view(&self) -> LAcceptor {
            LAcceptor {
                constants: self.constants@,
                max_bal: self.max_bal@,
                log_truncation_point: self.log_truncation_point as int,
            }
        }
    }

    // === EXEC FUNCTION (based on transpiler output) ===

    pub fn c_acceptor_init(c: &CReplicaConstants) -> (result: CAcceptor)
        requires
            c.well_formed(),
        ensures
            result.well_formed(),
            LAcceptorInit(result@, c@),
    {
        CAcceptor {
            constants: c.clone_for_view(),
            max_bal: CBallot {
                seqno: 0,
                proposer_id: 0,
            },
            log_truncation_point: 0,
        }
    }
}

fn main() {}
