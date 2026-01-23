// Complete LLearner Init example with both spec and exec
// Tests: struct literal equality, Map::empty()
// Based on RSL learner.rs LLearnerInit predicate

use vstd::prelude::*;
use vstd::map::*;

verus! {
    // === SPEC TYPES ===

    // Type aliases for clarity
    pub type OperationNumber = int;

    pub struct Ballot {
        pub seqno: int,
        pub proposer_id: int,
    }

    pub struct Request {
        pub client: int,  // Simplified from AbstractEndPoint
        pub seqno: int,
    }

    pub type RequestBatch = Seq<Request>;

    pub struct LearnerTuple {
        pub received_2b_message_senders: Set<int>,  // Simplified
        pub candidate_learned_value: RequestBatch,
    }

    pub type LearnerState = Map<OperationNumber, LearnerTuple>;

    pub struct LReplicaConstants {
        pub my_index: int,
    }

    pub struct LLearner {
        pub constants: LReplicaConstants,
        pub max_ballot_seen: Ballot,
        pub unexecuted_learner_state: LearnerState,
    }

    // === SPEC PREDICATE (from RSL learner.rs) ===

    pub open spec fn LLearnerInit(l: LLearner, c: LReplicaConstants) -> bool
    {
        &&& l.constants == c
        &&& l.max_ballot_seen == Ballot{seqno: 0, proposer_id: 0}
        &&& l.unexecuted_learner_state == Map::<OperationNumber, LearnerTuple>::empty()
    }

    // === EXEC TYPES ===

    pub struct CBallot {
        pub seqno: i64,
        pub proposer_id: i64,
    }

    impl CBallot {
        pub open spec fn well_formed(&self) -> bool { true }
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
    }

    impl CReplicaConstants {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn clone_for_view(&self) -> (result: CReplicaConstants)
            ensures result@ == self@
        {
            CReplicaConstants { my_index: self.my_index }
        }
    }

    impl View for CReplicaConstants {
        type V = LReplicaConstants;
        open spec fn view(&self) -> LReplicaConstants {
            LReplicaConstants { my_index: self.my_index as int }
        }
    }

    // Simplified - in real code this would be a proper HashMap wrapper
    pub struct CLearnerState {
        // Using a simple empty marker for now
        // Real implementation would wrap HashMap<i64, CLearnerTuple>
    }

    impl CLearnerState {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn empty() -> (result: CLearnerState)
            ensures result@ == Map::<OperationNumber, LearnerTuple>::empty()
        {
            CLearnerState {}
        }
    }

    impl View for CLearnerState {
        type V = LearnerState;
        open spec fn view(&self) -> LearnerState {
            Map::<OperationNumber, LearnerTuple>::empty()
        }
    }

    pub struct CLLearner {
        pub constants: CReplicaConstants,
        pub max_ballot_seen: CBallot,
        pub unexecuted_learner_state: CLearnerState,
    }

    impl CLLearner {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.constants.well_formed()
            &&& self.max_ballot_seen.well_formed()
            &&& self.unexecuted_learner_state.well_formed()
        }
    }

    impl View for CLLearner {
        type V = LLearner;
        open spec fn view(&self) -> LLearner {
            LLearner {
                constants: self.constants@,
                max_ballot_seen: self.max_ballot_seen@,
                unexecuted_learner_state: self.unexecuted_learner_state@,
            }
        }
    }

    // === EXEC FUNCTION (transpiler-generated pattern) ===

    pub fn c_learner_init(c: &CReplicaConstants) -> (result: CLLearner)
        requires
            c.well_formed(),
        ensures
            result.well_formed(),
            LLearnerInit(result@, c@),
    {
        CLLearner {
            constants: c.clone_for_view(),
            max_ballot_seen: CBallot {
                seqno: 0,
                proposer_id: 0,
            },
            unexecuted_learner_state: CLearnerState::empty(),
        }
    }
}

fn main() {}
