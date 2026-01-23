// Complete LLearnerForgetDecision example with both spec and exec
// Tests: conditional with map.contains_key(), map.remove(), identity case
// Based on RSL learner.rs LLearnerForgetDecision predicate

use vstd::prelude::*;
use vstd::map::*;

verus! {
    // === SPEC TYPES ===

    pub type OperationNumber = int;

    pub struct Ballot {
        pub seqno: int,
        pub proposer_id: int,
    }

    pub struct LReplicaConstants {
        pub my_index: int,
    }

    // Simplified LearnerTuple
    pub struct LearnerTuple {
        pub candidate_value: int,  // Simplified from RequestBatch
    }

    pub type LearnerState = Map<OperationNumber, LearnerTuple>;

    pub struct LLearner {
        pub constants: LReplicaConstants,
        pub max_ballot_seen: Ballot,
        pub unexecuted_learner_state: LearnerState,
    }

    // === SPEC PREDICATE (from RSL learner.rs) ===

    pub open spec fn LLearnerForgetDecision(
        s: LLearner,
        s_: LLearner,
        opn: OperationNumber
    ) -> bool
    {
        if s.unexecuted_learner_state.contains_key(opn) {
            s_ == LLearner{
                constants: s.constants,
                max_ballot_seen: s.max_ballot_seen,
                unexecuted_learner_state: s.unexecuted_learner_state.remove(opn)
            }
        } else {
            s_ == s
        }
    }

    // === EXEC TYPES ===

    pub struct CBallot {
        pub seqno: i64,
        pub proposer_id: i64,
    }

    impl CBallot {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn clone_for_view(&self) -> (result: CBallot)
            ensures result@ == self@
        {
            CBallot { seqno: self.seqno, proposer_id: self.proposer_id }
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

    pub struct CLearnerTuple {
        pub candidate_value: i64,
    }

    impl CLearnerTuple {
        pub open spec fn well_formed(&self) -> bool { true }
    }

    impl View for CLearnerTuple {
        type V = LearnerTuple;
        open spec fn view(&self) -> LearnerTuple {
            LearnerTuple { candidate_value: self.candidate_value as int }
        }
    }

    // Concrete map wrapper with tracked ghost state
    // In Verus, we use tracked ghost variables to maintain the spec-level map
    pub struct CLearnerState {
        // The concrete storage - simplified as a single optional entry for demo
        // Real implementation would use a HashMap
        entries: Ghost<Map<OperationNumber, LearnerTuple>>,
    }

    impl CLearnerState {
        pub open spec fn well_formed(&self) -> bool { true }

        pub closed spec fn view_spec(&self) -> LearnerState {
            self.entries@
        }

        pub fn empty() -> (result: CLearnerState)
            ensures result@ == Map::<OperationNumber, LearnerTuple>::empty()
        {
            CLearnerState {
                entries: Ghost(Map::empty()),
            }
        }

        #[verifier::external_body]
        pub fn contains_key(&self, opn: i64) -> (result: bool)
            ensures result == self@.contains_key(opn as int)
        {
            // In real impl, would check actual HashMap
            // External body - implementation would use concrete data structure
            unimplemented!()
        }

        pub fn remove(&self, opn: i64) -> (result: CLearnerState)
            requires self@.contains_key(opn as int)
            ensures result@ == self@.remove(opn as int)
        {
            CLearnerState {
                entries: Ghost(self.entries@.remove(opn as int)),
            }
        }

        pub fn clone_for_view(&self) -> (result: CLearnerState)
            ensures result@ == self@
        {
            CLearnerState {
                entries: Ghost(self.entries@),
            }
        }
    }

    impl View for CLearnerState {
        type V = LearnerState;
        open spec fn view(&self) -> LearnerState {
            self.view_spec()
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

        pub fn clone_for_view(&self) -> (result: CLLearner)
            ensures result@ == self@
        {
            CLLearner {
                constants: self.constants.clone_for_view(),
                max_ballot_seen: self.max_ballot_seen.clone_for_view(),
                unexecuted_learner_state: self.unexecuted_learner_state.clone_for_view(),
            }
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

    pub fn c_learner_forget_decision(s: &CLLearner, opn: i64) -> (result: CLLearner)
        requires
            s.well_formed(),
        ensures
            result.well_formed(),
            LLearnerForgetDecision(s@, result@, opn as int),
    {
        if s.unexecuted_learner_state.contains_key(opn) {
            CLLearner {
                constants: s.constants.clone_for_view(),
                max_ballot_seen: s.max_ballot_seen.clone_for_view(),
                unexecuted_learner_state: s.unexecuted_learner_state.remove(opn),
            }
        } else {
            s.clone_for_view()
        }
    }
}

fn main() {}
