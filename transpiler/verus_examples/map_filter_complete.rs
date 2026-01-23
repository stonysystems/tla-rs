// Test for spec predicates with quantifiers over map domains
// Tests: map filtering (retain entries where key >= threshold)
// This is the pattern used in LLearnerForgetOperationsBefore

use vstd::prelude::*;
use vstd::map::*;

verus! {
    // === SPEC TYPES ===

    pub type OperationNumber = int;

    pub struct LearnerTuple {
        pub value: int,
    }

    pub type LearnerState = Map<OperationNumber, LearnerTuple>;

    // === SPEC PREDICATE ===
    // Pattern: filter map to retain only entries with key >= threshold

    pub open spec fn MapFilteredByKey(
        s: LearnerState,
        s_: LearnerState,
        threshold: OperationNumber
    ) -> bool
    {
        &&& (forall |k: OperationNumber| s_.contains_key(k) <==> k >= threshold && s.contains_key(k))
        &&& (forall |k: OperationNumber| s_.contains_key(k) ==> s_[k] == s[k])
    }

    // === EXEC TYPES ===

    // Simple HashMap wrapper
    use std::collections::HashMap;

    pub struct CLearnerState {
        // Using ghost state for verification
        // Real impl would use HashMap<i64, CLearnerTuple>
        pub ghost_state: Ghost<LearnerState>,
    }

    impl CLearnerState {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn empty() -> (result: CLearnerState)
            ensures result@ == Map::<OperationNumber, LearnerTuple>::empty()
        {
            CLearnerState { ghost_state: Ghost(Map::empty()) }
        }

        // Filter map to retain only keys >= threshold
        #[verifier::external_body]
        pub fn filter_by_threshold(&self, threshold: i64) -> (result: CLearnerState)
            ensures MapFilteredByKey(self@, result@, threshold as int)
        {
            // In real impl, would iterate HashMap and filter
            unimplemented!()
        }

        pub fn clone_for_view(&self) -> (result: CLearnerState)
            ensures result@ == self@
        {
            CLearnerState { ghost_state: Ghost(self.ghost_state@) }
        }
    }

    impl View for CLearnerState {
        type V = LearnerState;
        open spec fn view(&self) -> LearnerState {
            self.ghost_state@
        }
    }

    // === EXEC FUNCTION ===
    // Demonstrates how map filtering predicates can be implemented

    pub struct CState {
        pub learner_state: CLearnerState,
        pub other_field: i64,
    }

    impl CState {
        pub open spec fn well_formed(&self) -> bool {
            self.learner_state.well_formed()
        }

        pub fn clone_for_view(&self) -> (result: CState)
            ensures result@ == self@
        {
            CState {
                learner_state: self.learner_state.clone_for_view(),
                other_field: self.other_field,
            }
        }
    }

    impl View for CState {
        type V = (LearnerState, int);  // Simplified view
        open spec fn view(&self) -> (LearnerState, int) {
            (self.learner_state@, self.other_field as int)
        }
    }

    // Simplified predicate matching LLearnerForgetOperationsBefore pattern
    pub open spec fn LForgetBefore(
        s: (LearnerState, int),
        s_: (LearnerState, int),
        threshold: OperationNumber
    ) -> bool
    {
        &&& MapFilteredByKey(s.0, s_.0, threshold)
        &&& s_.1 == s.1
    }

    pub fn c_forget_before(s: &CState, threshold: i64) -> (result: CState)
        requires
            s.well_formed(),
        ensures
            result.well_formed(),
            LForgetBefore(s@, result@, threshold as int),
    {
        CState {
            learner_state: s.learner_state.filter_by_threshold(threshold),
            other_field: s.other_field,
        }
    }
}

fn main() {}
