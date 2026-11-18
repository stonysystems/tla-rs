use crate::implementation::RSL::cconstants::*;
use crate::implementation::RSL::types_i::*;
use crate::protocol::RSL::learner::*;
use vstd::prelude::*;

verus! {
pub struct CLearner {
    pub constants: CReplicaConstants,
    pub max_ballot_seen: CBallot,
    pub unexecuted_learner_state: CLearnerState,
}

impl CLearner {

    /// Every hash table in the struct is well formed (always true on vstd
    /// releases without hash-table well-formedness; see hash_wf.rs).
    pub open spec fn hash_tables_ok(&self) -> bool {
        clearnerstate_hash_tables_ok(&self.unexecuted_learner_state)
    }

    pub open spec fn abstractable(self) -> bool {
        &&& self.constants.abstractable()
        &&& self.max_ballot_seen.abstractable()
        &&& clearnerstate_is_abstractable(&self.unexecuted_learner_state)
    }

    pub open spec fn valid(&self) -> bool {
        &&& self.abstractable()
        &&& self.constants.valid()
        &&& self.max_ballot_seen.valid()
        &&& clearnerstate_is_valid(&self.unexecuted_learner_state)
        &&& self.hash_tables_ok()
    }

    pub fn clone_up_to_view(&self) -> (res: CLearner)
    ensures
        self.hash_tables_ok() ==> res@ == self@,
        self.hash_tables_ok() ==> res.valid() == self.valid(),
    {
        let constants_clone = self.constants.clone();
        let state_clone = clone_clearnerstate_up_to_view(&self.unexecuted_learner_state);
        CLearner {
            constants: constants_clone,
            max_ballot_seen: self.max_ballot_seen, // CBallot is Copy
            unexecuted_learner_state: state_clone,
        }
    }
}

impl Clone for CLearner {
    fn clone(&self) -> (result: Self)
    ensures
        self.hash_tables_ok() ==> result@ == self@,
        self.hash_tables_ok() ==> result.valid() == self.valid(),
    {
        self.clone_up_to_view()
    }
}

impl View for CLearner {
    type V = LLearner;

    open spec fn view(&self) -> LLearner {
        LLearner {
            constants: self.constants@,
            max_ballot_seen: self.max_ballot_seen@,
            unexecuted_learner_state: abstractify_clearnerstate(&self.unexecuted_learner_state),
        }
    }
}
}
