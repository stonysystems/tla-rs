use crate::implementation::RSL::cconstants::*;
use crate::implementation::RSL::types_i::*;
use crate::protocol::RSL::learner::*;
use std::sync::Arc;
use vstd::prelude::*;

verus! {
pub struct CLearner {
    pub constants: CReplicaConstants,
    pub max_ballot_seen: CBallot,
    pub unexecuted_learner_state: Arc<CLearnerState>,
}

impl CLearner {
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
    }

    pub fn clone_up_to_view(&self) -> (res: CLearner)
    ensures
        res@ == self@,
        res.valid() == self.valid(),
    {
        let constants_clone = self.constants.clone();
        let state_clone = clone_arc_learner_state(&self.unexecuted_learner_state);
        CLearner {
            constants: constants_clone,
            max_ballot_seen: self.max_ballot_seen, // CBallot is Copy
            unexecuted_learner_state: state_clone,
        }
    }
}

/// Arc-backed shallow clone for unexecuted_learner_state. Refcount bump only.
#[verifier::external_body]
pub fn clone_arc_learner_state(v: &Arc<CLearnerState>) -> (res: Arc<CLearnerState>)
    ensures
        res@ == v@,
{
    Arc::clone(v)
}

impl Clone for CLearner {
    fn clone(&self) -> (result: Self)
    ensures
        result@ == self@,
        result.valid() == self.valid(),
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
