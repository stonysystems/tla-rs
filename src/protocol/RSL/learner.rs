use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::broadcast::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::message::*;
use crate::protocol::RSL::state_machine::*;
use crate::services::RSL::app_state_machine::*;
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;

verus! {
    pub struct LLearner {
        pub constants:LReplicaConstants,
        pub max_ballot_seen:Ballot,
        pub unexecuted_learner_state:LearnerState
    }

    pub open spec fn LLearnerInit(l:LLearner, c:LReplicaConstants) -> bool
    {
      &&& l.constants == c
      &&& l.max_ballot_seen == Ballot{seqno:0, proposer_id:0}
      &&& l.unexecuted_learner_state == Map::<OperationNumber, LearnerTuple>::empty()
    }

    pub open spec fn LLearnerProcess2b(
        s:LLearner, 
        s_:LLearner, 
        packet:RslPacket
    ) -> bool 
        recommends 
            packet.msg is RslMessage2b,
    {
        let m = packet.msg;
        let opn = m->opn_2b;
        if !s.constants.all.config.replica_ids.contains(packet.src) || BalLt(m->bal_2b, s.max_ballot_seen) {
            s_ == s 
        } else if BalLt(s.max_ballot_seen, m->bal_2b) {
            let tup_ = LearnerTuple{received_2b_message_senders:set![packet.src], candidate_learned_value:m->val_2b};
            s_ == LLearner{
                constants:s.constants,
                max_ballot_seen:m->bal_2b,
                unexecuted_learner_state:map![opn => tup_]
            }
        } else if !s.unexecuted_learner_state.contains_key(opn) {
            let tup_ = LearnerTuple{received_2b_message_senders:set![packet.src], candidate_learned_value:m->val_2b};
            s_ == LLearner{
                constants:s.constants,
                max_ballot_seen:m->bal_2b,
                unexecuted_learner_state:s.unexecuted_learner_state.insert(opn, tup_)
            }
        } else if s.unexecuted_learner_state[opn].received_2b_message_senders.contains(packet.src) {
            s_ == s 
        } else {
            let tup = s.unexecuted_learner_state[opn];
            let tup_ = LearnerTuple{received_2b_message_senders:tup.received_2b_message_senders+set![packet.src], candidate_learned_value:tup.candidate_learned_value};
            s_ == LLearner{
                constants:s.constants,
                max_ballot_seen:s.max_ballot_seen,
                unexecuted_learner_state:s.unexecuted_learner_state.insert(opn, tup_)
            }
        }
    }

    pub open spec fn LLearnerForgetDecision(
        s:LLearner, 
        s_:LLearner, 
        opn:OperationNumber
    ) -> bool
    {
        if s.unexecuted_learner_state.contains_key(opn) {
            s_ == LLearner{
                constants:s.constants,
                max_ballot_seen:s.max_ballot_seen,
                unexecuted_learner_state:s.unexecuted_learner_state.remove(opn)
            }
        } else {
            s_ == s
        }
    }

    pub open spec fn LLearnerForgetOperationsBefore(
        s:LLearner, 
        s_:LLearner, 
        ops_complete:OperationNumber
    ) -> bool 
    {
        &&& (forall |k:OperationNumber| s_.unexecuted_learner_state.contains_key(k) <==> k >= ops_complete && s.unexecuted_learner_state.contains_key(k))
        &&& (forall |k:OperationNumber| s_.unexecuted_learner_state.contains_key(k) ==> s_.unexecuted_learner_state[k] == s.unexecuted_learner_state[k])
        &&& s_ == LLearner{
            constants:s.constants,
            max_ballot_seen:s.max_ballot_seen,
            unexecuted_learner_state:s_.unexecuted_learner_state
        }
    }
}