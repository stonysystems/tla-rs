use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::election::*;
use crate::protocol::RSL::proposer::*;
use crate::protocol::RSL::executor::*;
use crate::protocol::RSL::learner::*;
use crate::protocol::RSL::message::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::common_proof::assumptions::*;
use crate::protocol::RSL::common_proof::constants::*;
use crate::protocol::RSL::common_proof::actions::*;
use crate::protocol::RSL::common_proof::message1b::*;
use crate::protocol::RSL::common_proof::message2a::*;
use crate::protocol::RSL::common_proof::message2b::*;
use crate::protocol::RSL::common_proof::quorum::*;
use crate::protocol::RSL::common_proof::environment::*;

use crate::common::logic::temporal_s::*;
use crate::common::logic::heuristics_i::*;
use crate::common::framework::environment_s::*;
use crate::common::framework::environment_s::LEnvStep;
use crate::common::native::io_s::*;
use crate::common::collections::maps2::*;

verus!{
    pub proof fn lemma_Received2bMessageSendersAlwaysValidReplicas(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        learner_idx: int,
        opn: OperationNumber
    )
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            0 <= learner_idx < b[i].replicas.len(),
            b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state.contains_key(opn),
        ensures
            forall |sender: AbstractEndPoint| b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state[opn].received_2b_message_senders.contains(sender) ==> c.config.replica_ids.contains(sender),
        decreases i,
    {
        if i == 0 {
            return;
        }
    
        lemma_AssumptionsMakeValidTransition(b, c, i - 1);
        lemma_ConstantsAllConsistent(b, c, i - 1);
        lemma_ConstantsAllConsistent(b, c, i);
    
        let s = b[i - 1].replicas[learner_idx].replica.learner;
        let s_prime = b[i].replicas[learner_idx].replica.learner;
    
        assert forall |sender: AbstractEndPoint| s_prime.unexecuted_learner_state[opn].received_2b_message_senders.contains(sender) implies c.config.replica_ids.contains(sender) by {
            if s.unexecuted_learner_state.contains_key(opn) && s.unexecuted_learner_state[opn].received_2b_message_senders.contains(sender) {
                lemma_Received2bMessageSendersAlwaysValidReplicas(b, c, i - 1, learner_idx, opn);
            } else {
                let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i - 1, learner_idx);
            }
        }
    }

    #[verifier::external_body]
    pub proof fn lemma_Received2bMessageSendersAlwaysNonempty(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        learner_idx: int,
        opn: OperationNumber
    )
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            0 <= learner_idx < b[i].replicas.len(),
            b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state.contains_key(opn),
        ensures
            b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state[opn].received_2b_message_senders.len() > 0,
        decreases i,
    {
        if i == 0 {
            return;
        }
    
        lemma_AssumptionsMakeValidTransition(b, c, i - 1);
        lemma_ConstantsAllConsistent(b, c, i - 1);
        lemma_ConstantsAllConsistent(b, c, i);
    
        let s = b[i - 1].replicas[learner_idx].replica.learner;
        let s_prime = &b[i].replicas[learner_idx].replica.learner;
    
        if s_prime.unexecuted_learner_state == s.unexecuted_learner_state {
            lemma_Received2bMessageSendersAlwaysNonempty(b, c, i - 1, learner_idx, opn);
            return;
        }
    
        let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i - 1, learner_idx);
        if s.unexecuted_learner_state.contains_key(opn) {
            lemma_Received2bMessageSendersAlwaysNonempty(b, c, i - 1, learner_idx, opn);
        }
    }

    #[verifier::external_body]
    pub proof fn lemma_GetSent2bMessageFromLearnerState(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        learner_idx: int,
        opn: OperationNumber,
        sender: AbstractEndPoint
    ) -> (rc:(int, RslPacket))
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            0 <= learner_idx < b[i].replicas.len(),
            b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state.contains_key(opn),
            b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state[opn].received_2b_message_senders.contains(sender),
        ensures
            ({
                // let (sender_idx, p) = lemma_GetSent2bMessageFromLearnerState(b, c, i, learner_idx, opn, sender);
                let sender_idx = rc.0;
                let p = rc.1;
                &&& 0 <= sender_idx < c.config.replica_ids.len()
                &&& b[i].environment.sentPackets.contains(p)
                &&& p.src == sender
                &&& sender == c.config.replica_ids[sender_idx]
                &&& p.msg is RslMessage2b
                &&& p.msg->opn_2b == opn
                &&& p.msg->bal_2b == b[i].replicas[learner_idx].replica.learner.max_ballot_seen
                &&& p.msg->val_2b == b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state[opn].candidate_learned_value
            })
            
        decreases i,
    {
        if i == 0 {
            return arbitrary();
        }
    
        lemma_ReplicaConstantsAllConsistent(b, c, i, learner_idx);
        lemma_ReplicaConstantsAllConsistent(b, c, i - 1, learner_idx);
        lemma_AssumptionsMakeValidTransition(b, c, i - 1);
    
        let s = b[i - 1].replicas[learner_idx].replica.learner;
        let s_prime = &b[i].replicas[learner_idx].replica.learner;
    
        if s_prime.max_ballot_seen == s.max_ballot_seen && s_prime.unexecuted_learner_state == s.unexecuted_learner_state {
            let (sender_idx_prev, p_prev) = lemma_GetSent2bMessageFromLearnerState(b, c, i - 1, learner_idx, opn, sender);
            lemma_PacketStaysInSentPackets(b, c, i - 1, i, p_prev);
            return (sender_idx_prev, p_prev);
        }
    
        if s.unexecuted_learner_state.contains_key(opn)
            && s.unexecuted_learner_state[opn].received_2b_message_senders.contains(sender)
            && s_prime.unexecuted_learner_state[opn].candidate_learned_value == s.unexecuted_learner_state[opn].candidate_learned_value
            && s_prime.max_ballot_seen == s.max_ballot_seen
        {
            let (sender_idx_prev, p_prev) = lemma_GetSent2bMessageFromLearnerState(b, c, i - 1, learner_idx, opn, sender);
            lemma_PacketStaysInSentPackets(b, c, i - 1, i, p_prev);
            return (sender_idx_prev, p_prev);
        }
    
        let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i - 1, learner_idx);
        let next_action_index = b[i - 1].replicas[learner_idx].nextActionIndex;
        assert(next_action_index == 0);
        assert(ios[0] is Receive);
        let p = ios[0]->r;
        let sender_idx = GetReplicaIndex(p.src, c.config);
    
        if p.msg->val_2b != s_prime.unexecuted_learner_state[opn].candidate_learned_value {
            assert(p.msg->bal_2b == s.max_ballot_seen);
            assert(s.unexecuted_learner_state.contains_key(opn));
            lemma_Received2bMessageSendersAlwaysNonempty(b, c, i - 1, learner_idx, opn);
            let sender2 = choose |sender2: AbstractEndPoint| s.unexecuted_learner_state[opn].received_2b_message_senders.contains(sender2);
            let (sender2_idx, p2) = lemma_GetSent2bMessageFromLearnerState(b, c, i - 1, learner_idx, opn, sender2);
    
            let p_2a = lemma_2bMessageHasCorresponding2aMessage(b, c, i, p);
            let p2_2a = lemma_2bMessageHasCorresponding2aMessage(b, c, i, p2);
            lemma_2aMessagesFromSameBallotAndOperationMatch(b, c, i, p_2a, p2_2a);
        }
        return (sender_idx, p);
    }
    
}