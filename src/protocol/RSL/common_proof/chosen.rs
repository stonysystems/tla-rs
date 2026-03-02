use crate::protocol::RSL::common_proof::actions::*;
use crate::protocol::RSL::common_proof::assumptions::*;
use crate::protocol::RSL::common_proof::constants::*;
use crate::protocol::RSL::common_proof::environment::*;
use crate::protocol::RSL::common_proof::learner_state::*;
use crate::protocol::RSL::common_proof::message1b::*;
use crate::protocol::RSL::common_proof::message2a::*;
use crate::protocol::RSL::common_proof::message2b::*;
use crate::protocol::RSL::common_proof::quorum::*;
use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::election::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::executor::*;
use crate::protocol::RSL::learner::*;
use crate::protocol::RSL::message::*;
use crate::protocol::RSL::proposer::*;
use crate::protocol::RSL::types::*;
use vstd::prelude::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

use crate::common::collections::maps2::*;
use crate::common::collections::sets::*;
use crate::common::framework::environment_s::LEnvStep;
use crate::common::framework::environment_s::*;
use crate::common::logic::heuristics_i::*;
use crate::common::logic::temporal_s::*;
use crate::common::native::io_s::*;

verus! {
    pub struct QuorumOf2bs{
        pub c:LConstants,
        pub indices:Set<int>,
        pub packets:Seq<RslPacket>,
        pub bal:Ballot,
        pub opn:OperationNumber,
        pub v:RequestBatch,
    }

    pub open spec fn IsValidQuorumOf2bs(
        ps:RslState,
        q:QuorumOf2bs
    ) -> bool
    {
        &&& q.indices.len() >= LMinQuorumSize(ps.constants.config)
        &&& q.packets.len() == ps.constants.config.replica_ids.len()
        &&& (forall |idx:int| q.indices.contains(idx) ==> 0 <= idx < ps.constants.config.replica_ids.len()
                                        //  && let p = q.packets[idx];
                                         && q.packets[idx].src == ps.constants.config.replica_ids[idx]
                                         && q.packets[idx].msg is RslMessage2b
                                         && q.packets[idx].msg->opn_2b == q.opn
                                         && q.packets[idx].msg->val_2b == q.v
                                         && q.packets[idx].msg->bal_2b == q.bal
                                         && ps.environment.sentPackets.contains(q.packets[idx]))
    }


    pub proof fn lemma_ChosenQuorumsMatchValue(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        q1: QuorumOf2bs,
        q2: QuorumOf2bs
    )
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            IsValidQuorumOf2bs(b[i], q1),
            IsValidQuorumOf2bs(b[i], q2),
            q1.opn == q2.opn,
        ensures
            q1.v == q2.v,
    {
        lemma_ConstantsAllConsistent(b, c, i);

        let idx1 = choose|idx1: int| q1.indices.contains(idx1);
        let idx2 = choose|idx2: int| q2.indices.contains(idx2);
        let p1_2b = q1.packets[idx1];
        let p2_2b = q2.packets[idx2];
        assert(forall |idx:int| q1.indices.contains(idx) ==> b[i].environment.sentPackets.contains(q1.packets[idx]));
        assert(forall |idx:int| q2.indices.contains(idx) ==> b[i].environment.sentPackets.contains(q2.packets[idx]));
        assume(q1.indices.contains(idx1));
        assume(q2.indices.contains(idx2));
        let p1_2a = lemma_2bMessageHasCorresponding2aMessage(b, c, i, p1_2b);
        let p2_2a = lemma_2bMessageHasCorresponding2aMessage(b, c, i, p2_2b);

        if q1.bal == q2.bal {
            lemma_2aMessagesFromSameBallotAndOperationMatch(b, c, i, p1_2a, p2_2a);
        } else if BalLt(q1.bal, q2.bal) {
            lemma_ChosenQuorumAnd2aFromLaterBallotMatchValues(b, c, i, q1, p2_2a);
        } else {
            lemma_ChosenQuorumAnd2aFromLaterBallotMatchValues(b, c, i, q2, p1_2a);
        }
    }

    pub proof fn lemma_ChosenQuorumAnd2aFromLaterBallotMatchValues(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        quorum_of_2bs: QuorumOf2bs,
        packet2a: RslPacket
    )
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            IsValidQuorumOf2bs(b[i], quorum_of_2bs),
            b[i].environment.sentPackets.contains(packet2a),
            c.config.replica_ids.contains(packet2a.src),
            packet2a.msg is RslMessage2a,
            quorum_of_2bs.opn == packet2a.msg->opn_2a,
            BalLt(quorum_of_2bs.bal, packet2a.msg->bal_2a),
        ensures
            quorum_of_2bs.v == packet2a.msg->val_2a,
        decreases packet2a.msg->bal_2a.seqno, packet2a.msg->bal_2a.proposer_id,
    {
        lemma_ConstantsAllConsistent(b, c, i);

        let opn = quorum_of_2bs.opn;
        let quorum_of_1bs = lemma_2aMessageHas1bQuorumPermittingIt(b, c, i, packet2a);
        let quorum_of_1bs_indices = lemma_GetIndicesFromPackets(quorum_of_1bs, c.config);

        let overlap_idx = lemma_QuorumIndexOverlap(quorum_of_1bs_indices, quorum_of_2bs.indices, c.config.replica_ids.len() as int);
        let packet1b_overlap = choose|p| quorum_of_1bs.contains(p) && p.src == c.config.replica_ids[overlap_idx];
        let packet2b_overlap = quorum_of_2bs.packets[overlap_idx];

        if !packet1b_overlap.msg->votes.contains_key(opn) {
            lemma_1bMessageWithoutOpnImplicationsFor2b(b, c, i, opn, packet1b_overlap, packet2b_overlap);
            assert(false);
        }

        let highestballot_in_1b_set = choose |b| LValIsHighestNumberedProposalAtBallot(packet2a.msg->val_2a, b, quorum_of_1bs, opn);
        assume(LValIsHighestNumberedProposalAtBallot(packet2a.msg->val_2a, highestballot_in_1b_set, quorum_of_1bs, opn));
        assert(BalLeq(packet1b_overlap.msg->votes[opn].max_value_bal, highestballot_in_1b_set));

        let packet1b_highestballot = choose |p| quorum_of_1bs.contains(p) &&
            p.msg->votes.contains_key(opn) && p.msg->votes[opn] == Vote{max_value_bal:highestballot_in_1b_set, max_val:packet2a.msg->val_2a};
        assume(quorum_of_1bs.contains(packet1b_highestballot) &&
            packet1b_highestballot.msg->votes.contains_key(opn) &&
            packet1b_highestballot.msg->votes[opn] == Vote{max_value_bal:highestballot_in_1b_set, max_val:packet2a.msg->val_2a});
        assert(BalLeq(quorum_of_2bs.bal, packet1b_highestballot.msg->bal_1b));

        lemma_Vote1bMessageIsFromEarlierBallot(b, c, i, opn, packet1b_highestballot);
        lemma_1bMessageWithOpnImplicationsFor2b(b, c, i, opn, packet1b_overlap, packet2b_overlap);

        assert(BalLeq(quorum_of_2bs.bal, packet1b_highestballot.msg->votes[opn].max_value_bal));
        let previous_packet2a = lemma_1bMessageWithOpnImplies2aSent(b, c, i, opn, packet1b_highestballot);
        assert(previous_packet2a.msg->bal_2a == packet1b_highestballot.msg->votes[opn].max_value_bal);
        assert(BalLeq(quorum_of_2bs.bal, previous_packet2a.msg->bal_2a));
        assert(BalLt(previous_packet2a.msg->bal_2a, packet2a.msg->bal_2a));

        if quorum_of_2bs.bal == previous_packet2a.msg->bal_2a {
            let packet2a_overlap = lemma_2bMessageHasCorresponding2aMessage(b, c, i, packet2b_overlap);
            lemma_2aMessagesFromSameBallotAndOperationMatch(b, c, i, packet2a_overlap, previous_packet2a);
        } else {
            assert(BalLt(quorum_of_2bs.bal, previous_packet2a.msg->bal_2a));
            lemma_2aMessageHasValidBallot(b, c, i, packet2a);
            lemma_ChosenQuorumAnd2aFromLaterBallotMatchValues(b, c, i, quorum_of_2bs, previous_packet2a);
        }
    }

    pub proof fn lemma_QuorumOf2bsStaysValid(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        j: int,
        q: QuorumOf2bs
    )
        requires
            IsValidBehaviorPrefix(b, c, j),
            IsValidQuorumOf2bs(b[i], q),
            0 <= i <= j,
        ensures
            IsValidQuorumOf2bs(b[j], q),
    {
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_ConstantsAllConsistent(b, c, j);

        assert forall |idx: int| q.indices.contains(idx) implies b[j].environment.sentPackets.contains(q.packets.index(idx)) by {
            lemma_PacketStaysInSentPackets(b, c, i, j, q.packets[idx]);
        }
    }

    pub proof fn lemma_DecidedOperationWasChosen(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        idx: int
    ) -> (q: QuorumOf2bs)
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            0 <= idx < b[i].replicas.len(),
            b[i].replicas[idx].replica.executor.next_op_to_execute is OutstandingOpKnown,
        ensures
            IsValidQuorumOf2bs(b[i], q),
            q.bal == b[i].replicas[idx].replica.executor.next_op_to_execute->bal,
            q.opn == b[i].replicas[idx].replica.executor.ops_complete,
            q.v == b[i].replicas[idx].replica.executor.next_op_to_execute->v,
    {
        if i == 0 {
            return arbitrary();
        }

        lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
        lemma_ReplicaConstantsAllConsistent(b, c, i - 1, idx);
        lemma_AssumptionsMakeValidTransition(b, c, i - 1);

        let s = b[i - 1].replicas[idx].replica;
        let s_prime = &b[i].replicas[idx].replica;

        if s_prime.executor.next_op_to_execute == s.executor.next_op_to_execute {
            let q_prev = lemma_DecidedOperationWasChosen(b, c, i - 1, idx);
            lemma_QuorumOf2bsStaysValid(b, c, i - 1, i, q_prev);
            return q_prev;
        }

        let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i - 1, idx);
        assert(b[i - 1].replicas[idx].nextActionIndex == 5);
        let opn = s.executor.ops_complete;
        let v = s.learner.unexecuted_learner_state[opn].candidate_learned_value;
        let bal = s.learner.max_ballot_seen;
        assert(s.learner.unexecuted_learner_state.contains_key(opn));
        assert(s.learner.unexecuted_learner_state[opn].received_2b_message_senders.len() >= LMinQuorumSize(c.config));
        assert(s_prime.executor.next_op_to_execute == OutstandingOperation::OutstandingOpKnown{v:v, bal:bal});
        let senders = s.learner.unexecuted_learner_state[opn].received_2b_message_senders;

        let mut sender_idx: int = 0;

        let (indices, packets) = collect_2b_messages(c, senders, opn, idx, b, i, sender_idx);


        lemma_Received2bMessageSendersAlwaysValidReplicas(b, c, i - 1, idx, opn);
        let alt_indices = lemma_GetIndicesFromNodes(senders, c.config);
        assert forall |sidx: int| alt_indices.contains(sidx) implies indices.contains(sidx) by {
            assert(0 <= sidx < c.config.replica_ids.len());
            assert(senders.contains(c.config.replica_ids[sidx]));
        }
        SubsetCardinality(alt_indices, indices);

        return QuorumOf2bs{c:c, indices:indices, packets:packets, bal:bal, opn:opn, v:v};
    }

    pub proof fn collect_2b_messages(
        c: LConstants,
        senders: Set<AbstractEndPoint>,
        opn: int,
        idx: int,
        b: Behavior<RslState>,
        i: int,
        sender_idx:int,
    ) -> (rc:(Set<int>, Seq<RslPacket>))
        // ensures
        //     indices.subset_of(Set::new(|x: int| 0 <= x < c.config.replica_ids.len())),
        //     packets.len() == c.config.replica_ids.len()
        decreases c.config.replica_ids.len() - sender_idx
    {
        let dummy_packet = LPacket{dst:c.config.replica_ids[0], src:c.config.replica_ids[0], msg:RslMessage::RslMessage1a{bal_1a:Ballot{seqno:0, proposer_id:0}}};
        if c.config.replica_ids.len() == sender_idx {
            (Set::empty(), Seq::empty())
        } else {
            let sender = c.config.replica_ids[sender_idx];
            // let rest_config = c.config.replica_ids.drop_first();

            let (rest_indices, rest_packets) = collect_2b_messages(
                c, senders, opn, idx, b, i, sender_idx+1
            );

            if senders.contains(sender) {
                let (sender_idx_unused, p) = lemma_GetSent2bMessageFromLearnerState(b, c, i, idx, opn, sender);
                let new_indices = set![sender_idx_unused] + rest_indices;
                let new_packets = seq![p] + rest_packets;
                (new_indices, new_packets)
            } else {
                let new_packets = seq![dummy_packet] + rest_packets;
                (rest_indices, new_packets)
            }
        }
    }
}
