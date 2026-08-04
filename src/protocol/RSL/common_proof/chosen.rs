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
        broadcast use vstd::set::group_set_lemmas;

        lemma_ConstantsAllConsistent(b, c, i);

        // Both quorum index sets are non-empty (size >= LMinQuorumSize >= 1)
        assert(q1.indices.len() >= LMinQuorumSize(b[i].constants.config));
        assert(q2.indices.len() >= LMinQuorumSize(b[i].constants.config));
        assert(q1.indices.len() > 0) by {
            assert(WellFormedLConfiguration(c.config));
            assert(LMinQuorumSize(c.config) >= 1);
        }
        assert(q2.indices.len() > 0) by {
            assert(WellFormedLConfiguration(c.config));
            assert(LMinQuorumSize(c.config) >= 1);
        }
        // Extract witnesses from non-empty sets
        let idx1 = q1.indices.choose();
        let idx2 = q2.indices.choose();
        assert(q1.indices.contains(idx1));
        assert(q2.indices.contains(idx2));
        assert(0 <= idx1 < q1.packets.len());
        assert(0 <= idx2 < q2.packets.len());
        let p1_2b = q1.packets[idx1];
        let p2_2b = q2.packets[idx2];
        assert(b[i].environment.sentPackets.contains(p1_2b));
        assert(b[i].environment.sentPackets.contains(p2_2b));
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

        // Prove quorum_of_1bs.finite() via injective preimage into replica_ids
        let rid_set = c.config.replica_ids.to_set();
        let f_src = |p: RslPacket| p.src;
        assert forall |p: RslPacket| quorum_of_1bs.contains(p)
            implies rid_set.contains(#[trigger] f_src(p)) by
        {
            assert(c.config.replica_ids.contains(p.src));
        };
        assert forall |p1: RslPacket, p2: RslPacket|
            #![trigger f_src(p1), f_src(p2)]
            quorum_of_1bs.contains(p1) && quorum_of_1bs.contains(p2) && f_src(p1) == f_src(p2)
            implies p1 == p2 by
        {
            if p1 != p2 {
                assert(p1.src != p2.src);
            }
        };
        lemma_injective_preimage_finite(quorum_of_1bs, f_src, rid_set);

        let quorum_of_1bs_indices = lemma_GetIndicesFromPackets(quorum_of_1bs, c.config);

        let overlap_idx = lemma_QuorumIndexOverlap(quorum_of_1bs_indices, quorum_of_2bs.indices, c.config.replica_ids.len() as int);
        let packet1b_overlap = choose|p| quorum_of_1bs.contains(p) && p.src == c.config.replica_ids[overlap_idx];
        let packet2b_overlap = quorum_of_2bs.packets[overlap_idx];

        if !packet1b_overlap.msg->votes.contains_key(opn) {
            lemma_1bMessageWithoutOpnImplicationsFor2b(b, c, i, opn, packet1b_overlap, packet2b_overlap);
            assert(false);
        }

        // packet1b_overlap is in quorum_of_1bs and has votes[opn], so LAllAcceptorsHadNoProposal is false.
        // Therefore LValIsHighestNumberedProposal must hold (from lemma_2aMessageHas1bQuorumPermittingIt).
        assert(!LAllAcceptorsHadNoProposal(quorum_of_1bs, opn));
        assert(LValIsHighestNumberedProposal(packet2a.msg->val_2a, quorum_of_1bs, opn));

        // Unfold: exists |c:Ballot| LValIsHighestNumberedProposalAtBallot(v, c, S, opn)
        let highestballot_in_1b_set = choose |b| LValIsHighestNumberedProposalAtBallot(packet2a.msg->val_2a, b, quorum_of_1bs, opn);
        assert(LValIsHighestNumberedProposalAtBallot(packet2a.msg->val_2a, highestballot_in_1b_set, quorum_of_1bs, opn));
        assert(BalLeq(packet1b_overlap.msg->votes[opn].max_value_bal, highestballot_in_1b_set));

        // LExistsBallotInS gives a witness packet for the highest ballot
        assert(LExistsBallotInS(packet2a.msg->val_2a, highestballot_in_1b_set, quorum_of_1bs, opn));
        let packet1b_highestballot = choose |p| quorum_of_1bs.contains(p) &&
            p.msg->votes.contains_key(opn) && p.msg->votes[opn] == Vote{max_value_bal:highestballot_in_1b_set, max_val:packet2a.msg->val_2a};
        assert(quorum_of_1bs.contains(packet1b_highestballot) &&
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
            lemma_2aMessageHasValidBallot(b, c, i, previous_packet2a);
            // Help termination: previous_packet2a.msg->bal_2a < packet2a.msg->bal_2a lexicographically
            assert(BalLt(previous_packet2a.msg->bal_2a, packet2a.msg->bal_2a));
            // Verus decreases clause is (seqno, proposer_id), lexicographic ordering:
            assert(previous_packet2a.msg->bal_2a.seqno <= packet2a.msg->bal_2a.seqno);
            if previous_packet2a.msg->bal_2a.seqno < packet2a.msg->bal_2a.seqno {
                // First component strictly decreases
            } else {
                // First component equal, second must strictly decrease
                assert(previous_packet2a.msg->bal_2a.seqno == packet2a.msg->bal_2a.seqno);
                assert(previous_packet2a.msg->bal_2a.proposer_id < packet2a.msg->bal_2a.proposer_id);
            }
            // Ensure non-negativity for nat decreases
            assert(previous_packet2a.msg->bal_2a.seqno >= 0);
            assert(previous_packet2a.msg->bal_2a.proposer_id >= 0);
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

    pub proof fn lemma_DecidedOperationWasChosen_change_step(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        idx: int
    ) -> (q: QuorumOf2bs)
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 < i,
            0 <= idx < b[i - 1].replicas.len(),
            0 <= idx < b[i].replicas.len(),
            c.config.replica_ids.len() > 0,
            b[i - 1].replicas[idx].replica.learner.unexecuted_learner_state.contains_key(
                b[i - 1].replicas[idx].replica.executor.ops_complete,
            ),
            b[i].replicas[idx].replica.executor.next_op_to_execute
                == (OutstandingOperation::OutstandingOpKnown{
                    v: b[i - 1].replicas[idx].replica.learner.unexecuted_learner_state[
                        b[i - 1].replicas[idx].replica.executor.ops_complete
                    ].candidate_learned_value,
                    bal: b[i - 1].replicas[idx].replica.learner.max_ballot_seen,
                }),
        ensures
            q.bal == b[i].replicas[idx].replica.executor.next_op_to_execute->bal,
            q.opn == b[i].replicas[idx].replica.executor.ops_complete,
            q.v == b[i].replicas[idx].replica.executor.next_op_to_execute->v,
            q.indices.finite(),
            q.packets.len() == c.config.replica_ids.len(),
            forall |sidx: int| q.indices.contains(sidx) ==> ({
                let p = q.packets[sidx];
                &&& 0 <= sidx < c.config.replica_ids.len()
                &&& p.src == c.config.replica_ids[sidx]
                &&& p.msg is RslMessage2b
                &&& p.msg->opn_2b == q.opn
                &&& p.msg->val_2b == q.v
                &&& p.msg->bal_2b == q.bal
                &&& b[i].environment.sentPackets.contains(p)
            }),
            forall |sidx: int|
                0 <= sidx < c.config.replica_ids.len()
                && b[i - 1].replicas[idx].replica.learner.unexecuted_learner_state[
                    b[i - 1].replicas[idx].replica.executor.ops_complete
                ].received_2b_message_senders.contains(c.config.replica_ids[sidx])
                ==> q.indices.contains(sidx),
    {
        let s = b[i - 1].replicas[idx].replica;
        let opn = s.executor.ops_complete;
        let v = s.learner.unexecuted_learner_state[opn].candidate_learned_value;
        let bal = s.learner.max_ballot_seen;
        let senders = s.learner.unexecuted_learner_state[opn].received_2b_message_senders;
        let (indices, packets) = collect_2b_messages(c, senders, opn, idx, b, i, 0);

        let q_out = QuorumOf2bs{c:c, indices:indices, packets:packets, bal:bal, opn:opn, v:v};
        assert(q_out.indices.finite());
        assert(q_out.packets.len() == c.config.replica_ids.len()) by {
            assert(q_out.packets.len() == c.config.replica_ids.len() - 0);
        };
        assert forall |sidx: int| q_out.indices.contains(sidx) implies ({
            let p = q_out.packets[sidx];
            &&& 0 <= sidx < c.config.replica_ids.len()
            &&& p.src == c.config.replica_ids[sidx]
            &&& p.msg is RslMessage2b
            &&& p.msg->opn_2b == q_out.opn
            &&& p.msg->val_2b == q_out.v
            &&& p.msg->bal_2b == q_out.bal
            &&& b[i].environment.sentPackets.contains(p)
        }) by {
            let p = q_out.packets[sidx];
            assert(0 <= sidx < c.config.replica_ids.len());
            assert(p == q_out.packets[sidx - 0]);
            assert(p.msg->opn_2b == opn);
            assert(p.msg->val_2b == v);
            assert(p.msg->bal_2b == bal);
        };
        assert forall |sidx: int|
            0 <= sidx < c.config.replica_ids.len()
            && b[i - 1].replicas[idx].replica.learner.unexecuted_learner_state[
                b[i - 1].replicas[idx].replica.executor.ops_complete
            ].received_2b_message_senders.contains(c.config.replica_ids[sidx])
            implies q_out.indices.contains(sidx) by {
            assert(q_out.indices.contains(sidx));
        };
        q_out
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
        decreases i,
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

        lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i - 1, idx);
        assert(b[i - 1].replicas[idx].nextActionIndex == 5);
        let opn = s.executor.ops_complete;
        let v = s.learner.unexecuted_learner_state[opn].candidate_learned_value;
        let bal = s.learner.max_ballot_seen;
        assert(s.learner.unexecuted_learner_state.contains_key(opn));
        assert(s.learner.unexecuted_learner_state[opn].received_2b_message_senders.len() >= LMinQuorumSize(c.config));
        assert(s_prime.executor.next_op_to_execute == OutstandingOperation::OutstandingOpKnown{v:v, bal:bal});
        let senders = s.learner.unexecuted_learner_state[opn].received_2b_message_senders;
        let q_new = lemma_DecidedOperationWasChosen_change_step(b, c, i, idx);

        lemma_Received2bMessageSendersAlwaysValidReplicas(b, c, i - 1, idx, opn);
        let rid_set = c.config.replica_ids.to_set();
        assert(senders.subset_of(rid_set)) by {
            assert forall |node: AbstractEndPoint| senders.contains(node) implies rid_set.contains(node) by
            {
                assert(c.config.replica_ids.contains(node));
            };
        };
        vstd::set_lib::lemma_len_subset(senders, rid_set);

        let alt_indices = lemma_GetIndicesFromNodes(senders, c.config);
        assert forall |sidx: int| alt_indices.contains(sidx) implies q_new.indices.contains(sidx) by {
            assert(0 <= sidx < c.config.replica_ids.len());
            assert(senders.contains(c.config.replica_ids[sidx]));
        }
        subset_cardinality(alt_indices, q_new.indices);
        assert(q_new.indices.len() >= LMinQuorumSize(c.config)) by {
            assert(alt_indices.len() == senders.len());
            assert(alt_indices.len() >= LMinQuorumSize(c.config));
        };
        assert(IsValidQuorumOf2bs(b[i], q_new)) by {
            assert(q_new.indices.len() >= LMinQuorumSize(b[i].constants.config));
            assert(q_new.packets.len() == b[i].constants.config.replica_ids.len());
            assert forall |sidx: int| q_new.indices.contains(sidx) implies
                0 <= sidx < b[i].constants.config.replica_ids.len()
                && q_new.packets[sidx].src == b[i].constants.config.replica_ids[sidx]
                && q_new.packets[sidx].msg is RslMessage2b
                && q_new.packets[sidx].msg->opn_2b == q_new.opn
                && q_new.packets[sidx].msg->val_2b == q_new.v
                && q_new.packets[sidx].msg->bal_2b == q_new.bal
                && b[i].environment.sentPackets.contains(q_new.packets[sidx]) by
            {
                let p = q_new.packets[sidx];
                assert(0 <= sidx < c.config.replica_ids.len());
                assert(p.src == c.config.replica_ids[sidx]);
                assert(p.msg->opn_2b == q_new.opn);
                assert(p.msg->val_2b == q_new.v);
                assert(p.msg->bal_2b == q_new.bal);
                assert(b[i].environment.sentPackets.contains(p));
            };
        };

        q_new
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
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 < i,
            0 <= idx < b[i - 1].replicas.len(),
            b[i - 1].replicas[idx].replica.learner.unexecuted_learner_state.contains_key(opn),
            senders.subset_of(
                b[i - 1].replicas[idx].replica.learner.unexecuted_learner_state[opn].received_2b_message_senders
            ),
            0 <= sender_idx <= c.config.replica_ids.len(),
            c.config.replica_ids.len() > 0,
        ensures
            rc.0.finite(),
            rc.1.len() == c.config.replica_ids.len() - sender_idx,
            forall |sidx: int| rc.0.contains(sidx)
                ==> sender_idx <= sidx < c.config.replica_ids.len(),
            forall |sidx: int|
                sender_idx <= sidx < c.config.replica_ids.len()
                && senders.contains(c.config.replica_ids[sidx])
                ==> rc.0.contains(sidx),
            forall |sidx: int| rc.0.contains(sidx) ==> ({
                let p = rc.1[sidx - sender_idx];
                &&& p.src == c.config.replica_ids[sidx]
                &&& p.msg is RslMessage2b
                &&& p.msg->opn_2b == opn
                &&& p.msg->bal_2b == b[i - 1].replicas[idx].replica.learner.max_ballot_seen
                &&& p.msg->val_2b == b[i - 1].replicas[idx].replica.learner.unexecuted_learner_state[opn].candidate_learned_value
                &&& b[i].environment.sentPackets.contains(p)
            }),
        decreases c.config.replica_ids.len() - sender_idx
    {
        broadcast use vstd::set::group_set_lemmas;

        let dummy_packet = LPacket{dst:c.config.replica_ids[0], src:c.config.replica_ids[0], msg:RslMessage::RslMessage1a{bal_1a:Ballot{seqno:0, proposer_id:0}}};
        if c.config.replica_ids.len() == sender_idx {
            (Set::empty(), Seq::empty())
        } else {
            let sender = c.config.replica_ids[sender_idx];
            // let rest_config = c.config.replica_ids.drop_first();

            let (rest_indices, rest_packets) = collect_2b_messages(
                c, senders, opn, idx, b, i, sender_idx+1
            );
            // IH: rest_indices.finite()

            if senders.contains(sender) {
                assert(
                    b[i - 1].replicas[idx].replica.learner.unexecuted_learner_state[opn]
                        .received_2b_message_senders.contains(sender)
                ) by {
                    assert(senders.subset_of(
                        b[i - 1].replicas[idx].replica.learner.unexecuted_learner_state[opn]
                            .received_2b_message_senders
                    ));
                }
                let (sender_idx_unused, p) = lemma_GetSent2bMessageFromLearnerState(b, c, i - 1, idx, opn, sender);
                lemma_PacketStaysInSentPackets(b, c, i - 1, i, p);
                assert(sender == c.config.replica_ids[sender_idx]);
                assert(sender == c.config.replica_ids[sender_idx_unused]);
                assert(sender_idx_unused == sender_idx) by {
                    if sender_idx_unused != sender_idx {
                        assert(ReplicasDistinct(c.config.replica_ids, sender_idx_unused, sender_idx));
                        assert(c.config.replica_ids[sender_idx_unused] != c.config.replica_ids[sender_idx]);
                        assert(false);
                    }
                };
                let new_indices = set![sender_idx_unused] + rest_indices;
                // set![sender_idx_unused] = Set::empty().insert(sender_idx_unused) is finite
                // Set unions are finite by construction.
                let new_packets = seq![p] + rest_packets;
                assert(new_packets.len() == c.config.replica_ids.len() - sender_idx);
                assert forall |sidx: int| new_indices.contains(sidx)
                    implies sender_idx <= sidx < c.config.replica_ids.len() by {
                    if sidx == sender_idx_unused {
                        assert(sender_idx <= sidx < c.config.replica_ids.len());
                    } else {
                        assert(rest_indices.contains(sidx));
                        assert(sender_idx + 1 <= sidx < c.config.replica_ids.len());
                        assert(sender_idx <= sidx);
                    }
                };
                assert forall |sidx: int| new_indices.contains(sidx) implies ({
                    let p_out = new_packets[sidx - sender_idx];
                    &&& p_out.src == c.config.replica_ids[sidx]
                    &&& p_out.msg is RslMessage2b
                    &&& p_out.msg->opn_2b == opn
                    &&& p_out.msg->bal_2b == b[i - 1].replicas[idx].replica.learner.max_ballot_seen
                    &&& p_out.msg->val_2b == b[i - 1].replicas[idx].replica.learner.unexecuted_learner_state[opn].candidate_learned_value
                    &&& b[i].environment.sentPackets.contains(p_out)
                }) by {
                    if sidx == sender_idx_unused {
                        assert(sidx == sender_idx);
                        assert(sidx - sender_idx == 0);
                        assert(new_packets[sidx - sender_idx] == p);
                    } else {
                        assert(rest_indices.contains(sidx));
                        assert(sender_idx + 1 <= sidx < c.config.replica_ids.len());
                        assert(0 <= sidx - (sender_idx + 1) < rest_packets.len());
                        assert(new_packets[sidx - sender_idx] == rest_packets[sidx - (sender_idx + 1)]);
                    }
                };
                assert forall |sidx: int|
                    sender_idx <= sidx < c.config.replica_ids.len()
                    && senders.contains(c.config.replica_ids[sidx])
                    implies new_indices.contains(sidx) by {
                    if sidx == sender_idx_unused {
                        assert(new_indices.contains(sender_idx_unused));
                    } else {
                        assert(sender_idx + 1 <= sidx < c.config.replica_ids.len());
                        assert(rest_indices.contains(sidx));
                        assert(new_indices.contains(sidx));
                    }
                };
                (new_indices, new_packets)
            } else {
                let new_packets = seq![dummy_packet] + rest_packets;
                assert(new_packets.len() == c.config.replica_ids.len() - sender_idx);
                assert forall |sidx: int| rest_indices.contains(sidx)
                    implies sender_idx <= sidx < c.config.replica_ids.len() by {
                    assert(sender_idx + 1 <= sidx < c.config.replica_ids.len());
                    assert(sender_idx <= sidx);
                };
                assert forall |sidx: int| rest_indices.contains(sidx) implies ({
                    let p_out = new_packets[sidx - sender_idx];
                    &&& p_out.src == c.config.replica_ids[sidx]
                    &&& p_out.msg is RslMessage2b
                    &&& p_out.msg->opn_2b == opn
                    &&& p_out.msg->bal_2b == b[i - 1].replicas[idx].replica.learner.max_ballot_seen
                    &&& p_out.msg->val_2b == b[i - 1].replicas[idx].replica.learner.unexecuted_learner_state[opn].candidate_learned_value
                    &&& b[i].environment.sentPackets.contains(p_out)
                }) by {
                    assert(sender_idx + 1 <= sidx < c.config.replica_ids.len());
                    assert(0 <= sidx - (sender_idx + 1) < rest_packets.len());
                    assert(new_packets[sidx - sender_idx] == rest_packets[sidx - (sender_idx + 1)]);
                };
                assert forall |sidx: int|
                    sender_idx <= sidx < c.config.replica_ids.len()
                    && senders.contains(c.config.replica_ids[sidx])
                    implies rest_indices.contains(sidx) by {
                    if sidx == sender_idx {
                        assert(c.config.replica_ids[sidx] == sender);
                        assert(senders.contains(sender));
                        assert(false);
                    } else {
                        assert(sender_idx + 1 <= sidx < c.config.replica_ids.len());
                        assert(rest_indices.contains(sidx));
                    }
                };
                (rest_indices, new_packets)
            }
        }
    }
}
