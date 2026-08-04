use crate::common::collections::seqs::*;
use crate::protocol::RSL::common_proof::actions::*;
use crate::protocol::RSL::common_proof::assumptions::*;
use crate::protocol::RSL::common_proof::constants::*;
use crate::protocol::RSL::common_proof::environment::*;
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
use crate::protocol::RSL::replica::*;
use crate::protocol::RSL::types::*;
use vstd::prelude::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

use crate::common::collections::maps2::*;
use crate::common::framework::environment_s::LEnvStep;
use crate::common::framework::environment_s::*;
use crate::common::logic::heuristics_i::*;
use crate::common::logic::temporal_s::*;
use crate::common::native::io_s::*;

verus! {
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
            forall |sender: AbstractEndPoint| #![trigger c.config.replica_ids.contains(sender)] b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state[opn].received_2b_message_senders.contains(sender) ==> c.config.replica_ids.contains(sender),
        decreases i, 1int,
    {
        if i == 0 {
            return;
        }

        lemma_AssumptionsMakeValidTransition(b, c, i - 1);
        lemma_ConstantsAllConsistent(b, c, i - 1);
        lemma_ConstantsAllConsistent(b, c, i);

        let s = b[i - 1].replicas[learner_idx].replica.learner;
        let s_prime = b[i].replicas[learner_idx].replica.learner;

        assert forall |sender: AbstractEndPoint| #![trigger c.config.replica_ids.contains(sender)] s_prime.unexecuted_learner_state[opn].received_2b_message_senders.contains(sender) implies c.config.replica_ids.contains(sender) by {
            if s.unexecuted_learner_state.contains_key(opn) && s.unexecuted_learner_state[opn].received_2b_message_senders.contains(sender) {
                lemma_Received2bMessageSendersAlwaysValidReplicas(b, c, i - 1, learner_idx, opn);
            } else {
                let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i - 1, learner_idx);
            }
        }
    }

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
        let s_prime = b[i].replicas[learner_idx].replica.learner;

        if s_prime.unexecuted_learner_state == s.unexecuted_learner_state {
            lemma_Received2bMessageSendersAlwaysNonempty(b, c, i - 1, learner_idx, opn);
            return;
        }

        let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i - 1, learner_idx);
        let sched = b[i - 1].replicas[learner_idx];
        let sched_prime = b[i].replicas[learner_idx];
        let next_action_index = sched.nextActionIndex;

        assert(RslNextOneReplica(b[i - 1], b[i], learner_idx, ios));
        assert(LSchedulerNext(sched, sched_prime, ios));

        assert forall |k: OperationNumber| #![trigger s.unexecuted_learner_state.contains_key(k)]
            s.unexecuted_learner_state.contains_key(k) implies s.unexecuted_learner_state[k].received_2b_message_senders.len() > 0 by {
            lemma_Received2bMessageSendersAlwaysNonempty(b, c, i - 1, learner_idx, k);
        }
        assert forall |k: OperationNumber| #![trigger s.unexecuted_learner_state.contains_key(k)]
            s.unexecuted_learner_state.contains_key(k) implies s.unexecuted_learner_state[k].received_2b_message_senders.finite() by {
            lemma_Received2bMessageSendersAlwaysValidReplicas(b, c, i - 1, learner_idx, k);
            assert(s.unexecuted_learner_state[k].received_2b_message_senders.subset_of(c.config.replica_ids.to_set())) by {
                assert forall |sender: AbstractEndPoint| #![trigger c.config.replica_ids.to_set().contains(sender)]
                    s.unexecuted_learner_state[k].received_2b_message_senders.contains(sender) implies c.config.replica_ids.to_set().contains(sender) by {
                    assert(c.config.replica_ids.contains(sender));
                }
            }
        }

        if next_action_index == 0 {
            assert(LReplicaNextProcessPacket(sched.replica, sched_prime.replica, ios));
            if ios[0] is TimeoutReceive {
                assert(s_prime.unexecuted_learner_state == s.unexecuted_learner_state);
                assert(false);
            }

            assert(ios[0] is Receive);
            if ios[0]->r.msg is RslMessageHeartbeat {
                assert(LReplicaNextReadClockAndProcessPacket(sched.replica, sched_prime.replica, ios));
                assert(s_prime.unexecuted_learner_state == s.unexecuted_learner_state);
                assert(false);
            }

            assert(LReplicaNextProcessPacketWithoutReadingClock(sched.replica, sched_prime.replica, ios));
            let packet = ios[0]->r;

            if packet.msg is RslMessage2b {
                assert(LReplicaNextProcess2b(sched.replica, sched_prime.replica, packet, ExtractSentPacketsFromIos(ios)));
                let op_learnable = sched.replica.executor.ops_complete < packet.msg->opn_2b
                    || (sched.replica.executor.ops_complete == packet.msg->opn_2b
                        && sched.replica.executor.next_op_to_execute is OutstandingOpUnknown);
                if !op_learnable {
                    assert(s_prime == s);
                    assert(false);
                }
                assert(LLearnerProcess2b(s, s_prime, packet));
                lemma_LLearnerProcess2b_preserves_nonempty_sender_sets(s, s_prime, packet);
                assert(s_prime.unexecuted_learner_state[opn].received_2b_message_senders.len() > 0);
                return;
            }

            if packet.msg is RslMessageAppStateSupply {
                assert(LReplicaNextProcessAppStateSupply(
                    sched.replica,
                    sched_prime.replica,
                    packet,
                    ExtractSentPacketsFromIos(ios),
                ));
                assert(LLearnerForgetOperationsBefore(s, s_prime, packet.msg->opn_state_supply));
                assert(s_prime.unexecuted_learner_state.contains_key(opn) <==> opn >= packet.msg->opn_state_supply
                    && s.unexecuted_learner_state.contains_key(opn));
                assert(s.unexecuted_learner_state.contains_key(opn));
                lemma_Received2bMessageSendersAlwaysNonempty(b, c, i - 1, learner_idx, opn);
                assert(s_prime.unexecuted_learner_state[opn] == s.unexecuted_learner_state[opn]);
                return;
            }

            assert(s_prime.unexecuted_learner_state == s.unexecuted_learner_state);
            assert(false);
        }

        assert(LReplicaNoReceiveNext(sched.replica, next_action_index, sched_prime.replica, ios));
        if next_action_index == 6 {
            assert(LReplicaNextSpontaneousMaybeExecute(
                sched.replica,
                sched_prime.replica,
                ExtractSentPacketsFromIos(ios),
            ));
            assert(LLearnerForgetDecision(s, s_prime, sched.replica.executor.ops_complete));
            if s.unexecuted_learner_state.contains_key(sched.replica.executor.ops_complete) {
                assert(s_prime.unexecuted_learner_state == s.unexecuted_learner_state.remove(
                    sched.replica.executor.ops_complete,
                ));
                if opn == sched.replica.executor.ops_complete {
                    assert(!s_prime.unexecuted_learner_state.contains_key(opn));
                    assert(false);
                }
            } else {
                assert(s_prime.unexecuted_learner_state == s.unexecuted_learner_state);
            }
        } else {
            assert(s_prime.unexecuted_learner_state == s.unexecuted_learner_state);
        }

        assert(s.unexecuted_learner_state.contains_key(opn));
        lemma_Received2bMessageSendersAlwaysNonempty(b, c, i - 1, learner_idx, opn);
        assert(s_prime.unexecuted_learner_state[opn] == s.unexecuted_learner_state[opn]);
    }

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
        assert(
            !(s_prime.max_ballot_seen == s.max_ballot_seen
                && s_prime.unexecuted_learner_state == s.unexecuted_learner_state)
        );
        assert(
            !(s.unexecuted_learner_state.contains_key(opn)
                && s.unexecuted_learner_state[opn].received_2b_message_senders.contains(sender)
                && s_prime.unexecuted_learner_state[opn].candidate_learned_value
                    == s.unexecuted_learner_state[opn].candidate_learned_value
                && s_prime.max_ballot_seen == s.max_ballot_seen)
        );

        let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i - 1, learner_idx);
        let next_action_index = b[i - 1].replicas[learner_idx].nextActionIndex;
        assert(next_action_index == 0);
        assert(ios[0] is Receive);
        let p = ios[0]->r;
        // The received 2b message's src is the sender that was added to received_2b_message_senders
        assert(p.msg is RslMessage2b);
        assert(p.src == sender);
        lemma_getsent2b_sender_index_witness(b, c, i, learner_idx, opn, sender, p);
        lemma_getsent2b_message_shape_from_receive(b, c, i, learner_idx, opn, sender, ios, p);
        let sender_idx = GetReplicaIndex(p.src, c.config);
        assert(0 <= sender_idx < c.config.replica_ids.len());
        assert(sender == c.config.replica_ids[sender_idx]);

        lemma_getsent2b_receive_packet_was_sent(b, c, i, learner_idx, ios, p);
        assert(b[i].environment.sentPackets.contains(p));
        lemma_getsent2b_value_matches_candidate(
            b,
            c,
            i,
            learner_idx,
            opn,
            sender,
            p,
        );
        assert(p.msg->opn_2b == opn);
        assert(p.msg->bal_2b == s_prime.max_ballot_seen);
        assert(p.msg->val_2b == s_prime.unexecuted_learner_state[opn].candidate_learned_value);
        return (sender_idx, p);
    }

    pub proof fn lemma_getsent2b_receive_packet_was_sent(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        learner_idx: int,
        ios: Seq<RslIo>,
        p: RslPacket,
    )
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 < i,
            0 <= learner_idx < b[i].replicas.len(),
            RslNextOneReplica(b[i - 1], b[i], learner_idx, ios),
            b[i - 1].environment.nextStep is LEnvStepHostIos,
            b[i - 1].environment.nextStep->ios == ios,
            ios.contains(LIoOp::Receive { r: p }),
        ensures
            b[i].environment.sentPackets.contains(p),
    {
        let e = b[i - 1].environment;
        let e_ = b[i].environment;
        let actor = e.nextStep->actor;
        assert(LEnvironment_Next(e, e_));
        assert(e.nextStep == LEnvStep::LEnvStepHostIos { actor, ios });
        assert(LEnvironment_PerformIos(e, e_, actor, ios));
        assert(forall |io| #![trigger ios.contains(io)] ios.contains(io) ==> match_ios_recv(io, e.sentPackets));
        assert(match_ios_recv(LIoOp::Receive { r: p }, e.sentPackets));
        assert(e.sentPackets.contains(p));
        lemma_PacketStaysInSentPackets(b, c, i - 1, i, p);
    }

    proof fn lemma_getsent2b_ballots_not_lt_each_way_implies_equal(a: Ballot, b: Ballot)
        requires
            !BalLt(a, b),
            !BalLt(b, a),
        ensures
            a == b,
    {
        if a != b {
            lemma_BalLtMiddle(a, b);
            assert(false);
        }
    }

    pub proof fn lemma_getsent2b_message_shape_from_learner_process2b(
        s: LLearner,
        s_prime: LLearner,
        opn: OperationNumber,
        sender: AbstractEndPoint,
        p: RslPacket,
    )
        requires
            p.msg is RslMessage2b,
            p.src == sender,
            LLearnerProcess2b(s, s_prime, p),
            s_prime.unexecuted_learner_state.contains_key(opn),
            s_prime.unexecuted_learner_state[opn].received_2b_message_senders.contains(sender),
            !(s_prime.max_ballot_seen == s.max_ballot_seen
                && s_prime.unexecuted_learner_state == s.unexecuted_learner_state),
            !(s.unexecuted_learner_state.contains_key(opn)
                && s.unexecuted_learner_state[opn].received_2b_message_senders.contains(sender)
                && s_prime.unexecuted_learner_state[opn].candidate_learned_value
                    == s.unexecuted_learner_state[opn].candidate_learned_value
                && s_prime.max_ballot_seen == s.max_ballot_seen),
        ensures
            p.msg->opn_2b == opn,
            p.msg->bal_2b == s_prime.max_ballot_seen,
    {
        let m = p.msg;
        if !s.constants.all.config.replica_ids.contains(p.src) || BalLt(m->bal_2b, s.max_ballot_seen) {
            assert(s_prime == s);
            assert(false);
        } else if BalLt(s.max_ballot_seen, m->bal_2b) {
            let tup_ = LearnerTuple{
                received_2b_message_senders: set![p.src],
                candidate_learned_value: m->val_2b,
            };
            assert(s_prime == LLearner{
                constants: s.constants,
                max_ballot_seen: m->bal_2b,
                unexecuted_learner_state: map![m->opn_2b => tup_],
            });
            if opn != m->opn_2b {
                assert(!s_prime.unexecuted_learner_state.contains_key(opn));
                assert(false);
            }
            assert(p.msg->opn_2b == opn);
            assert(p.msg->bal_2b == s_prime.max_ballot_seen);
        } else if !s.unexecuted_learner_state.contains_key(m->opn_2b) {
            let tup_ = LearnerTuple{
                received_2b_message_senders: set![p.src],
                candidate_learned_value: m->val_2b,
            };
            assert(s_prime == LLearner{
                constants: s.constants,
                max_ballot_seen: m->bal_2b,
                unexecuted_learner_state: s.unexecuted_learner_state.insert(m->opn_2b, tup_),
            });
            lemma_getsent2b_ballots_not_lt_each_way_implies_equal(m->bal_2b, s.max_ballot_seen);
            assert(s_prime.max_ballot_seen == s.max_ballot_seen);
            if opn != m->opn_2b {
                assert(s_prime.unexecuted_learner_state[opn] == s.unexecuted_learner_state[opn]);
                assert(s.unexecuted_learner_state.contains_key(opn));
                assert(s.unexecuted_learner_state[opn].received_2b_message_senders.contains(sender));
                assert(
                    s_prime.unexecuted_learner_state[opn].candidate_learned_value
                        == s.unexecuted_learner_state[opn].candidate_learned_value
                );
                assert(s_prime.max_ballot_seen == s.max_ballot_seen);
                assert(false);
            }
            assert(p.msg->opn_2b == opn);
            assert(p.msg->bal_2b == s_prime.max_ballot_seen);
        } else if s.unexecuted_learner_state[m->opn_2b].received_2b_message_senders.contains(p.src) {
            assert(s_prime == s);
            assert(false);
        } else {
            let tup = s.unexecuted_learner_state[m->opn_2b];
            let tup_ = LearnerTuple{
                received_2b_message_senders: tup.received_2b_message_senders + set![p.src],
                candidate_learned_value: tup.candidate_learned_value,
            };
            assert(s_prime == LLearner{
                constants: s.constants,
                max_ballot_seen: s.max_ballot_seen,
                unexecuted_learner_state: s.unexecuted_learner_state.insert(m->opn_2b, tup_),
            });
            if opn != m->opn_2b {
                assert(s_prime.unexecuted_learner_state[opn] == s.unexecuted_learner_state[opn]);
                assert(s.unexecuted_learner_state.contains_key(opn));
                assert(s.unexecuted_learner_state[opn].received_2b_message_senders.contains(sender));
                assert(
                    s_prime.unexecuted_learner_state[opn].candidate_learned_value
                        == s.unexecuted_learner_state[opn].candidate_learned_value
                );
                assert(s_prime.max_ballot_seen == s.max_ballot_seen);
                assert(false);
            }
            lemma_getsent2b_ballots_not_lt_each_way_implies_equal(m->bal_2b, s.max_ballot_seen);
            assert(m->bal_2b == s.max_ballot_seen);
            assert(s_prime.max_ballot_seen == s.max_ballot_seen);
            assert(p.msg->opn_2b == opn);
            assert(p.msg->bal_2b == s_prime.max_ballot_seen);
        }
    }

    pub proof fn lemma_getsent2b_message_shape_from_receive(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        learner_idx: int,
        opn: OperationNumber,
        sender: AbstractEndPoint,
        ios: Seq<RslIo>,
        p: RslPacket,
    )
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 < i,
            0 <= learner_idx < b[i].replicas.len(),
            b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state.contains_key(opn),
            b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state[opn].received_2b_message_senders.contains(sender),
            !(b[i].replicas[learner_idx].replica.learner.max_ballot_seen
                == b[i - 1].replicas[learner_idx].replica.learner.max_ballot_seen
                && b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state
                    == b[i - 1].replicas[learner_idx].replica.learner.unexecuted_learner_state),
            !(b[i - 1].replicas[learner_idx].replica.learner.unexecuted_learner_state.contains_key(opn)
                && b[i - 1].replicas[learner_idx].replica.learner.unexecuted_learner_state[opn].received_2b_message_senders.contains(sender)
                && b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state[opn].candidate_learned_value
                    == b[i - 1].replicas[learner_idx].replica.learner.unexecuted_learner_state[opn].candidate_learned_value
                && b[i].replicas[learner_idx].replica.learner.max_ballot_seen
                    == b[i - 1].replicas[learner_idx].replica.learner.max_ballot_seen),
            RslNextOneReplica(b[i - 1], b[i], learner_idx, ios),
            b[i - 1].replicas[learner_idx].nextActionIndex == 0,
            ios[0] is Receive,
            ios[0]->r == p,
            p.msg is RslMessage2b,
            p.src == sender,
        ensures
            p.msg->opn_2b == opn,
            p.msg->bal_2b == b[i].replicas[learner_idx].replica.learner.max_ballot_seen,
            LLearnerProcess2b(
                b[i - 1].replicas[learner_idx].replica.learner,
                b[i].replicas[learner_idx].replica.learner,
                p,
            ),
    {
        let sched = b[i - 1].replicas[learner_idx];
        let sched_prime = b[i].replicas[learner_idx];
        let s = sched.replica.learner;
        let s_prime = sched_prime.replica.learner;

        assert(LSchedulerNext(sched, sched_prime, ios));
        assert(LReplicaNextProcessPacket(sched.replica, sched_prime.replica, ios));
        assert(LReplicaNextProcessPacketWithoutReadingClock(sched.replica, sched_prime.replica, ios));
        assert(LReplicaNextProcess2b(sched.replica, sched_prime.replica, p, ExtractSentPacketsFromIos(ios)));

        let op_learnable = sched.replica.executor.ops_complete < p.msg->opn_2b
            || (sched.replica.executor.ops_complete == p.msg->opn_2b
                && sched.replica.executor.next_op_to_execute is OutstandingOpUnknown);
        if !op_learnable {
            assert(sched_prime.replica == sched.replica);
            assert(s_prime == s);
            assert(false);
        }
        assert(LLearnerProcess2b(s, s_prime, p));
        lemma_getsent2b_message_shape_from_learner_process2b(s, s_prime, opn, sender, p);
    }

    proof fn lemma_getsent2b_process2b_fresh_candidate(
        s: LLearner,
        s_prime: LLearner,
        opn: OperationNumber,
        p: RslPacket,
    )
        requires
            p.msg is RslMessage2b,
            p.msg->opn_2b == opn,
            LLearnerProcess2b(s, s_prime, p),
            !s.unexecuted_learner_state.contains_key(opn),
            s_prime.unexecuted_learner_state.contains_key(opn),
            !(s_prime.max_ballot_seen == s.max_ballot_seen
                && s_prime.unexecuted_learner_state == s.unexecuted_learner_state),
        ensures
            p.msg->val_2b
                == s_prime.unexecuted_learner_state[opn].candidate_learned_value,
    {
        let m = p.msg;
        if !s.constants.all.config.replica_ids.contains(p.src)
            || BalLt(m->bal_2b, s.max_ballot_seen)
        {
            assert(s_prime == s);
            assert(false);
        } else if BalLt(s.max_ballot_seen, m->bal_2b) {
            let tup_ = LearnerTuple{
                received_2b_message_senders: set![p.src],
                candidate_learned_value: m->val_2b,
            };
            assert(s_prime == LLearner{
                constants: s.constants,
                max_ballot_seen: m->bal_2b,
                unexecuted_learner_state: map![m->opn_2b => tup_],
            });
        } else if !s.unexecuted_learner_state.contains_key(m->opn_2b) {
            let tup_ = LearnerTuple{
                received_2b_message_senders: set![p.src],
                candidate_learned_value: m->val_2b,
            };
            assert(s_prime == LLearner{
                constants: s.constants,
                max_ballot_seen: m->bal_2b,
                unexecuted_learner_state: s.unexecuted_learner_state.insert(m->opn_2b, tup_),
            });
        } else {
            assert(false);
        }
    }

    proof fn lemma_getsent2b_process2b_preserves_or_selects_candidate(
        s: LLearner,
        s_prime: LLearner,
        opn: OperationNumber,
        p: RslPacket,
    )
        requires
            p.msg is RslMessage2b,
            p.msg->opn_2b == opn,
            LLearnerProcess2b(s, s_prime, p),
            s.unexecuted_learner_state.contains_key(opn),
            s_prime.unexecuted_learner_state.contains_key(opn),
            !(s_prime.max_ballot_seen == s.max_ballot_seen
                && s_prime.unexecuted_learner_state == s.unexecuted_learner_state),
        ensures
            p.msg->val_2b
                == s_prime.unexecuted_learner_state[opn].candidate_learned_value
            || (s_prime.unexecuted_learner_state[opn].candidate_learned_value
                    == s.unexecuted_learner_state[opn].candidate_learned_value
                && p.msg->bal_2b == s.max_ballot_seen),
    {
        let m = p.msg;
        if !s.constants.all.config.replica_ids.contains(p.src)
            || BalLt(m->bal_2b, s.max_ballot_seen)
        {
            assert(s_prime == s);
            assert(false);
        } else if BalLt(s.max_ballot_seen, m->bal_2b) {
            let tup_ = LearnerTuple{
                received_2b_message_senders: set![p.src],
                candidate_learned_value: m->val_2b,
            };
            assert(s_prime == LLearner{
                constants: s.constants,
                max_ballot_seen: m->bal_2b,
                unexecuted_learner_state: map![m->opn_2b => tup_],
            });
        } else if !s.unexecuted_learner_state.contains_key(m->opn_2b) {
            assert(false);
        } else if s.unexecuted_learner_state[m->opn_2b].received_2b_message_senders.contains(
            p.src,
        ) {
            assert(s_prime == s);
            assert(false);
        } else {
            let tup = s.unexecuted_learner_state[m->opn_2b];
            let tup_ = LearnerTuple{
                received_2b_message_senders: tup.received_2b_message_senders + set![p.src],
                candidate_learned_value: tup.candidate_learned_value,
            };
            assert(s_prime == LLearner{
                constants: s.constants,
                max_ballot_seen: s.max_ballot_seen,
                unexecuted_learner_state: s.unexecuted_learner_state.insert(m->opn_2b, tup_),
            });
            lemma_getsent2b_ballots_not_lt_each_way_implies_equal(
                m->bal_2b, s.max_ballot_seen);
        }
    }

    #[verifier(spinoff_prover)]
    proof fn lemma_getsent2b_existing_candidate_witness(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        learner_idx: int,
        opn: OperationNumber,
    ) -> (p2: RslPacket)
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 < i,
            0 <= learner_idx < b[i - 1].replicas.len(),
            b[i - 1].replicas[learner_idx].replica.learner
                .unexecuted_learner_state.contains_key(opn),
        ensures
            b[i].environment.sentPackets.contains(p2),
            c.config.replica_ids.contains(p2.src),
            p2.msg is RslMessage2b,
            p2.msg->opn_2b == opn,
            p2.msg->bal_2b
                == b[i - 1].replicas[learner_idx].replica.learner.max_ballot_seen,
            p2.msg->val_2b
                == b[i - 1].replicas[learner_idx].replica.learner
                    .unexecuted_learner_state[opn].candidate_learned_value,
        decreases i, 0int,
    {
        let s = b[i - 1].replicas[learner_idx].replica.learner;
        lemma_Received2bMessageSendersAlwaysNonempty(b, c, i - 1, learner_idx, opn);
        let senders = s.unexecuted_learner_state[opn].received_2b_message_senders;
        vstd::set::lemma_set_choose_len(senders);
        let sender2 = senders.choose();
        let (sender2_idx_unused, p2) = lemma_GetSent2bMessageFromLearnerState(
            b, c, i - 1, learner_idx, opn, sender2);
        assert(b[i].environment.sentPackets.contains(p2)) by {
            lemma_PacketStaysInSentPackets(b, c, i - 1, i, p2);
        };
        assert(c.config.replica_ids.contains(p2.src)) by {};
        p2
    }

    proof fn lemma_getsent2b_packets_with_same_ballot_and_opn_match(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        p: RslPacket,
        p2: RslPacket,
    )
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            b[i].environment.sentPackets.contains(p),
            b[i].environment.sentPackets.contains(p2),
            c.config.replica_ids.contains(p.src),
            c.config.replica_ids.contains(p2.src),
            p.msg is RslMessage2b,
            p2.msg is RslMessage2b,
            p.msg->opn_2b == p2.msg->opn_2b,
            p.msg->bal_2b == p2.msg->bal_2b,
        ensures p.msg->val_2b == p2.msg->val_2b,
    {
        let p_2a = lemma_2bMessageHasCorresponding2aMessage(b, c, i, p);
        let p2_2a = lemma_2bMessageHasCorresponding2aMessage(b, c, i, p2);
        lemma_2aMessagesFromSameBallotAndOperationMatch(b, c, i, p_2a, p2_2a);
        assert(p.msg->val_2b == p2.msg->val_2b);
    }

    proof fn lemma_getsent2b_existing_candidate_matches_packet(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        learner_idx: int,
        opn: OperationNumber,
        p: RslPacket,
    )
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 < i,
            0 <= learner_idx < b[i - 1].replicas.len(),
            b[i - 1].replicas[learner_idx].replica.learner
                .unexecuted_learner_state.contains_key(opn),
            b[i].environment.sentPackets.contains(p),
            c.config.replica_ids.contains(p.src),
            p.msg is RslMessage2b,
            p.msg->opn_2b == opn,
            p.msg->bal_2b
                == b[i - 1].replicas[learner_idx].replica.learner.max_ballot_seen,
        ensures
            p.msg->val_2b
                == b[i - 1].replicas[learner_idx].replica.learner
                    .unexecuted_learner_state[opn].candidate_learned_value,
        decreases i, 1int,
    {
        let p2 = lemma_getsent2b_existing_candidate_witness(
            b, c, i, learner_idx, opn);
        lemma_getsent2b_packets_with_same_ballot_and_opn_match(b, c, i, p, p2);
    }

    pub proof fn lemma_getsent2b_value_matches_candidate(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        learner_idx: int,
        opn: OperationNumber,
        sender: AbstractEndPoint,
        p: RslPacket,
    )
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 < i,
            0 <= learner_idx < b[i].replicas.len(),
            b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state.contains_key(opn),
            b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state[opn].received_2b_message_senders.contains(sender),
            p.msg is RslMessage2b,
            p.src == sender,
            p.msg->opn_2b == opn,
            p.msg->bal_2b == b[i].replicas[learner_idx].replica.learner.max_ballot_seen,
            b[i].environment.sentPackets.contains(p),
            LLearnerProcess2b(
                b[i - 1].replicas[learner_idx].replica.learner,
                b[i].replicas[learner_idx].replica.learner,
                p,
            ),
            !(b[i].replicas[learner_idx].replica.learner.max_ballot_seen
                == b[i - 1].replicas[learner_idx].replica.learner.max_ballot_seen
                && b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state
                    == b[i - 1].replicas[learner_idx].replica.learner.unexecuted_learner_state),
        ensures
            p.msg->val_2b == b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state[opn].candidate_learned_value,
        decreases i, 2int,
    {
        let s = b[i - 1].replicas[learner_idx].replica.learner;
        let s_prime = b[i].replicas[learner_idx].replica.learner;
        if !s.unexecuted_learner_state.contains_key(opn) {
            lemma_getsent2b_process2b_fresh_candidate(s, s_prime, opn, p);
            return;
        }
        lemma_getsent2b_process2b_preserves_or_selects_candidate(s, s_prime, opn, p);
        if p.msg->val_2b != s_prime.unexecuted_learner_state[opn].candidate_learned_value {
            assert(s.unexecuted_learner_state.contains_key(opn));
            assert(p.msg->bal_2b == s.max_ballot_seen);
            lemma_Received2bMessageSendersAlwaysValidReplicas(b, c, i, learner_idx, opn);
            assert(c.config.replica_ids.contains(p.src));
            assert(0 <= learner_idx < b[i - 1].replicas.len());
            lemma_getsent2b_existing_candidate_matches_packet(
                b, c, i, learner_idx, opn, p);
            assert(false);
        }
    }

    pub proof fn lemma_getsent2b_sender_index_witness(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        learner_idx: int,
        opn: OperationNumber,
        sender: AbstractEndPoint,
        p: RslPacket,
    )
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            0 <= learner_idx < b[i].replicas.len(),
            b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state.contains_key(opn),
            b[i].replicas[learner_idx].replica.learner.unexecuted_learner_state[opn].received_2b_message_senders.contains(sender),
            p.src == sender,
        ensures
            ({
                let sender_idx = GetReplicaIndex(p.src, c.config);
                &&& 0 <= sender_idx < c.config.replica_ids.len()
                &&& sender == c.config.replica_ids[sender_idx]
            }),
    {
        lemma_Received2bMessageSendersAlwaysValidReplicas(b, c, i, learner_idx, opn);
        assert(c.config.replica_ids.contains(sender));
        assert(c.config.replica_ids.contains(p.src));
        lemma_FindIndexInSeq(c.config.replica_ids, p.src);
        let sender_idx = GetReplicaIndex(p.src, c.config);
        assert(0 <= sender_idx < c.config.replica_ids.len());
        assert(c.config.replica_ids[sender_idx] == p.src);
        assert(sender == c.config.replica_ids[sender_idx]);
    }

}
