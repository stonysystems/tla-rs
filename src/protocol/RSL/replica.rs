use crate::protocol::RSL::acceptor::*;
use crate::protocol::RSL::broadcast::*;
use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::election::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::executor::*;
use crate::protocol::RSL::learner::*;
use crate::protocol::RSL::message::*;
use crate::protocol::RSL::proposer::*;
use crate::protocol::RSL::state_machine::*;
use crate::protocol::RSL::types::*;
use vstd::prelude::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

use crate::protocol::common::upper_bound::*;

use crate::services::RSL::app_state_machine::*;

use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;

verus! {
    pub struct LReplica{
        pub constants:LReplicaConstants,
        pub nextHeartbeatTime:int,
        pub proposer:LProposer,
        pub acceptor:LAcceptor,
        pub learner:LLearner,
        pub executor:LExecutor
    }

    pub open spec fn LReplicaInit(r:LReplica, c:LReplicaConstants) -> bool
        recommends
            WellFormedLConfiguration(c.all.config)
    {
        &&& r.constants == c
        &&& r.nextHeartbeatTime == 0
        &&& LProposerInit(r.proposer, c)
        &&& LAcceptorInit(r.acceptor, c)
        &&& LLearnerInit(r.learner, c)
        &&& LExecutorInit(r.executor, c)
    }

    pub open spec fn LReplicaNextProcessInvalid(
        s:LReplica,
        s_:LReplica,
        received_packet:RslPacket,
        sent_packets:Seq<RslPacket>
    ) -> bool
    recommends received_packet.msg is RslMessageInvalid
    {
        &&& s_ == s
        &&& sent_packets == Seq::<RslPacket>::empty()
    }

    pub open spec fn LReplicaNextProcessRequest(
        s:LReplica,
        s_:LReplica,
        received_packet:RslPacket,
        sent_packets:Seq<RslPacket>
    ) -> bool
    recommends received_packet.msg is RslMessageRequest
    {
        if s.executor.reply_cache.contains_key(received_packet.src)
            // && s.executor.reply_cache[received_packet.src] is Reply
            && received_packet.msg->seqno_req <= s.executor.reply_cache[received_packet.src].seqno
        {
            &&& LExecutorProcessRequest(s.executor, received_packet, sent_packets)
            &&& s_ == s
        } else {
            &&& LProposerProcessRequest(s.proposer, s_.proposer, received_packet)
            &&& s_ == LReplica {
                constants:s.constants,
                nextHeartbeatTime:s.nextHeartbeatTime,
                proposer:s_.proposer,
                acceptor:s.acceptor,
                learner:s.learner,
                executor:s.executor
            }
            &&& sent_packets == Seq::<RslPacket>::empty()
        }
    }

    pub open spec fn LReplicaNextProcess1a(
        s:LReplica,
        s_:LReplica,
        received_packet:RslPacket,
        sent_packets:Seq<RslPacket>
    ) -> bool
    recommends received_packet.msg is RslMessage1a
    {
        &&& LAcceptorProcess1a(s.acceptor, s_.acceptor, received_packet, sent_packets)
        // UNCHANGED
        &&& s_ == LReplica {
            constants:s.constants,
            nextHeartbeatTime:s.nextHeartbeatTime,
            proposer:s.proposer,
            acceptor:s_.acceptor,
            learner:s.learner,
            executor:s.executor
        }
    }

    pub open spec fn LReplicaNextProcess1b(
        s:LReplica,
        s_:LReplica,
        received_packet:RslPacket,
        sent_packets:Seq<RslPacket>
    ) -> bool
    recommends received_packet.msg is RslMessage1b
    {
        if s.proposer.constants.all.config.replica_ids.contains(received_packet.src)
            && received_packet.msg->bal_1b == s.proposer.max_ballot_i_sent_1a
            && s.proposer.current_state == 1
            && (forall |other_packet:RslPacket| s.proposer.received_1b_packets.contains(other_packet) ==> other_packet.src != received_packet.src)
        {
            &&& LProposerProcess1b(s.proposer, s_.proposer, received_packet)
            &&& LAcceptorTruncateLog(s.acceptor, s_.acceptor, received_packet.msg->log_truncation_point)
            &&& sent_packets == Seq::<RslPacket>::empty()
            &&& s_ == LReplica {
                constants:s.constants,
                nextHeartbeatTime:s.nextHeartbeatTime,
                proposer:s_.proposer,
                acceptor:s_.acceptor,
                learner:s.learner,
                executor:s.executor
            }
        } else {
            &&& s_ == s
            &&& sent_packets == Seq::<RslPacket>::empty()
        }
    }

    pub open spec fn LReplicaNextProcessStartingPhase2(
        s:LReplica,
        s_:LReplica,
        received_packet:RslPacket,
        sent_packets:Seq<RslPacket>
    ) -> bool
    recommends received_packet.msg is RslMessageStartingPhase2
    {
        &&& LExecutorProcessStartingPhase2(s.executor, s_.executor, received_packet, sent_packets)
        &&& s_ == LReplica {
            constants:s.constants,
            nextHeartbeatTime:s.nextHeartbeatTime,
            proposer:s.proposer,
            acceptor:s.acceptor,
            learner:s.learner,
            executor:s_.executor
        }
    }

    pub open spec fn LReplicaNextProcess2a(
        s:LReplica,
        s_:LReplica,
        received_packet:RslPacket,
        sent_packets:Seq<RslPacket>
    ) -> bool
    recommends received_packet.msg is RslMessage2a
    {
        let m = received_packet.msg;
        if s.acceptor.constants.all.config.replica_ids.contains(received_packet.src)
            && BalLeq(s.acceptor.max_bal, m->bal_2a)
            && LeqUpperBound(m->opn_2a, s.acceptor.constants.all.params.max_integer_val)
        {
            &&& LAcceptorProcess2a(s.acceptor, s_.acceptor, received_packet, sent_packets)
            &&& s_ == LReplica {
                constants:s.constants,
                nextHeartbeatTime:s.nextHeartbeatTime,
                proposer:s.proposer,
                acceptor:s_.acceptor,
                learner:s.learner,
                executor:s.executor
            }
        } else {
            &&& s_ == s
            &&& sent_packets == Seq::<RslPacket>::empty()
        }
    }

    pub open spec fn LReplicaNextProcess2b(
        s:LReplica,
        s_:LReplica,
        received_packet:RslPacket,
        sent_packets:Seq<RslPacket>
    ) -> bool
    recommends received_packet.msg is RslMessage2b
    {
        let opn = received_packet.msg->opn_2b;
        let op_learnable = s.executor.ops_complete < opn || (s.executor.ops_complete == opn && s.executor.next_op_to_execute is OutstandingOpUnknown);
        if op_learnable {
            &&& LLearnerProcess2b(s.learner, s_.learner, received_packet)
            &&& s_ == LReplica {
                constants:s.constants,
                nextHeartbeatTime:s.nextHeartbeatTime,
                proposer:s.proposer,
                acceptor:s.acceptor,
                learner:s_.learner,
                executor:s.executor
            }
            &&& sent_packets == Seq::<RslPacket>::empty()
        } else {
            &&& s_ == s
            &&& sent_packets == Seq::<RslPacket>::empty()
        }
    }

    pub open spec fn LReplicaNextProcessReply(
        s:LReplica,
        s_:LReplica,
        received_packet:RslPacket,
        sent_packets:Seq<RslPacket>
    ) -> bool
    recommends received_packet.msg is RslMessageReply
    {
        &&& s_ == s
        &&& sent_packets == Seq::<RslPacket>::empty()
    }

    pub open spec fn LReplicaNextProcessAppStateSupply(
        s:LReplica,
        s_:LReplica,
        received_packet:RslPacket,
        sent_packets:Seq<RslPacket>
    ) -> bool
    recommends received_packet.msg is RslMessageAppStateSupply
    {
        if s.executor.constants.all.config.replica_ids.contains(received_packet.src)
            && received_packet.msg->opn_state_supply > s.executor.ops_complete
        {
            &&& LLearnerForgetOperationsBefore(s.learner, s_.learner, received_packet.msg->opn_state_supply)
            &&& LExecutorProcessAppStateSupply(s.executor, s_.executor, received_packet)
            &&& s_ == LReplica {
                constants:s.constants,
                nextHeartbeatTime:s.nextHeartbeatTime,
                proposer:s.proposer,
                acceptor:s.acceptor,
                learner:s_.learner,
                executor:s_.executor
            }
            &&& sent_packets == Seq::<RslPacket>::empty()
        } else {
            &&& s_ == s
            &&& sent_packets == Seq::<RslPacket>::empty()
        }
    }

    pub open spec fn LReplicaNextProcessAppStateRequest(
        s:LReplica,
        s_:LReplica,
        received_packet:RslPacket,
        sent_packets:Seq<RslPacket>
    ) -> bool
    recommends received_packet.msg is RslMessageAppStateRequest
    {
        &&& LExecutorProcessAppStateRequest(s.executor, s_.executor, received_packet, sent_packets)
        &&& s_ == LReplica {
            constants:s.constants,
            nextHeartbeatTime:s.nextHeartbeatTime,
            proposer:s.proposer,
            acceptor:s.acceptor,
            learner:s.learner,
            executor:s_.executor
        }
    }

    pub open spec fn LReplicaNextProcessHeartbeat(
        s:LReplica,
        s_:LReplica,
        received_packet:RslPacket,
        clock:int,
        sent_packets:Seq<RslPacket>
    ) -> bool
    recommends received_packet.msg is RslMessageHeartbeat
    {
        &&& LProposerProcessHeartbeat(s.proposer, s_.proposer, received_packet, clock)
        &&& LAcceptorProcessHeartbeat(s.acceptor, s_.acceptor, received_packet)
        &&& s_ == LReplica {
            constants:s.constants,
            nextHeartbeatTime:s.nextHeartbeatTime,
            proposer:s_.proposer,
            acceptor:s_.acceptor,
            learner:s.learner,
            executor:s.executor
        }
        &&& sent_packets == Seq::<RslPacket>::empty()
    }

    pub open spec fn LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(
        s:LReplica,
        s_:LReplica,
        sent_packets:Seq<RslPacket>
    ) -> bool
    {
        &&& LProposerMaybeEnterNewViewAndSend1a(s.proposer, s_.proposer, sent_packets)
        &&& s_ == LReplica {
            constants:s.constants,
            nextHeartbeatTime:s.nextHeartbeatTime,
            proposer:s_.proposer,
            acceptor:s.acceptor,
            learner:s.learner,
            executor:s.executor
        }
    }

    pub open spec fn LReplicaNextSpontaneousMaybeEnterPhase2(
        s:LReplica,
        s_:LReplica,
        sent_packets:Seq<RslPacket>
    ) -> bool
    {
        &&& LProposerMaybeEnterPhase2(s.proposer, s_.proposer, s.acceptor.log_truncation_point, sent_packets)
        &&& s_ == LReplica {
            constants:s.constants,
            nextHeartbeatTime:s.nextHeartbeatTime,
            proposer:s_.proposer,
            acceptor:s.acceptor,
            learner:s.learner,
            executor:s.executor
        }
    }

    pub open spec fn LReplicaNextReadClockMaybeNominateValueAndSend2a(
        s:LReplica,
        s_:LReplica,
        clock:ClockReading,
        sent_packets:Seq<RslPacket>
    ) -> bool
    {
        &&& LProposerMaybeNominateValueAndSend2a(s.proposer, s_.proposer, clock.t, s.acceptor.log_truncation_point, sent_packets)
        &&& s_ == LReplica {
            constants:s.constants,
            nextHeartbeatTime:s.nextHeartbeatTime,
            proposer:s_.proposer,
            acceptor:s.acceptor,
            learner:s.learner,
            executor:s.executor
        }
    }

    pub open spec fn LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(
        s:LReplica,
        s_:LReplica,
        sent_packets:Seq<RslPacket>
    ) -> bool
    {
        exists |opn:OperationNumber| s.acceptor.last_checkpointed_operation.contains(opn)
                                    && IsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config)
                                    && if opn > s.acceptor.log_truncation_point {
                                        &&& LAcceptorTruncateLog(s.acceptor, s_.acceptor, opn)
                                        &&& s_ == LReplica {
                                            constants:s.constants,
                                            nextHeartbeatTime:s.nextHeartbeatTime,
                                            proposer:s.proposer,
                                            acceptor:s_.acceptor,
                                            learner:s.learner,
                                            executor:s.executor
                                        }
                                        &&& sent_packets == Seq::<RslPacket>::empty()
                                    } else {
                                        &&& s_ == s
                                        &&& sent_packets == Seq::<RslPacket>::empty()
                                    }
    }

    pub open spec fn LReplicaNextSpontaneousMaybeMakeDecision(
        s:LReplica,
        s_:LReplica,
        sent_packets:Seq<RslPacket>
    ) -> bool
    {
        let opn = s.executor.ops_complete;
        if s.executor.next_op_to_execute is OutstandingOpUnknown
            && s.learner.unexecuted_learner_state.contains_key(opn)
            && s.learner.unexecuted_learner_state[opn].received_2b_message_senders.len() >= LMinQuorumSize(s.learner.constants.all.config)
        {
            &&& LExecutorGetDecision(s.executor, s_.executor, s.learner.max_ballot_seen, opn,
                           s.learner.unexecuted_learner_state[opn].candidate_learned_value)
            &&& s_ == LReplica {
                constants:s.constants,
                nextHeartbeatTime:s.nextHeartbeatTime,
                proposer:s.proposer,
                acceptor:s.acceptor,
                learner:s.learner,
                executor:s_.executor
            }
            &&& sent_packets == Seq::<RslPacket>::empty()
        } else {
            &&& s_ == s
            &&& sent_packets == Seq::<RslPacket>::empty()
        }
    }

    pub open spec fn LReplicaNextSpontaneousMaybeExecute(
        s:LReplica,
        s_:LReplica,
        sent_packets:Seq<RslPacket>
    ) -> bool
    {
        if s.executor.next_op_to_execute is OutstandingOpKnown
            && LtUpperBound(s.executor.ops_complete, s.executor.constants.all.params.max_integer_val)
            && LReplicaConstantsValid(s.executor.constants)
        {
            let v = s.executor.next_op_to_execute->v;
            &&& LProposerResetViewTimerDueToExecution(s.proposer, s_.proposer, v)
            &&& LLearnerForgetDecision(s.learner, s_.learner, s.executor.ops_complete)
            &&& LExecutorExecute(s.executor, s_.executor, sent_packets)
            &&& s_ == LReplica {
                constants:s.constants,
                nextHeartbeatTime:s.nextHeartbeatTime,
                proposer:s_.proposer,
                acceptor:s.acceptor,
                learner:s_.learner,
                executor:s_.executor
            }
        } else {
            &&& s_ == s
            &&& sent_packets == Seq::<RslPacket>::empty()
        }
    }

    pub open spec fn LReplicaNextReadClockMaybeSendHeartbeat(
        s:LReplica,
        s_:LReplica,
        clock:ClockReading,
        sent_packets:Seq<RslPacket>
    ) -> bool
    {
        if clock.t < s.nextHeartbeatTime
        {
            &&& s_ == s
            &&& sent_packets == Seq::<RslPacket>::empty()
        } else {
            &&& s_.nextHeartbeatTime == UpperBoundedAddition(clock.t, s.constants.all.params.heartbeat_period, s.constants.all.params.max_integer_val)
            &&& LBroadcastToEveryone(s.constants.all.config, s.constants.my_index,
                                    RslMessage::RslMessageHeartbeat{
                                        bal_heartbeat:s.proposer.election_state.current_view,
                                        suspicious:s.proposer.election_state.current_view_suspectors.contains(s.constants.my_index),
                                        opn_ckpt:s.executor.ops_complete
                                    },
                                    sent_packets)
            &&& s_ == LReplica {
                constants:s.constants,
                nextHeartbeatTime:s_.nextHeartbeatTime,
                proposer:s.proposer,
                acceptor:s.acceptor,
                learner:s.learner,
                executor:s.executor
            }
        }
    }

    pub open spec fn LReplicaNextReadClockCheckForViewTimeout(
        s:LReplica,
        s_:LReplica,
        clock:ClockReading,
        sent_packets:Seq<RslPacket>
    ) -> bool
    {
        &&& LProposerCheckForViewTimeout(s.proposer, s_.proposer, clock.t)
        &&& s_ == LReplica {
            constants:s.constants,
            nextHeartbeatTime:s.nextHeartbeatTime,
            proposer:s_.proposer,
            acceptor:s.acceptor,
            learner:s.learner,
            executor:s.executor
        }
        &&& sent_packets == Seq::<RslPacket>::empty()
    }

    pub open spec fn LReplicaNextReadClockCheckForQuorumOfViewSuspicions(
        s:LReplica,
        s_:LReplica,
        clock:ClockReading,
        sent_packets:Seq<RslPacket>
    ) -> bool
    {
        &&& LProposerCheckForQuorumOfViewSuspicions(s.proposer, s_.proposer, clock.t)
        &&& s_ == LReplica {
            constants:s.constants,
            nextHeartbeatTime:s.nextHeartbeatTime,
            proposer:s_.proposer,
            acceptor:s.acceptor,
            learner:s.learner,
            executor:s.executor
        }
        &&& sent_packets == Seq::<RslPacket>::empty()
    }

    pub open spec fn ExtractSentPacketsFromIos(ios:Seq<RslIo>) -> (res:Seq<RslPacket>)
        // ensures
        //     forall |p:RslPacket| res.contains(p) <==> ios.contains(LIoOp::Send{s:p})
        decreases ios.len()
    {
        if ios.len() == 0 {
            Seq::<RslPacket>::empty()
        } else if ios[0] is Send {
            seq![ios[0]->s] + ExtractSentPacketsFromIos(ios.drop_first())
        } else {
            ExtractSentPacketsFromIos(ios.drop_first())
        }
    }

    #[verifier::external_body]
    pub proof fn lemma_ExtractSentPacketsFromIos(ios:Seq<RslIo>)
        ensures forall |p:RslPacket| ExtractSentPacketsFromIos(ios).contains(p) <==> ios.contains(LIoOp::Send{s:p})
    {

    }

    pub proof fn ExtractSentPacketsFromIos_Ensures1(ios:Seq<RslIo>)
        ensures forall |p:RslPacket| ExtractSentPacketsFromIos(ios).contains(p) ==> ios.contains(LIoOp::Send{s:p})
        decreases ios.len()
    {
        if ios.len() == 0 {
            assert(forall |p:RslPacket| ExtractSentPacketsFromIos(ios).contains(p) ==> ios.contains(LIoOp::Send{s:p}));
        } else {
            ExtractSentPacketsFromIos_Ensures1(ios.drop_first());

            let first = ios[0];
            let rest = ios.drop_first();

            if first is Send {
                let p = first->s;
                let rest_p = ExtractSentPacketsFromIos(rest);
                let front_p = seq![ios[0]->s];
                assert(forall |p:RslPacket| rest_p.contains(p) ==> ios.contains(LIoOp::Send{s:p}));
                assert(forall |p:RslPacket| front_p.contains(p) ==> ios.contains(LIoOp::Send{s:p}));
                assert(ExtractSentPacketsFromIos(ios) == front_p + rest_p);

                let pkts = front_p + rest_p;
                SeqConcatenate(front_p, rest_p);
                assert(forall |p:RslPacket| front_p.contains(p) || rest_p.contains(p) <==> pkts.contains(p));
                assert(forall |p:RslPacket| pkts.contains(p) ==> ios.contains(LIoOp::Send{s:p}));
                assert(forall |p:RslPacket| ExtractSentPacketsFromIos(ios).contains(p) ==> ios.contains(LIoOp::Send{s:p}));


                // assert(forall |p:RslPacket| ios.contains(LIoOp::Send{s:p}) ==> ExtractSentPacketsFromIos(ios).contains(p));

                // assert(forall |p:RslPacket| ExtractSentPacketsFromIos(ios).contains(p) <==> ios.contains(LIoOp::Send{s:p}));
            }
        }
    }

    #[verifier(external_body)]
    // #[verifier(opaque)]
    pub proof fn ExtractSentPacketsFromIos_Ensures2(ios:Seq<RslIo>)
        ensures forall |p:RslPacket| ios.contains(LIoOp::Send{s:p}) ==> ExtractSentPacketsFromIos(ios).contains(p)
    {
        assume(forall |p:RslPacket| ios.contains(LIoOp::Send{s:p}) ==> ExtractSentPacketsFromIos(ios).contains(p));
    }

    pub proof fn SeqConcatenate<T>(s1:Seq<T>, s2:Seq<T>)
        ensures forall |i:T| s1.contains(i) || s2.contains(i) <==> (s1+s2).contains(i)
    {
        let s = s1+s2;
        assert forall |i: T| s1.contains(i) || s2.contains(i) implies s.contains(i) by {
            if s1.contains(i) {
                let idx = choose |idx: int| 0 <= idx < s1.len() && s1[idx] == i;
                assert(s.contains(i)) by {
                    let new_idx = idx;
                    assert(s[new_idx] == i);
                };
            } else if s2.contains(i) {
                let idx = choose |idx: int| 0 <= idx < s2.len() && s2[idx] == i;
                assert(s.contains(i)) by {
                    let new_idx = s1.len() + idx;
                    assert(s[new_idx] == i);
                };
            }
        }

        assert(forall |i:T| s.contains(i) ==> s1.contains(i) || s2.contains(i));
    }


    pub open spec fn LReplicaNextReadClockAndProcessPacket(s:LReplica, s_:LReplica, ios:Seq<RslIo>) -> bool
        recommends
            ios.len() >= 1,
            ios[0] is Receive,
            ios[0]->r.msg is RslMessageHeartbeat,
    {
        &&& ios.len() > 1
        &&& ios[1] is ReadClock
        &&& (forall |io: RslIo| ios.subrange(2, ios.len() as int).contains(io) ==> io is Send)
        &&& LReplicaNextProcessHeartbeat(s, s_, ios[0]->r, ios[1]->t, ExtractSentPacketsFromIos(ios))
    }

    pub open spec fn LReplicaNextProcessPacketWithoutReadingClock(s:LReplica, s_:LReplica, ios:Seq<RslIo>) -> bool
        recommends
            ios.len() >= 1,
            ios[0] is Receive,
            !(ios[0]->r.msg is RslMessageHeartbeat),
    {
        let sent_packets = ExtractSentPacketsFromIos(ios);
        &&& (forall |io: RslIo| ios.drop_first().contains(io) ==> io is Send)
        &&& match ios[0]->r.msg {
                RslMessage::RslMessageInvalid{} => LReplicaNextProcessInvalid(s, s_, ios[0]->r, sent_packets),
                RslMessage::RslMessageRequest{seqno_req, val} => LReplicaNextProcessRequest(s, s_, ios[0]->r, sent_packets),
                RslMessage::RslMessage1a{bal_1a} => LReplicaNextProcess1a(s, s_, ios[0]->r, sent_packets),
                RslMessage::RslMessage1b{bal_1b, log_truncation_point, votes} => LReplicaNextProcess1b(s, s_, ios[0]->r, sent_packets),
                RslMessage::RslMessageStartingPhase2{bal_2, logTruncationPoint_2} => LReplicaNextProcessStartingPhase2(s, s_, ios[0]->r, sent_packets),
                RslMessage::RslMessage2a{bal_2a, opn_2a, val_2a} => LReplicaNextProcess2a(s, s_, ios[0]->r, sent_packets),
                RslMessage::RslMessage2b{bal_2b, opn_2b, val_2b} => LReplicaNextProcess2b(s, s_, ios[0]->r, sent_packets),
                RslMessage::RslMessageReply{seqno_reply, reply} => LReplicaNextProcessReply(s, s_, ios[0]->r, sent_packets),
                RslMessage::RslMessageAppStateRequest{bal_state_req, opn_state_req} => LReplicaNextProcessAppStateRequest(s, s_, ios[0]->r, sent_packets),
                RslMessage::RslMessageAppStateSupply{bal_state_supply, opn_state_supply, app_state, reply_cache} => LReplicaNextProcessAppStateSupply(s, s_, ios[0]->r, sent_packets),
                RslMessage::RslMessageHeartbeat{bal_heartbeat, suspicious, opn_ckpt} => false
            }
    }

    pub open spec fn LReplicaNextProcessPacket(s:LReplica, s_:LReplica, ios:Seq<RslIo>) -> bool
    {
        &&& ios.len() >= 1
        &&& if ios[0] is TimeoutReceive {
            &&& s_ == s
            &&& ios.len() == 1
        } else {
            &&& ios[0] is Receive
            &&& if ios[0]->r.msg is RslMessageHeartbeat {
                LReplicaNextReadClockAndProcessPacket(s, s_, ios)
            } else {
                LReplicaNextProcessPacketWithoutReadingClock(s, s_, ios)
            }
        }
    }

    pub open spec fn LReplicaNumActions() -> int
    {
      10
    }

    pub open spec fn SpontaneousIos(ios:Seq<RslIo>, clocks:int) -> bool
        recommends 0<=clocks<=1
    {
        &&& clocks <= ios.len()
        &&& (forall |i:int| 0<=i<clocks ==> ios[i] is ReadClock)
        &&& (forall |i:int| clocks<=i<ios.len() ==> ios[i] is Send)
    }

    pub open spec fn SpontaneousClock(ios:Seq<RslIo>) -> ClockReading
    {
        if SpontaneousIos(ios, 1){
            ClockReading{t:ios[0]->t}
        } else {
            ClockReading{t:0}
        }
    }

    pub open spec fn LReplicaNoReceiveNext(s:LReplica, nextActionIndex:int, s_:LReplica, ios:Seq<RslIo>) -> bool
    {
        let sent_packets = ExtractSentPacketsFromIos(ios);

        if nextActionIndex == 1 {
            &&& SpontaneousIos(ios, 0)
            &&& LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s, s_, sent_packets)
        } else if nextActionIndex == 2 {
            &&& SpontaneousIos(ios, 0)
            &&& LReplicaNextSpontaneousMaybeEnterPhase2(s, s_, sent_packets)
        } else if nextActionIndex == 3 {
            &&& SpontaneousIos(ios, 1)
            &&& LReplicaNextReadClockMaybeNominateValueAndSend2a(s, s_, SpontaneousClock(ios), sent_packets)
        } else if nextActionIndex == 4 {
            &&& SpontaneousIos(ios, 0)
            &&& LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s, s_, sent_packets)
        } else if nextActionIndex == 5 {
            &&& SpontaneousIos(ios, 0)
            &&& LReplicaNextSpontaneousMaybeMakeDecision(s, s_, sent_packets)
        } else if nextActionIndex == 6 {
            &&& SpontaneousIos(ios, 0)
            &&& LReplicaNextSpontaneousMaybeExecute(s, s_, sent_packets)
        } else if nextActionIndex == 7 {
            &&& SpontaneousIos(ios, 1)
            &&& LReplicaNextReadClockCheckForViewTimeout(s, s_, SpontaneousClock(ios), sent_packets)
        } else if nextActionIndex == 8 {
            &&& SpontaneousIos(ios, 1)
            &&& LReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, s_, SpontaneousClock(ios), sent_packets)
        } else {
            &&& nextActionIndex == 9
            &&& SpontaneousIos(ios, 1)
            &&& LReplicaNextReadClockMaybeSendHeartbeat(s, s_, SpontaneousClock(ios), sent_packets)
        }
    }

    pub struct LScheduler {
        pub replica:LReplica,
        pub nextActionIndex:int,
    }

    pub open spec fn LSchedulerInit(s:LScheduler, c:LReplicaConstants) -> bool
        recommends WellFormedLConfiguration(c.all.config)
    {
        &&& LReplicaInit(s.replica, c)
        &&& s.nextActionIndex == 0
    }

    pub open spec fn LSchedulerNext(s:LScheduler, s_:LScheduler, ios:Seq<RslIo>) -> bool
    {
        &&& s_.nextActionIndex == (s.nextActionIndex + 1) % LReplicaNumActions()
        &&& if s.nextActionIndex == 0 {
            LReplicaNextProcessPacket(s.replica, s_.replica, ios)
        } else {
            LReplicaNoReceiveNext(s.replica, s.nextActionIndex, s_.replica, ios)
        }
    }

    /*
    s_ == LReplica {
        constants:s.constants,
        nextHeartbeatTime:s.nextHeartbeatTime,
        proposer:s.proposer,
        acceptor:s.acceptor,
        learner:s.learner,
        executor:s.executor
    }
    */


}
