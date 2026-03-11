use crate::common::framework::environment_s::*;
use crate::protocol::RSL::acceptor::*;
use crate::protocol::RSL::common_proof::actions::*;
use crate::protocol::RSL::common_proof::assumptions::*;
use crate::protocol::RSL::common_proof::chosen::*;
use crate::protocol::RSL::common_proof::constants::*;
use crate::protocol::RSL::common_proof::environment::*;
use crate::protocol::RSL::common_proof::message1b::*;
use crate::protocol::RSL::common_proof::message2a::*;
use crate::protocol::RSL::common_proof::message2b::*;
use crate::protocol::RSL::common_proof::packet_sending::*;
use crate::protocol::RSL::common_proof::receive1b::*;
use crate::protocol::RSL::common_proof::requests::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::election::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::executor::*;
use crate::protocol::RSL::learner::*;
use crate::protocol::RSL::proposer::*;
use crate::protocol::RSL::replica::*;
use crate::protocol::RSL::types::*;
use crate::protocol::common::upper_bound::*;
use vstd::prelude::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

use crate::protocol::RSL::refinement_proof::chosen::*;

use crate::common::collections::maps2::*;
use crate::common::framework::environment_s::LEnvStep;
use crate::common::framework::environment_s::*;
use crate::common::logic::heuristics_i::*;
use crate::common::logic::temporal_s::*;
use crate::common::native::io_s::*;

verus! {
    pub proof fn lemma_RequestInSubrangeImpliesRequestInOriginal(
        s: Seq<Request>,
        start: int,
        end: int,
        req: Request,
    )
        requires
            0 <= start <= end <= s.len(),
            s.subrange(start, end).contains(req),
        ensures
            s.contains(req),
    {
        let idx = choose |idx: int| 0 <= idx < s.subrange(start, end).len() && s.subrange(start, end)[idx] == req;
        assert(0 <= start + idx < end);
        assert(s[start + idx] == req);
        assert(s.contains(req));
    }

    pub proof fn lemma_RequestInQueueAppendComesFromAppendedElement(
        s: Seq<Request>,
        req: Request,
        val: Request,
    )
        requires
            !s.contains(req),
            (s + seq![val]).contains(req),
        ensures
            req == val,
    {
        SeqConcatenate(s, seq![val]);
        assert(seq![val].contains(req));
        let idx = choose |idx: int| 0 <= idx < seq![val].len() && seq![val][idx] == req;
        assert(idx == 0);
        assert(req == val);
    }

    pub proof fn lemma_RequestInQueueAfterMaybeNominateValueComesFromPreviousQueue(
        s: LProposer,
        s_: LProposer,
        clock: int,
        log_truncation_point: int,
        sent_packets: Seq<RslPacket>,
        req: Request,
    )
        requires
            LProposerMaybeNominateValueAndSend2a(s, s_, clock, log_truncation_point, sent_packets),
            s_.request_queue.contains(req),
        ensures
            s.request_queue.contains(req),
    {
        if !LProposerCanNominateUsingOperationNumber(s, log_truncation_point, s.next_operation_number_to_propose) {
            assert(s_ == s);
        } else if !LAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose) {
            assert(LProposerNominateOldValueAndSend2a(s, s_, log_truncation_point, sent_packets));
            assert(s_.request_queue == s.request_queue);
        } else if LExistsAcceptorHasProposalLargeThanOpn(s.received_1b_packets, s.next_operation_number_to_propose)
            || s.request_queue.len() >= s.constants.all.params.max_batch_size
            || (s.request_queue.len() > 0
                && s.incomplete_batch_timer is IncompleteBatchTimerOn
                && clock >= s.incomplete_batch_timer->when)
        {
            assert(LProposerNominateNewValueAndSend2a(s, s_, clock, log_truncation_point, sent_packets));
            let batch_size = if s.request_queue.len() <= s.constants.all.params.max_batch_size || s.constants.all.params.max_batch_size < 0 {
                s.request_queue.len() as int
            } else {
                s.constants.all.params.max_batch_size
            };
            assert(s_.request_queue == s.request_queue.subrange(batch_size, s.request_queue.len() as int));
            lemma_RequestInSubrangeImpliesRequestInOriginal(
                s.request_queue,
                batch_size,
                s.request_queue.len() as int,
                req,
            );
        } else if s.request_queue.len() > 0 && s.incomplete_batch_timer is IncompleteBatchTimerOff {
            assert(s_.request_queue == s.request_queue);
        } else {
            assert(s_ == s);
        }
    }

    pub proof fn lemma_RequestInRequestsReceivedThisEpochHasCorrespondingRequestMessage(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        idx:int,
        req:Request
    ) -> (p:RslPacket)
        requires IsValidBehaviorPrefix(b, c, i),
                 0 <= i,
                 0 <= idx < b[i].replicas.len(),
                 b[i].replicas[idx].replica.proposer.election_state.requests_received_this_epoch.contains(req)
        ensures b[i].environment.sentPackets.contains(p),
                c.config.replica_ids.contains(p.dst),
                p.msg is RslMessageRequest,
                req.client == p.src,
                req.seqno == p.msg->seqno_req,
                req.request == p.msg->val,
        decreases i
    {
        if i == 0 { return arbitrary(); }

        lemma_ConstantsAllConsistent(b, c, i-1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_AssumptionsMakeValidTransition(b, c, i-1);

        let es = b[i-1].replicas[idx].replica.proposer.election_state;
        let es_ = b[i].replicas[idx].replica.proposer.election_state;

        if es.requests_received_this_epoch.contains(req)
        {
            let p = lemma_RequestInRequestsReceivedThisEpochHasCorrespondingRequestMessage(b, c, i-1, idx, req);
            lemma_PacketStaysInSentPackets(b, c, i-1, i, p);
            return p;
        }

        let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
        let nextActionIndex = b[i-1].replicas[idx].nextActionIndex;

        if nextActionIndex == 0
        {
            let e = b[i-1].environment;
            assert(LEnvironment_Next(e, b[i].environment));
            assert(e.nextStep is LEnvStepHostIos);
            assert(IsValidLEnvStep(e, e.nextStep));
            let actor = e.nextStep->actor;
            assert(actor == c.config.replica_ids[idx]);
            assert(forall |io| e.nextStep->ios.contains(io) ==> IsValidLIoOp(io, actor, e));
            assert(LEnvironment_PerformIos(e, b[i].environment, actor, ios));

            let p = ios[0]->r;
            assert(ios[0] is Receive);
            assert(ios.contains(ios[0]));
            assert(IsValidLIoOp(ios[0], actor, e));
            // IsValidLIoOp for Receive: r.dst == actor
            assert(p.dst == actor);
            assert(p.dst == c.config.replica_ids[idx]);

            // p was in sentPackets at i-1 (match_ios_recv)
            assert(forall |io| ios.contains(io) ==> match_ios_recv(io, e.sentPackets));
            assert(match_ios_recv(ios[0], e.sentPackets));
            assert(e.sentPackets.contains(p));
            lemma_PacketStaysInSentPackets(b, c, i-1, i, p);

            assert(c.config.replica_ids.contains(p.dst));
            return p;
        }

        assert(nextActionIndex == 6);
        let batch = b[i-1].replicas[idx].replica.executor.next_op_to_execute->v;
        assert(ElectionStateReflectExecutedRequestBatch(es, es_, batch));
        lemma_RemoveExecutedRequestBatchProducesSubsequence(es_.requests_received_this_epoch, es.requests_received_this_epoch, batch);
        assert(false);
        arbitrary()
    }

    pub proof fn lemma_RequestInRequestsReceivedPrevEpochsHasCorrespondingRequestMessage(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        idx:int,
        req:Request
    ) -> (
        p:RslPacket
    )
        requires IsValidBehaviorPrefix(b, c, i),
                 0 <= i,
                 0 <= idx < b[i].replicas.len(),
                 b[i].replicas[idx].replica.proposer.election_state.requests_received_prev_epochs.contains(req)
        ensures b[i].environment.sentPackets.contains(p),
                c.config.replica_ids.contains(p.dst),
                p.msg is RslMessageRequest,
                req.client == p.src,
                req.seqno == p.msg->seqno_req,
                req.request == p.msg->val,
        decreases i
    {
        if i == 0 { return arbitrary(); }

        lemma_ConstantsAllConsistent(b, c, i-1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_AssumptionsMakeValidTransition(b, c, i-1);

        let es = b[i-1].replicas[idx].replica.proposer.election_state;
        let es_ = b[i].replicas[idx].replica.proposer.election_state;

        if es.requests_received_prev_epochs.contains(req)
        {
          let p = lemma_RequestInRequestsReceivedPrevEpochsHasCorrespondingRequestMessage(b, c, i-1, idx, req);
          lemma_PacketStaysInSentPackets(b, c, i-1, i, p);
          return p;
        }
        if es.requests_received_this_epoch.contains(req)
        {
          let p = lemma_RequestInRequestsReceivedThisEpochHasCorrespondingRequestMessage(b, c, i-1, idx, req);
          lemma_PacketStaysInSentPackets(b, c, i-1, i, p);
          return p;
        }

        let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
        let nextActionIndex = b[i-1].replicas[idx].nextActionIndex;
        assert(nextActionIndex == 6);
        let batch = b[i-1].replicas[idx].replica.executor.next_op_to_execute->v;
        assert(ElectionStateReflectExecutedRequestBatch(es, es_, batch));
        lemma_RemoveExecutedRequestBatchProducesSubsequence(es_.requests_received_prev_epochs, es.requests_received_prev_epochs, batch);
        assert(false);
        arbitrary()
    }

    pub proof fn lemma_RequestInRequestQueueHasCorrespondingRequestMessage(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        idx:int,
        req:Request
    ) -> (
        p:RslPacket
    )
        requires IsValidBehaviorPrefix(b, c, i),
                 0 <= i,
                 0 <= idx < b[i].replicas.len(),
                 b[i].replicas[idx].replica.proposer.request_queue.contains(req),
        ensures b[i].environment.sentPackets.contains(p),
                c.config.replica_ids.contains(p.dst),
                p.msg is RslMessageRequest,
                req.client == p.src,
                req.seqno == p.msg->seqno_req,
                req.request == p.msg->val,
        decreases i
    {
        if i == 0 { return arbitrary(); }

        lemma_ConstantsAllConsistent(b, c, i-1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_AssumptionsMakeValidTransition(b, c, i-1);

        let sched_prev = b[i - 1].replicas[idx];
        let sched_cur = b[i].replicas[idx];
        let s_prev = b[i-1].replicas[idx].replica.proposer;
        let s_cur = b[i].replicas[idx].replica.proposer;
        let nextActionIndex = b[i-1].replicas[idx].nextActionIndex;

        if s_prev.request_queue.contains(req)
        {
          let p = lemma_RequestInRequestQueueHasCorrespondingRequestMessage(b, c, i-1, idx, req);
          lemma_PacketStaysInSentPackets(b, c, i-1, i, p);
          return p;
        }
        if s_cur.election_state.requests_received_prev_epochs.contains(req)
        {
          let p = lemma_RequestInRequestsReceivedPrevEpochsHasCorrespondingRequestMessage(b, c, i, idx, req);
          return p;
        }
        if s_cur.election_state.requests_received_this_epoch.contains(req)
        {
          let p = lemma_RequestInRequestsReceivedThisEpochHasCorrespondingRequestMessage(b, c, i, idx, req);
          return p;
        }

        let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
        assert(RslNextOneReplica(b[i - 1], b[i], idx, ios));
        assert(LSchedulerNext(sched_prev, sched_cur, ios));

        if nextActionIndex == 1
        {
            // Isolate the "enter new view" queue-reset branch: any newly introduced queue
            // request must come from election-state request sets.
            assert(LReplicaNoReceiveNext(sched_prev.replica, nextActionIndex, sched_cur.replica, ios));
            let sent_packets = ExtractSentPacketsFromIos(ios);
            assert(LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(
                sched_prev.replica,
                sched_cur.replica,
                sent_packets,
            ));
            assert(LProposerMaybeEnterNewViewAndSend1a(s_prev, s_cur, sent_packets));
            lemma_RequestInQueueAfterMaybeEnterNewViewComesFromElectionState(s_prev, s_cur, sent_packets, req);
            assert(false);
            return arbitrary();
        }

        if nextActionIndex != 0
        {
            assert(LReplicaNoReceiveNext(sched_prev.replica, nextActionIndex, sched_cur.replica, ios));

            if nextActionIndex == 3 {
                let sent_packets = ExtractSentPacketsFromIos(ios);
                assert(LReplicaNextReadClockMaybeNominateValueAndSend2a(
                    sched_prev.replica,
                    sched_cur.replica,
                    SpontaneousClock(ios),
                    sent_packets,
                ));
                assert(LProposerMaybeNominateValueAndSend2a(
                    s_prev,
                    s_cur,
                    SpontaneousClock(ios).t,
                    sched_prev.replica.acceptor.log_truncation_point,
                    sent_packets,
                ));
                lemma_RequestInQueueAfterMaybeNominateValueComesFromPreviousQueue(
                    s_prev,
                    s_cur,
                    SpontaneousClock(ios).t,
                    sched_prev.replica.acceptor.log_truncation_point,
                    sent_packets,
                    req,
                );
                assert(s_prev.request_queue.contains(req));
                assert(false);
            }

            if nextActionIndex == 8 {
                assert(LReplicaNextReadClockCheckForQuorumOfViewSuspicions(
                    sched_prev.replica,
                    sched_cur.replica,
                    SpontaneousClock(ios),
                    ExtractSentPacketsFromIos(ios),
                ));
                assert(LProposerCheckForQuorumOfViewSuspicions(s_prev, s_cur, SpontaneousClock(ios).t));
                if BalLt(s_prev.election_state.current_view, s_cur.election_state.current_view) {
                    assert(s_cur.request_queue == Seq::<Request>::empty());
                    assert(false);
                } else {
                    assert(s_cur.request_queue == s_prev.request_queue);
                    assert(s_prev.request_queue.contains(req));
                    assert(false);
                }
            }

            if nextActionIndex == 2 {
                assert(LReplicaNextSpontaneousMaybeEnterPhase2(
                    sched_prev.replica,
                    sched_cur.replica,
                    ExtractSentPacketsFromIos(ios),
                ));
                assert(s_cur.request_queue == s_prev.request_queue);
                assert(s_prev.request_queue.contains(req));
                assert(false);
            } else if nextActionIndex == 4 {
                assert(LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(
                    sched_prev.replica,
                    sched_cur.replica,
                    ExtractSentPacketsFromIos(ios),
                ));
                assert(s_cur.request_queue == s_prev.request_queue);
                assert(s_prev.request_queue.contains(req));
                assert(false);
            } else if nextActionIndex == 5 {
                assert(LReplicaNextSpontaneousMaybeMakeDecision(
                    sched_prev.replica,
                    sched_cur.replica,
                    ExtractSentPacketsFromIos(ios),
                ));
                assert(s_cur.request_queue == s_prev.request_queue);
                assert(s_prev.request_queue.contains(req));
                assert(false);
            } else if nextActionIndex == 6 {
                assert(LReplicaNextSpontaneousMaybeExecute(
                    sched_prev.replica,
                    sched_cur.replica,
                    ExtractSentPacketsFromIos(ios),
                ));
                assert(s_cur.request_queue == s_prev.request_queue);
                assert(s_prev.request_queue.contains(req));
                assert(false);
            } else if nextActionIndex == 7 {
                assert(LReplicaNextReadClockCheckForViewTimeout(
                    sched_prev.replica,
                    sched_cur.replica,
                    SpontaneousClock(ios),
                    ExtractSentPacketsFromIos(ios),
                ));
                assert(s_cur.request_queue == s_prev.request_queue);
                assert(s_prev.request_queue.contains(req));
                assert(false);
            } else {
                assert(nextActionIndex == 9);
                assert(LReplicaNextReadClockMaybeSendHeartbeat(
                    sched_prev.replica,
                    sched_cur.replica,
                    SpontaneousClock(ios),
                    ExtractSentPacketsFromIos(ios),
                ));
                assert(s_cur.request_queue == s_prev.request_queue);
                assert(s_prev.request_queue.contains(req));
                assert(false);
            }

            assert(false);
            return arbitrary();
        }

        assert(nextActionIndex == 0);
        assert(LReplicaNextProcessPacket(sched_prev.replica, sched_cur.replica, ios));

        if ios[0] is TimeoutReceive {
            assert(s_cur.request_queue == s_prev.request_queue);
            assert(false);
        }
        assert(ios[0] is Receive);
        let p = ios[0]->r;

        if p.msg is RslMessageHeartbeat {
            assert(LReplicaNextReadClockAndProcessPacket(sched_prev.replica, sched_cur.replica, ios));
            assert(LReplicaNextProcessHeartbeat(
                sched_prev.replica,
                sched_cur.replica,
                p,
                ios[1]->t,
                ExtractSentPacketsFromIos(ios),
            ));
            if BalLt(s_prev.election_state.current_view, s_cur.election_state.current_view) {
                assert(s_cur.request_queue == Seq::<Request>::empty());
                assert(false);
            } else {
                assert(s_cur.request_queue == s_prev.request_queue);
                assert(s_prev.request_queue.contains(req));
                assert(false);
            }
        }

        assert(LReplicaNextProcessPacketWithoutReadingClock(sched_prev.replica, sched_cur.replica, ios));

        if p.msg is RslMessageRequest {
            assert(LReplicaNextProcessRequest(
                sched_prev.replica,
                sched_cur.replica,
                p,
                ExtractSentPacketsFromIos(ios),
            ));
            if sched_prev.replica.executor.reply_cache.contains_key(p.src)
                && p.msg->seqno_req <= sched_prev.replica.executor.reply_cache[p.src].seqno
            {
                assert(sched_cur.replica == sched_prev.replica);
                assert(false);
            }
            assert(LProposerProcessRequest(s_prev, s_cur, p));
            let req_from_packet = Request{client:p.src, seqno:p.msg->seqno_req, request:p.msg->val};
            if !(s_prev.current_state != 0
                && (!s_prev.highest_seqno_requested_by_client_this_view.contains_key(req_from_packet.client)
                    || req_from_packet.seqno > s_prev.highest_seqno_requested_by_client_this_view[req_from_packet.client]))
            {
                assert(s_cur.request_queue == s_prev.request_queue);
                assert(false);
            }
            assert(s_cur.request_queue == s_prev.request_queue + seq![req_from_packet]);
            lemma_RequestInQueueAppendComesFromAppendedElement(s_prev.request_queue, req, req_from_packet);
            lemma_PacketProcessedImpliesPacketSent(b[i - 1], b[i], idx, ios, p);
            lemma_PacketStaysInSentPackets(b, c, i - 1, i, p);
            let e = b[i - 1].environment;
            assert(LEnvironment_Next(e, b[i].environment));
            assert(e.nextStep is LEnvStepHostIos);
            assert(IsValidLEnvStep(e, e.nextStep));
            assert(forall |io| e.nextStep->ios.contains(io) ==> IsValidLIoOp(io, e.nextStep->actor, e));
            assert(IsValidLIoOp(ios[0], e.nextStep->actor, e));
            assert(e.nextStep->actor == c.config.replica_ids[idx]);
            assert(0 <= idx < c.config.replica_ids.len());
            assert(p.dst == e.nextStep->actor);
            assert(c.config.replica_ids.contains(p.dst));
            return p;
        }

        if p.msg is RslMessageInvalid {
            assert(LReplicaNextProcessInvalid(sched_prev.replica, sched_cur.replica, p, ExtractSentPacketsFromIos(ios)));
            assert(s_cur.request_queue == s_prev.request_queue);
            assert(false);
        } else if p.msg is RslMessage1a {
            assert(LReplicaNextProcess1a(sched_prev.replica, sched_cur.replica, p, ExtractSentPacketsFromIos(ios)));
            assert(s_cur.request_queue == s_prev.request_queue);
            assert(false);
        } else if p.msg is RslMessage1b {
            assert(LReplicaNextProcess1b(sched_prev.replica, sched_cur.replica, p, ExtractSentPacketsFromIos(ios)));
            if sched_prev.replica.constants.all.config.replica_ids.contains(p.src)
                && p.msg->bal_1b == sched_prev.replica.proposer.max_ballot_i_sent_1a
                && sched_prev.replica.proposer.current_state == 1
                && (forall |other_packet:RslPacket| sched_prev.replica.proposer.received_1b_packets.contains(other_packet) ==> other_packet.src != p.src)
            {
                assert(s_cur.request_queue == s_prev.request_queue);
            } else {
                assert(s_cur == s_prev);
            }
            assert(false);
        } else if p.msg is RslMessageStartingPhase2 {
            assert(LReplicaNextProcessStartingPhase2(sched_prev.replica, sched_cur.replica, p, ExtractSentPacketsFromIos(ios)));
            assert(s_cur.request_queue == s_prev.request_queue);
            assert(false);
        } else if p.msg is RslMessage2a {
            assert(LReplicaNextProcess2a(sched_prev.replica, sched_cur.replica, p, ExtractSentPacketsFromIos(ios)));
            if sched_prev.replica.acceptor.constants.all.config.replica_ids.contains(p.src)
                && BalLeq(sched_prev.replica.acceptor.max_bal, p.msg->bal_2a)
                && LeqUpperBound(p.msg->opn_2a, sched_prev.replica.acceptor.constants.all.params.max_integer_val)
            {
                assert(s_cur.request_queue == s_prev.request_queue);
            } else {
                assert(s_cur == s_prev);
            }
            assert(false);
        } else if p.msg is RslMessage2b {
            assert(LReplicaNextProcess2b(sched_prev.replica, sched_cur.replica, p, ExtractSentPacketsFromIos(ios)));
            let op_learnable = sched_prev.replica.executor.ops_complete < p.msg->opn_2b
                || (sched_prev.replica.executor.ops_complete == p.msg->opn_2b
                    && sched_prev.replica.executor.next_op_to_execute is OutstandingOpUnknown);
            if op_learnable {
                assert(s_cur.request_queue == s_prev.request_queue);
            } else {
                assert(s_cur == s_prev);
            }
            assert(false);
        } else if p.msg is RslMessageReply {
            assert(LReplicaNextProcessReply(sched_prev.replica, sched_cur.replica, p, ExtractSentPacketsFromIos(ios)));
            assert(s_cur == s_prev);
            assert(false);
        } else if p.msg is RslMessageAppStateRequest {
            assert(LReplicaNextProcessAppStateRequest(sched_prev.replica, sched_cur.replica, p, ExtractSentPacketsFromIos(ios)));
            assert(s_cur.request_queue == s_prev.request_queue);
            assert(false);
        } else {
            assert(p.msg is RslMessageAppStateSupply);
            assert(LReplicaNextProcessAppStateSupply(sched_prev.replica, sched_cur.replica, p, ExtractSentPacketsFromIos(ios)));
            if sched_prev.replica.executor.constants.all.config.replica_ids.contains(p.src)
                && p.msg->opn_state_supply > sched_prev.replica.executor.ops_complete
            {
                assert(s_cur.request_queue == s_prev.request_queue);
            } else {
                assert(s_cur == s_prev);
            }
            assert(false);
        }

        assert(false);
        arbitrary()
    }

    pub proof fn lemma_RequestInQueueAfterMaybeEnterNewViewComesFromElectionState(
        s:LProposer,
        s_:LProposer,
        sent_packets:Seq<RslPacket>,
        req:Request
    )
        requires LProposerMaybeEnterNewViewAndSend1a(s, s_, sent_packets),
                 s_.request_queue.contains(req),
                 !s.request_queue.contains(req),
        ensures s_.election_state.requests_received_prev_epochs.contains(req)
                || s_.election_state.requests_received_this_epoch.contains(req),
    {
        if s.election_state.current_view.proposer_id == s.constants.my_index
            && BalLt(s.max_ballot_i_sent_1a, s.election_state.current_view)
        {
            SeqConcatenate(
                s.election_state.requests_received_prev_epochs,
                s.election_state.requests_received_this_epoch,
            );
            assert(
                (s.election_state.requests_received_prev_epochs + s.election_state.requests_received_this_epoch).contains(req)
            );
            assert(
                s.election_state.requests_received_prev_epochs.contains(req)
                || s.election_state.requests_received_this_epoch.contains(req)
            );
        } else {
            assert(s_ == s);
            assert(false);
        }
    }

    pub proof fn lemma_RequestIn1bMessageHasCorrespondingRequestMessage(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        p_1b:RslPacket,
        opn:OperationNumber,
        req_num:int
    ) -> (
        p_req:RslPacket
    )
        requires IsValidBehaviorPrefix(b, c, i),
                 0 <= i,
                 b[i].environment.sentPackets.contains(p_1b),
                 c.config.replica_ids.contains(p_1b.src),
                 p_1b.msg is RslMessage1b,
                 p_1b.msg->votes.contains_key(opn),
                 0 <= req_num < p_1b.msg->votes[opn].max_val.len(),
        ensures b[i].environment.sentPackets.contains(p_req),
                c.config.replica_ids.contains(p_req.dst),
                p_req.msg is RslMessageRequest,
                p_1b.msg->votes[opn].max_val[req_num].client == p_req.src,
                p_1b.msg->votes[opn].max_val[req_num].seqno == p_req.msg->seqno_req,
                p_1b.msg->votes[opn].max_val[req_num].request == p_req.msg->val,
                // p_1b.msg.votes[opn].max_val[req_num] == Request(p_req.src, p_req.msg.seqno_req, p_req.msg.val)
        decreases i, 1 as nat
    {
        let p_2a = lemma_1bMessageWithOpnImplies2aSent(b, c, i, opn, p_1b);
        let p_req = lemma_RequestIn2aMessageHasCorrespondingRequestMessage(b, c, i, p_2a, req_num);
        p_req
    }

    #[verifier(external_body)]
    pub proof fn lemma_RequestIn2aMessageHasCorrespondingRequestMessage(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        p_2a:RslPacket,
        req_num:int
    ) -> (
        p_req:RslPacket
    )
        requires IsValidBehaviorPrefix(b, c, i),
                0 <= i,
                b[i].environment.sentPackets.contains(p_2a),
                c.config.replica_ids.contains(p_2a.src),
                p_2a.msg is RslMessage2a,
                0 <= req_num < p_2a.msg->val_2a.len(),
        ensures b[i].environment.sentPackets.contains(p_req),
                c.config.replica_ids.contains(p_req.dst),
                p_req.msg is RslMessageRequest,
                // p_2a.msg->val_2a[req_num] == Request{client:p_req.src, seqno:p_req.msg.seqno_req, request:p_req.msg.val},
                p_2a.msg->val_2a[req_num].client == p_req.src,
                p_2a.msg->val_2a[req_num].seqno == p_req.msg->seqno_req,
                p_2a.msg->val_2a[req_num].request == p_req.msg->val,
        decreases i, 0 as nat
    {
        if i == 0
        {
          return arbitrary();
        }

        if b[i-1].environment.sentPackets.contains(p_2a)
        {
          let p_req = lemma_RequestIn2aMessageHasCorrespondingRequestMessage(b, c, i-1, p_2a, req_num);
          lemma_PacketStaysInSentPackets(b, c, i-1, i, p_req);
          return p_req;
        }

        lemma_ConstantsAllConsistent(b, c, i-1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_AssumptionsMakeValidTransition(b, c, i-1);
        let (idx, ios) = lemma_ActionThatSends2aIsMaybeNominateValueAndSend2a(b[i-1], b[i], p_2a);

        let s = b[i-1].replicas[idx].replica.proposer;
        let s_ = b[i].replicas[idx].replica.proposer;
        let log_truncation_point = b[i-1].replicas[idx].replica.acceptor.log_truncation_point;
        let sent_packets = ExtractSentPacketsFromIos(ios);

        if LAllAcceptorsHadNoProposal(s.received_1b_packets, s.next_operation_number_to_propose)
        {
          assert(LProposerNominateNewValueAndSend2a(s, s_, ios[0]->t, log_truncation_point, sent_packets));
          assert(s.request_queue[req_num] == p_2a.msg->val_2a[req_num]);
          let p_req = lemma_RequestInRequestQueueHasCorrespondingRequestMessage(b, c, i-1, idx, s.request_queue[req_num]);
          p_req
        }
        else
        {
          assert(LProposerNominateOldValueAndSend2a(s, s_, log_truncation_point, sent_packets));
          let opn = s.next_operation_number_to_propose;
          let v = p_2a.msg->val_2a;
          // var earlier_ballot :| LValIsHighestNumberedProposalAtBallot(v, earlier_ballot, s.received_1b_packets, opn);
          let p_1b = choose |p_1b:RslPacket| s.received_1b_packets.contains(p_1b) && p_1b.msg->votes.contains_key(opn) && p_1b.msg->votes[opn].max_val == v;
          lemma_PacketInReceived1bWasSent(b, c, i-1, idx, p_1b);
          let p_req = lemma_RequestIn1bMessageHasCorrespondingRequestMessage(b, c, i-1, p_1b, opn, req_num);
          p_req
        }
    }

    #[verifier(external_body)]
    pub proof fn lemma_DecidedRequestWasSentByClient(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        qs:Seq<QuorumOf2bs>,
        batches:Seq<RequestBatch>,
        batch_num:int,
        req_num:int
    ) -> (
        p:RslPacket
    )
        requires IsValidBehaviorPrefix(b, c, i),
                0 <= i,
                IsValidQuorumOf2bsSequence(b[i], qs),
                batches == GetSequenceOfRequestBatches(qs),
                0 <= batch_num < batches.len(),
                0 <= req_num < batches[batch_num].len(),
        ensures b[i].environment.sentPackets.contains(p),
                c.config.replica_ids.contains(p.dst),
                p.msg is RslMessageRequest,
                batches[batch_num][req_num].client == p.src,
                batches[batch_num][req_num].seqno == p.msg->seqno_req,
                batches[batch_num][req_num].request == p.msg->val,
        decreases i
    {
        lemma_ConstantsAllConsistent(b, c, i);

        lemma_GetSequenceOfRequestBatches(qs);
        lemma_SequenceOfRequestBatchesNthElement(qs, batch_num);
        let batch = batches[batch_num];
        let request = batch[req_num];
        let q = qs[batch_num];
        let idx = choose |idx:int| q.indices.contains(idx);
        let packet_2b = q.packets[idx];
        assert(packet_2b.msg is RslMessage2b);
        assert(packet_2b.msg->val_2b == batch);

        let packet_2a = lemma_2bMessageHasCorresponding2aMessage(b, c, i, packet_2b);

        let p = lemma_RequestIn2aMessageHasCorrespondingRequestMessage(b, c, i, packet_2a, req_num);
        p
    }
}
