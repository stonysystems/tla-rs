use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::election::*;
use crate::protocol::RSL::acceptor::*;
use crate::protocol::RSL::proposer::*;
use crate::protocol::RSL::learner::*;
use crate::protocol::RSL::executor::*;
use crate::protocol::RSL::replica::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::common_proof::assumptions::*;
use crate::protocol::RSL::common_proof::constants::*;
use crate::protocol::RSL::common_proof::actions::*;
use crate::protocol::RSL::common_proof::environment::*;
use crate::protocol::RSL::common_proof::requests::*;
use crate::protocol::RSL::common_proof::message1b::*;
use crate::protocol::RSL::common_proof::message2a::*;
use crate::protocol::RSL::common_proof::message2b::*;
use crate::protocol::RSL::common_proof::receive1b::*;
use crate::protocol::RSL::common_proof::packet_sending::*;
use crate::protocol::RSL::common_proof::chosen::*;

use crate::protocol::RSL::refinement_proof::chosen::*;

use crate::common::logic::temporal_s::*;
use crate::common::logic::heuristics_i::*;
use crate::common::framework::environment_s::*;
use crate::common::framework::environment_s::LEnvStep;
use crate::common::native::io_s::*;
use crate::common::collections::maps2::*;

verus!{
    #[verifier::external_body]
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
            let p = ios[0]->r;
            assert(IsValidLIoOp(ios[0], c.config.replica_ids[idx], b[i-1].environment));
            assume(b[i].environment.sentPackets.contains(p));
            return p;
        }
        
        assert(nextActionIndex == 6);
        let batch = b[i-1].replicas[idx].replica.executor.next_op_to_execute->v;
        assert(ElectionStateReflectExecutedRequestBatch(es, es_, batch));
        lemma_RemoveExecutedRequestBatchProducesSubsequence(es_.requests_received_this_epoch, es.requests_received_this_epoch, batch);
        assert(false);
        arbitrary()
    }

    #[verifier::external_body]
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

    #[verifier::external_body]
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
      
        let s = b[i-1].replicas[idx].replica.proposer;
        let s = b[i].replicas[idx].replica.proposer;
      
        if s.request_queue.contains(req)
        {
          let p = lemma_RequestInRequestQueueHasCorrespondingRequestMessage(b, c, i-1, idx, req);
          lemma_PacketStaysInSentPackets(b, c, i-1, i, p);
          return p;
        }
        if s.election_state.requests_received_prev_epochs.contains(req)
        {
          let p = lemma_RequestInRequestsReceivedPrevEpochsHasCorrespondingRequestMessage(b, c, i-1, idx, req);
          lemma_PacketStaysInSentPackets(b, c, i-1, i, p);
          return p;
        }
        if s.election_state.requests_received_this_epoch.contains(req)
        {
          let p = lemma_RequestInRequestsReceivedThisEpochHasCorrespondingRequestMessage(b, c, i-1, idx, req);
          lemma_PacketStaysInSentPackets(b, c, i-1, i, p);
          return p;
        }
      
        let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
        let p = ios[0]->r;
        assert(IsValidLIoOp(ios[0], c.config.replica_ids[idx], b[i-1].environment));
        p
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

    #[verifier::external_body]
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

    #[verifier::external_body]
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