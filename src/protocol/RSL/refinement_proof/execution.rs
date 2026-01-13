use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::election::*;
use crate::protocol::RSL::acceptor::*;
use crate::protocol::RSL::proposer::*;
use crate::protocol::RSL::learner::*;
use crate::protocol::RSL::executor::*;
use crate::protocol::RSL::replica::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::state_machine::*;
use crate::protocol::RSL::message::*;
use crate::protocol::common::upper_bound::*;
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
use crate::protocol::RSL::refinement_proof::state_machine::*;
use crate::protocol::RSL::refinement_proof::handle_request_batch::*;

use crate::common::logic::temporal_s::*;
use crate::common::logic::heuristics_i::*;
use crate::common::framework::environment_s::*;
use crate::common::framework::environment_s::LEnvStep;
use crate::common::native::io_s::*;
use crate::common::collections::maps2::*;
use crate::common::collections::sets::*;

verus!{
    #[verifier::external_body]
    pub proof fn lemma_AppStateAlwaysValid(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        idx: int
    ) -> (qs: Seq<QuorumOf2bs>)
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            0 <= idx < b[i].replicas.len(),
        ensures
            IsValidQuorumOf2bsSequence(b[i], qs),
            qs.len() == b[i].replicas[idx].replica.executor.ops_complete,
            b[i].replicas[idx].replica.executor.app == GetAppStateFromRequestBatches(GetSequenceOfRequestBatches(qs)),
        decreases i,
    {
        if i == 0 {
            return arbitrary();
        }
    
        lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
        lemma_ReplicaConstantsAllConsistent(b, c, i - 1, idx);
        lemma_AssumptionsMakeValidTransition(b, c, i - 1);
    
        let s = b[i - 1].replicas[idx].replica.executor;
        let s_prime = b[i].replicas[idx].replica.executor;
    
        if s_prime.ops_complete == s.ops_complete {
            let qs_prev = lemma_AppStateAlwaysValid(b, c, i - 1, idx);
            lemma_IfValidQuorumOf2bsSequenceNowThenNext(b, c, i - 1, qs_prev);
            return qs_prev;
        }
    
        let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i - 1, idx);
        if b[i - 1].replicas[idx].nextActionIndex == 0 {
            let p = ios[0]->r;
            return lemma_TransferredStateAlwaysValid(b, c, i - 1, p);
        }
    
        let prev_qs = lemma_AppStateAlwaysValid(b, c, i - 1, idx);
        let q = lemma_DecidedOperationWasChosen(b, c, i - 1, idx);
        let new_qs = prev_qs + seq![q];
        assert(GetSequenceOfRequestBatches(new_qs) == GetSequenceOfRequestBatches(prev_qs).push(q.v));
        return new_qs;
    }

    #[verifier::external_body]
    pub proof fn lemma_TransferredStateAlwaysValid(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        p: RslPacket
    ) -> (qs: Seq<QuorumOf2bs>)
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            b[i].environment.sentPackets.contains(p),
            c.config.replica_ids.contains(p.src),
            p.msg is RslMessageAppStateSupply,
        ensures
            IsValidQuorumOf2bsSequence(b[i], qs),
            qs.len() == p.msg->opn_state_supply,
            p.msg->app_state == GetAppStateFromRequestBatches(GetSequenceOfRequestBatches(qs)),
        decreases i,
    {
        if i == 0 {
            return Seq::empty();
        }
    
        lemma_ConstantsAllConsistent(b, c, i - 1);
        lemma_ConstantsAllConsistent(b, c, i);
    
        if b[i - 1].environment.sentPackets.contains(p) {
            let qs_prev = lemma_TransferredStateAlwaysValid(b, c, i - 1, p);
            lemma_IfValidQuorumOf2bsSequenceNowThenNext(b, c, i - 1, qs_prev);
            return qs_prev;
        }
    
        lemma_AssumptionsMakeValidTransition(b, c, i - 1);
        let (idx, ios) = lemma_ActionThatSendsAppStateSupplyIsProcessAppStateRequest(b[i - 1], b[i], p);
        return lemma_AppStateAlwaysValid(b, c, i - 1, idx);
    }
    
    #[verifier::external_body]
    pub proof fn lemma_ReplySentIsAllowed(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        p: RslPacket
    ) -> (r:(Seq<QuorumOf2bs>, Seq<RequestBatch>, int, int))
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            b[i].environment.sentPackets.contains(p),
            c.config.replica_ids.contains(p.src),
            p.msg is RslMessageReply,
        ensures
            IsValidQuorumOf2bsSequence(b[i], r.0),
            r.1 == GetSequenceOfRequestBatches(r.0),
            0 <= r.2 < r.1.len(),
            0 <= r.3 < r.1[r.2].len(),
            ({let reply = Reply{client:p.dst, seqno:p.msg->seqno_reply, reply:p.msg->reply};
                reply == GetReplyFromRequestBatches(r.1, r.2, r.3)}),
            // Reply(p.dst, p.msg.seqno_reply, p.msg.reply) == GetReplyFromRequestBatches(batches, batch_num, req_num),
        decreases i,
    {
        if i == 0 {
            return arbitrary();
        }
    
        lemma_ConstantsAllConsistent(b, c, i - 1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_AssumptionsMakeValidTransition(b, c, i - 1);
    
        if b[i - 1].environment.sentPackets.contains(p) {
            let (qs_prime, batches_prime, batch_num_prime, req_num_prime) = lemma_ReplySentIsAllowed(b, c, i - 1, p);
            lemma_IfValidQuorumOf2bsSequenceNowThenNext(b, c, i - 1, qs_prime);
            return (qs_prime, batches_prime, batch_num_prime, req_num_prime);
        }
    
        assert(b[i - 1].environment.nextStep is LEnvStepHostIos);
        assert(b[i - 1].environment.nextStep->ios.contains(LIoOp::Send{s:p}));
        let idx = GetReplicaIndex(b[i - 1].environment.nextStep->actor, c.config);
        let ios = b[i - 1].environment.nextStep->ios;
        let idx_alt = choose |idx_alt: int| RslNextOneReplica(b[i - 1], b[i], idx_alt, ios);
        assert(ReplicasDistinct(c.config.replica_ids, idx, idx_alt));
    
        let next_action_index = b[i - 1].replicas[idx].nextActionIndex;
        if next_action_index == 0 {
            let (qs_prime, batches_prime, batch_num_prime, req_num_prime) = lemma_ReplyInReplyCacheIsAllowed(b, c, i - 1, ios[0]->r.src, idx);
            lemma_IfValidQuorumOf2bsSequenceNowThenNext(b, c, i - 1, qs_prime);
            return (qs_prime, batches_prime, batch_num_prime, req_num_prime);
        } else if next_action_index == 6 {
            let (qs_prime, batches_prime, batch_num_prime, req_num_prime) = lemma_ReplySentViaExecutionIsAllowed(b, c, i - 1, p, idx, ios);
            lemma_IfValidQuorumOf2bsSequenceNowThenNext(b, c, i - 1, qs_prime);
            return (qs_prime, batches_prime, batch_num_prime, req_num_prime);
        } else {
            assert(false);
            return arbitrary();
        }
    }

    #[verifier::external_body]
    pub proof fn lemma_ReplyInReplyCacheIsAllowed(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        client: AbstractEndPoint,
        idx: int
    ) -> (rc:(Seq<QuorumOf2bs>, Seq<RequestBatch>, int, int))
        requires
            IsValidBehaviorPrefix(b, c, i + 1),
            0 <= i,
            0 <= idx < c.config.replica_ids.len(),
            0 <= idx < b[i].replicas.len(),
            b[i].replicas[idx].replica.executor.reply_cache.contains_key(client),
        ensures
            ({
                // let (qs, batches, batch_num, req_num) = lemma_ReplyInReplyCacheIsAllowed(b, c, i, client, idx);
                let qs = rc.0;
                let batches = rc.1;
                let batch_num = rc.2;
                let req_num = rc.3;
                &&& IsValidQuorumOf2bsSequence(b[i], qs)
                &&& batches == GetSequenceOfRequestBatches(qs)
                &&& 0 <= batch_num < batches.len()
                &&& 0 <= req_num < batches[batch_num].len()
                &&& b[i].replicas[idx].replica.executor.reply_cache[client] == GetReplyFromRequestBatches(batches, batch_num, req_num)
            }),
        decreases i,
    {
        if i == 0 {
            return arbitrary();
        }
    
        lemma_ConstantsAllConsistent(b, c, i - 1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_AssumptionsMakeValidTransition(b, c, i - 1);
    
        let s = b[i - 1].replicas[idx].replica.executor;
        let s_prime = b[i].replicas[idx].replica.executor;
        if s.reply_cache.contains_key(client) && s_prime.reply_cache[client] == s.reply_cache[client] {
            let (qs_prev, batches_prev, batch_num_prev, req_num_prev) = lemma_ReplyInReplyCacheIsAllowed(b, c, i - 1, client, idx);
            return (qs_prev, batches_prev, batch_num_prev, req_num_prev);
        }
    
        let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i - 1, idx);
        let next_action_index = b[i - 1].replicas[idx].nextActionIndex;
        if next_action_index == 0 {
            let p = ios[0]->r;
            let (qs_prev, batches_prev, batch_num_prev, req_num_prev) = lemma_ReplyInAppStateSupplyIsAllowed(b, c, i - 1, client, p);
            return (qs_prev, batches_prev, batch_num_prev, req_num_prev);
        }
    
        assert(next_action_index == 6);
    
        let qs_prev = lemma_AppStateAlwaysValid(b, c, i - 1, idx);
        let q = lemma_DecidedOperationWasChosen(b, c, i - 1, idx);
        let qs_new = qs_prev + seq![q];
        let batches_new = GetSequenceOfRequestBatches(qs_new);
        let batch_num_new = qs_prev.len() as int;
    
        assert(GetSequenceOfRequestBatches(qs_prev) == batches_new.subrange(0, batch_num_new));
        assert(s.app == GetAppStateFromRequestBatches(GetSequenceOfRequestBatches(qs_prev)));
    
        let batch = s.next_op_to_execute->v;
        let replies = HandleRequestBatch(s.app, batch).1;
    
        let req_num_new = choose |req_num: int| 0 <= req_num < batch.len() && replies[req_num].client == client && s_prime.reply_cache[client] == replies[req_num];
    
        return (qs_new, batches_new, batch_num_new, req_num_new);
    }

    #[verifier::external_body]
    pub proof fn lemma_ReplyInAppStateSupplyIsAllowed(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        client: AbstractEndPoint,
        p: RslPacket
    ) -> (rc:(Seq<QuorumOf2bs>, Seq<RequestBatch>, int, int))
        requires
            IsValidBehaviorPrefix(b, c, i + 1),
            0 <= i,
            b[i].environment.sentPackets.contains(p),
            c.config.replica_ids.contains(p.src),
            p.msg is RslMessageAppStateSupply,
            p.msg->reply_cache.contains_key(client),
        ensures
            ({
                // let (qs, batches, batch_num, req_num) = lemma_ReplyInAppStateSupplyIsAllowed(b, c, i, client, p);
                let qs = rc.0;
                let batches = rc.1;
                let batch_num = rc.2;
                let req_num = rc.3;
                &&& IsValidQuorumOf2bsSequence(b[i], qs)
                &&& batches == GetSequenceOfRequestBatches(qs)
                &&& 0 <= batch_num < batches.len()
                &&& 0 <= req_num < batches[batch_num].len()
                &&& p.msg->reply_cache[client] == GetReplyFromRequestBatches(batches, batch_num, req_num)
            })
        decreases i,
    {
        if i == 0 {
            return arbitrary();
        }

        lemma_ConstantsAllConsistent(b, c, i - 1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_AssumptionsMakeValidTransition(b, c, i - 1);

        if b[i - 1].environment.sentPackets.contains(p) {
            let (qs_prev, batches_prev, batch_num_prev, req_num_prev) = lemma_ReplyInAppStateSupplyIsAllowed(b, c, i - 1, client, p);
            lemma_IfValidQuorumOf2bsSequenceNowThenNext(b, c, i - 1, qs_prev);
            return (qs_prev, batches_prev, batch_num_prev, req_num_prev);
        }

        let (idx, ios) = lemma_ActionThatSendsAppStateSupplyIsProcessAppStateRequest(b[i - 1], b[i], p);
        let (qs_new, batches_new, batch_num_new, req_num_new) = lemma_ReplyInReplyCacheIsAllowed(b, c, i - 1, client, idx);
        
        return (qs_new, batches_new, batch_num_new, req_num_new);
    }

    #[verifier::external_body]
    pub proof fn lemma_ReplySentViaExecutionIsAllowed(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        p: RslPacket,
        idx: int,
        ios: Seq<RslIo>
    ) -> (
        rc:(Seq<QuorumOf2bs>, Seq<RequestBatch>, int, int)
    )
        requires
            ({
                let next_step = LEnvStep::LEnvStepHostIos{actor:c.config.replica_ids[idx], ios:ios};
                &&& IsValidBehaviorPrefix(b, c, i + 1)
                &&& 0 <= i
                &&& 0 <= idx < c.config.replica_ids.len()
                &&& 0 <= idx < b[i].replicas.len()
                &&& ios.contains(LIoOp::Send{s:p})
                &&& RslNext(b[i], b[i + 1])
                &&& b[i].environment.nextStep == next_step
                &&& b[i].replicas[idx].replica.executor.next_op_to_execute is OutstandingOpKnown
                &&& LtUpperBound(
                    b[i].replicas[idx].replica.executor.ops_complete,
                    b[i].replicas[idx].replica.executor.constants.all.params.max_integer_val
                )
                &&& LReplicaConstantsValid(b[i].replicas[idx].replica.executor.constants)
                &&& LExecutorExecute(
                    b[i].replicas[idx].replica.executor,
                    b[i + 1].replicas[idx].replica.executor,
                    ExtractSentPacketsFromIos(ios)
                )
            })
            // IsValidBehaviorPrefix(b, c, i + 1),
            // 0 <= i,
            // 0 <= idx < c.config.replica_ids.len(),
            // 0 <= idx < b[i].replicas.len(),
            // ios.contains(LIoOp::Send{s:p}),
            // RslNext(b[i], b[i + 1]),
            // b[i].environment.nextStep == LEnvStepHostIos{actor:c.config.replica_ids[idx], ios:ios},
            // b[i].replicas[idx].replica.executor.next_op_to_execute is OutstandingOpKnown,
            // LtUpperBound(
            //     b[i].replicas[idx].replica.executor.ops_complete,
            //     b[i].replicas[idx].replica.executor.constants.all.params.max_integer_val
            // ),
            // LReplicaConstantsValid(b[i].replicas[idx].replica.executor.constants),
            // LExecutorExecute(
            //     b[i].replicas[idx].replica.executor,
            //     b[i + 1].replicas[idx].replica.executor,
            //     ExtractSentPacketsFromIos(ios)
            // ),
        ensures
            ({
                let reply = Reply{client:p.dst, seqno:p.msg->seqno_reply, reply:p.msg->reply};
                let qs = rc.0;
                let batches = rc.1;
                let batch_num = rc.2;
                let req_num = rc.3;
                &&& IsValidQuorumOf2bsSequence(b[i], qs)
                &&& batches == GetSequenceOfRequestBatches(qs)
                &&& 0 <= batch_num < batches.len()
                &&& 0 <= req_num < batches[batch_num].len()
                &&& reply == GetReplyFromRequestBatches(batches, batch_num, req_num)
            })
    {
        lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
        lemma_ReplicaConstantsAllConsistent(b, c, i + 1, idx);
    
        let qs_prev = lemma_AppStateAlwaysValid(b, c, i, idx);
        let q = lemma_DecidedOperationWasChosen(b, c, i, idx);
        let qs = qs_prev + seq![q];
        let batches = GetSequenceOfRequestBatches(qs);
        let batch_num = qs_prev.len() as int;
    
        assert(GetSequenceOfRequestBatches(qs_prev) == batches.subrange(0, batch_num));
    
        let s = b[i].replicas[idx].replica.executor;
        assert(s.app == GetAppStateFromRequestBatches(GetSequenceOfRequestBatches(qs_prev)));
    
        let batch = s.next_op_to_execute->v;
        let temp = HandleRequestBatch(s.app, batch);
        lemma_HandleRequestBatchTriggerHappy(s.app, batch, temp.0, temp.1);
        let new_state = temp.0.last();
        let replies = temp.1;
        let me = c.config.replica_ids[idx];
    
        assert(GetPacketsFromReplies(me, batch, replies).contains(p));
        assert(p.src == c.config.replica_ids[idx]);
        let req_num = lemma_GetRequestIndexCorrespondingToPacketInGetPacketsFromReplies(p, me, batch, replies);
        let reply = Reply{client:p.dst, seqno:p.msg->seqno_reply, reply:p.msg->reply};
        assert(reply == replies[req_num]);
        (qs, batches, batch_num, req_num)
    }

    pub proof fn lemma_GetRequestIndexCorrespondingToPacketInGetPacketsFromReplies(
        p: RslPacket,
        me: AbstractEndPoint,
        requests: Seq<Request>,
        replies: Seq<Reply>
    ) -> (i: int)
        requires
            requests.len() == replies.len(),
            forall |r: Reply| replies.contains(r) ==> r is Reply,
            GetPacketsFromReplies(me, requests, replies).contains(p),
        ensures
            0 <= i < requests.len(),
            p.src == me,
            p.dst == requests[i].client,
            p.msg is RslMessageReply,
            p.msg->seqno_reply == requests[i].seqno,
            p.msg->reply == replies[i].reply,
        decreases requests.len()
    {
        if requests.len() == 0 {
            assert(false);
        }

        let pkt = LPacket{dst:requests[0].client, src:me, msg: RslMessage::RslMessageReply{seqno_reply:requests[0].seqno, reply:replies[0].reply}};
    
        if p == pkt {
            0
        } else {
            let i_minus_1 = lemma_GetRequestIndexCorrespondingToPacketInGetPacketsFromReplies(
                p,
                me,
                requests.drop_first(),
                replies.drop_first(),
                // requests.subrange(1, requests.len() as int),
                // replies.subrange(1, replies.len() as int),
            );
            i_minus_1 + 1
        }
    }

   
}