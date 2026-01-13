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
use crate::protocol::RSL::state_machine::*;
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
use crate::protocol::RSL::refinement_proof::requests::*;
use crate::protocol::RSL::refinement_proof::execution::*;

use crate::services::RSL::app_state_machine::*;

use crate::common::logic::temporal_s::*;
use crate::common::logic::heuristics_i::*;
use crate::common::framework::environment_s::*;
use crate::common::framework::environment_s::LEnvStep;
use crate::common::native::io_s::*;
use crate::common::collections::maps2::*;
use crate::common::collections::sets::*;

verus!{
    pub open spec fn GetServerAddresses(ps:RslState) -> Set<AbstractEndPoint>
    {
        // let f = 
        // MapSeqToSet(ps.constants.config.replica_ids, |x| x)
        ps.constants.config.replica_ids.to_set()
    }
    

    pub open spec fn ProduceIntermediateAbstractState(
        server_addresses: Set<AbstractEndPoint>,
        batches: Seq<RequestBatch>,
        reqs_in_last_batch: int
    ) -> RSLSystemState
        recommends
            batches.len() > 0,
            0 <= reqs_in_last_batch <= batches.last().len(),
    {
        // let batch_num_ = 
        let requests = Set::new(|req:Request| exists |batch_num:int, req_num:int| 
                                 0 <= batch_num < batches.len()
                              && 0 <= req_num < (if batch_num == batches.len()-1 {reqs_in_last_batch} else {batches[batch_num].len() as int} )
                              && batches[batch_num][req_num] == req);
        
        let replies = Set::new(|rep:Reply| exists |batch_num:int, req_num:int| 
                                  0 <= batch_num < batches.len()
                              && 0 <= req_num < (if batch_num == batches.len()-1 {reqs_in_last_batch} else {batches[batch_num].len() as int} )
                              && GetReplyFromRequestBatches(batches, batch_num, req_num) == rep);
        
        let state_before_prev_batch = GetAppStateFromRequestBatches(batches.subrange(0, batches.len() - 1));
        let (app_states_during_batch, _) = HandleRequestBatch(state_before_prev_batch, batches.last());
        
        RSLSystemState{server_addresses:server_addresses, app:app_states_during_batch[reqs_in_last_batch], requests:requests, replies:replies}
    }

    pub open spec fn ProduceAbstractState(server_addresses:Set<AbstractEndPoint>, batches:Seq<RequestBatch>) -> RSLSystemState
    {
        let requests = Set::new(|req:Request| exists |batch_num:int, req_num:int| 
                                                  0 <= batch_num < batches.len()
                                              && 0 <= req_num < batches[batch_num].len()
                                              && batches[batch_num][req_num] == req);

        let replies = Set::new(|rep:Reply| exists |batch_num:int, req_num:int| 
                                                0 <= batch_num < batches.len()
                                            && 0 <= req_num < batches[batch_num].len()
                                            && GetReplyFromRequestBatches(batches, batch_num, req_num) == rep);
        RSLSystemState{server_addresses:server_addresses, app:GetAppStateFromRequestBatches(batches), requests:requests, replies:replies}
    }

    pub open spec fn SystemRefinementRelation(ps: RslState, rs: RSLSystemState) -> bool {
        exists |qs: Seq<QuorumOf2bs>|
            IsMaximalQuorumOf2bsSequence(ps, qs) &&
            rs == ProduceAbstractState(GetServerAddresses(ps), GetSequenceOfRequestBatches(qs))
    }

    pub proof fn lemma_ProduceAbstractStateSatisfiesRefinementRelation(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        qs: Seq<QuorumOf2bs>,
        rs: RSLSystemState
    )
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            IsMaximalQuorumOf2bsSequence(b[i], qs),
            rs == ProduceAbstractState(GetServerAddresses(b[i]), GetSequenceOfRequestBatches(qs)),
        ensures
            RslSystemRefinement(b[i], rs),
    {
        let ps = b[i];
        let batches = GetSequenceOfRequestBatches(qs);

        lemma_ConstantsAllConsistent(b, c, i);
        
        assert forall |p: RslPacket| ps.environment.sentPackets.contains(p) && rs.server_addresses.contains(p.src) && p.msg is RslMessageReply 
            implies rs.replies.contains(Reply{client:p.dst, seqno:p.msg->seqno_reply, reply:p.msg->reply}) by {
            assert(GetServerAddresses(ps).contains(p.src));
            let (qs_prime, batches_prime, batch_num, req_num) = lemma_ReplySentIsAllowed(b, c, i, p);
            lemma_RegularQuorumOf2bSequenceIsPrefixOfMaximalQuorumOf2bSequence(b, c, i, qs_prime, qs);
            lemma_GetReplyFromRequestBatchesMatchesInSubsequence(batches_prime, batches, batch_num, req_num);
        }

        assert forall |req: Request| rs.requests.contains(req) 
            implies exists |p: RslPacket| ps.environment.sentPackets.contains(p) && rs.server_addresses.contains(p.dst) 
                && p.msg is RslMessageRequest && req == Request{client:p.src, seqno:p.msg->seqno_req, request:p.msg->val} by {
            let (batch_num, req_num) = choose |batch_num: int, req_num: int| 
                0 <= batch_num < batches.len() && 0 <= req_num < batches[batch_num].len() && req == batches[batch_num][req_num];
            let p = lemma_DecidedRequestWasSentByClient(b, c, i, qs, batches, batch_num, req_num);
        }
    }

    pub proof fn lemma_ProduceIntermediateAbstractStatesSatisfiesNext(
        server_addresses: Set<AbstractEndPoint>,
        batches: Seq<RequestBatch>,
        reqs_in_last_batch: int
    ) -> (request: Request)
        requires
            batches.len() > 0,
            0 <= reqs_in_last_batch < batches.last().len(),
        ensures
            request == batches.last()[reqs_in_last_batch],
            RslSystemNextServerExecutesRequest(
                ProduceIntermediateAbstractState(server_addresses, batches, reqs_in_last_batch),
                ProduceIntermediateAbstractState(server_addresses, batches, reqs_in_last_batch + 1),
                request,
            ),
    {
        let rs = ProduceIntermediateAbstractState(server_addresses, batches, reqs_in_last_batch);
        let rs_prime = ProduceIntermediateAbstractState(server_addresses, batches, reqs_in_last_batch + 1);
    
        let request = batches.last()[reqs_in_last_batch];
        let reply = GetReplyFromRequestBatches(batches, batches.len() - 1, reqs_in_last_batch);
    
        assert(rs_prime.requests == rs.requests + set![request]);
        assert(rs_prime.replies == rs.replies + set![reply]);
    
        let state_before_prev_batch = GetAppStateFromRequestBatches(batches.drop_last());
        let app_states_during_batch = HandleRequestBatch(state_before_prev_batch, batches.last()).0;
        let g_replies = HandleRequestBatch(state_before_prev_batch, batches.last()).1;
        lemma_HandleRequestBatchTriggerHappy(state_before_prev_batch, batches.last(), app_states_during_batch, g_replies);
        let result = AppHandleRequest(rs.app, batches.last()[reqs_in_last_batch].request);
        assert(rs_prime.app == result.0);
        assert(reply.reply == result.1);
    
        assert(RslSystemNextServerExecutesRequest(rs, rs_prime, request));
        request
    }
    
    #[verifier::external_body]
    pub proof fn lemma_FirstProduceIntermediateAbstractStateProducesAbstractState(
        server_addresses: Set<AbstractEndPoint>,
        batches: Seq<RequestBatch>
    )
        requires batches.len() > 0,
        ensures ProduceAbstractState(server_addresses, batches.drop_last()) == 
                ProduceIntermediateAbstractState(server_addresses, batches, 0),
    {
        let rs = ProduceAbstractState(server_addresses, batches.drop_last());
        let rs_prime = ProduceIntermediateAbstractState(server_addresses, batches, 0);
    
        let requests = Set::new(|req:Request| exists |batch_num:int, req_num:int|
            0 <= batch_num < batches.len() as int &&
            0 <= req_num < (if batch_num == batches.len() - 1 { 0 } else { batches[batch_num].len() })
            && batches[batch_num][req_num] == req);
    
        let replies = Set::new(|rep:Reply| exists |batch_num:int, req_num:int|
            0 <= batch_num < batches.len() &&
            0 <= req_num < (if batch_num == batches.len() - 1 { 0 } else { batches[batch_num].len() })
            && GetReplyFromRequestBatches(batches, batch_num, req_num) == rep);
    
        let state_before_prev_batch = GetAppStateFromRequestBatches(batches.drop_last());
        let app_states_during_batch = HandleRequestBatch(state_before_prev_batch, batches.last()).0;
        let replies_prime = HandleRequestBatch(state_before_prev_batch, batches.last()).1;
        lemma_HandleRequestBatchTriggerHappy(state_before_prev_batch, batches.last(), app_states_during_batch, replies_prime);
    
        assert forall |req: Request| rs_prime.requests.contains(req) implies rs.requests.contains(req) by {
            let (batch_num, req_num) = choose |batch_num: int, req_num: int|
                0 <= batch_num < batches.len() &&
                0 <= req_num < (if batch_num == batches.len() - 1 { 0 } else { batches[batch_num].len() })
                && req == batches[batch_num][req_num];
            assert(rs.requests.contains(req));
        };
    
        assert forall |reply: Reply| rs_prime.replies.contains(reply) implies rs.replies.contains(reply) by {
            let (batch_num, req_num) = choose |batch_num: int, req_num: int|
                0 <= batch_num < batches.len() &&
                0 <= req_num < (if batch_num == batches.len() - 1 { 0 } else { batches[batch_num].len() })
                && reply == GetReplyFromRequestBatches(batches, batch_num, req_num);
            assert(rs.replies.contains(reply));
        };
    
        assert forall |reply: Reply| rs.replies.contains(reply) implies rs_prime.replies.contains(reply) by {
            let (batch_num, req_num) = choose |batch_num: int, req_num: int|
                0 <= batch_num < batches.len() - 1 &&
                0 <= req_num < batches[batch_num].len() &&
                reply == GetReplyFromRequestBatches(batches.drop_last(), batch_num, req_num);
            assert(rs_prime.replies.contains(reply));
        };
        
        assert(rs_prime.requests == rs.requests);
        assert(rs_prime.replies == rs.replies);
    }

    #[verifier::external_body]
    pub proof fn lemma_LastProduceIntermediateAbstractStateProducesAbstractState(
        server_addresses: Set<AbstractEndPoint>,
        batches: Seq<RequestBatch>
    )
        requires batches.len() > 0,
        ensures ProduceAbstractState(server_addresses, batches) == 
                ProduceIntermediateAbstractState(server_addresses, batches, batches.last().len() as int),
    {
        let rs = ProduceAbstractState(server_addresses, batches);
        let rs_prime = ProduceIntermediateAbstractState(server_addresses, batches, batches.last().len() as int);
    
        assert(rs_prime.requests == rs.requests);
    
        assert forall |reply: Reply| rs_prime.replies.contains(reply) implies rs.replies.contains(reply) by {
            let (batch_num, req_num) = choose |batch_num: int, req_num: int|
                0 <= batch_num < batches.len() &&
                0 <= req_num < (if batch_num == batches.len() - 1 { batches.last().len() } else { batches[batch_num].len() })
                && reply == GetReplyFromRequestBatches(batches, batch_num, req_num);
            assert(0 <= req_num < batches[batch_num].len());
        };
    
        assert(rs_prime.replies == rs.replies);
        assert(rs_prime.server_addresses == rs.server_addresses);
        assert(rs_prime.app == rs.app); /* fails*/
    }

    pub open spec fn ConvertBehaviorSeqToImap<T>(s:Seq<T>) -> Map<int, T>
        recommends s.len() > 0
        // ensures  imaptotal(ConvertBehaviorSeqToImap(s))
        // ensures  forall i :: 0 <= i < |s| ==> ConvertBehaviorSeqToImap(s)[i] == s[i]
    {
        // imap i {:trigger s[i]} :: if i < 0 then s[0] else if 0 <= i < |s| then s[i] else last(s)
        Map::new(|i:int| i == i, |i:int| if i < 0 { s[0] } else if 0 <= i < s.len() { s[i] } else { s.last() })
    }

    pub proof fn lemma_ConvertBehaviorSeqToImap_ensures<T>(s:Seq<T>)
        requires s.len() > 0 
        ensures imaptotal(ConvertBehaviorSeqToImap(s)),
                forall |i:int| 0 <= i < s.len() ==> ConvertBehaviorSeqToImap(s)[i] == s[i]
    {

    }

    pub open spec fn RslSystemBehaviorRefinementCorrectImap(
        b: Behavior<RslState>,
        prefix_len: int,
        high_level_behavior: Seq<RSLSystemState>
    ) -> bool {
        &&& imaptotal(b)
        &&& high_level_behavior.len() == prefix_len
        &&& (forall|i: int| 0 <= i < prefix_len ==> RslSystemRefinement(b[i], high_level_behavior[i]))
        &&& high_level_behavior.len() > 0
        &&& RslSystemInit(high_level_behavior[0], Set::new(|x: AbstractEndPoint| b[0].constants.config.replica_ids.contains(x)))
        &&& (forall|i: int| #![trigger high_level_behavior[i]] 0 <= i < high_level_behavior.len() - 1 ==> RslSystemNext(high_level_behavior[i], high_level_behavior[i + 1]))
    }

    #[verifier::external_body]
    pub proof fn lemma_GetBehaviorRefinementForBehaviorOfOneStep(
        b: Behavior<RslState>,
        c: LConstants
    ) -> (high_level_behavior: Seq<RSLSystemState>)
        requires imaptotal(b),
                 RslInit(c, b[0])
        ensures RslSystemBehaviorRefinementCorrectImap(b, 1, high_level_behavior),
                high_level_behavior.len() == 1,
                SystemRefinementRelation(b[0], high_level_behavior[0]),
    {
        let mut qs: Seq<QuorumOf2bs> = Seq::empty();
        let rs = ProduceAbstractState(GetServerAddresses(b[0]), GetSequenceOfRequestBatches(qs));
        
        if exists|q: QuorumOf2bs| IsValidQuorumOf2bs(b[0], q) && q.opn == 0 {
            let q = choose|q: QuorumOf2bs| IsValidQuorumOf2bs(b[0], q) && q.opn == 0;
            let idx = choose|idx: int| q.indices.contains(idx);
            let packet = q.packets[idx];
            assert(false);
        }
        
        assert(IsMaximalQuorumOf2bsSequence(b[0], qs));
        assert(SystemRefinementRelation(b[0], rs));
        let high_level_behavior = seq![rs];
        high_level_behavior
    }

    pub proof fn lemma_DemonstrateRslSystemNextWhenBatchExtended(
        server_addresses: Set<AbstractEndPoint>,
        s: RSLSystemState,
        s_prime: RSLSystemState,
        batches: Seq<RequestBatch>,
        count: int
    ) -> (rc:(Seq<RSLSystemState>, Seq<Request>))
        requires batches.len() > 0,
                 0 <= count <= batches.last().len(),
                 s == ProduceIntermediateAbstractState(server_addresses, batches, 0),
                 s_prime == ProduceIntermediateAbstractState(server_addresses, batches, count)
        ensures 
                ({
                    let intermediate_states = rc.0;
                    let batch = rc.1;
                    &&& RslStateSequenceReflectsBatchExecution(s, s_prime, intermediate_states, batch)
                    &&& RslSystemNext(s, s_prime)
                })
        decreases count
    {
        if count == 0 {
            assert(s_prime == s);
            let intermediate_states = seq![s];
            let batch = seq![];
            assert(RslStateSequenceReflectsBatchExecution(s, s_prime, intermediate_states, batch));
            return (intermediate_states, batch);
        }
    
        let s_middle = ProduceIntermediateAbstractState(server_addresses, batches, count - 1);
        let (intermediate_states_middle, batch_middle) =
            lemma_DemonstrateRslSystemNextWhenBatchExtended(server_addresses, s, s_middle, batches, count - 1);
        
        let intermediate_states = intermediate_states_middle.push(s_prime);
        
        let next_request = lemma_ProduceIntermediateAbstractStatesSatisfiesNext(server_addresses, batches, count - 1);
        let batch = batch_middle.push(next_request);
        
        assert(RslSystemNextServerExecutesRequest(s_middle, s_prime, next_request));
        assert(RslStateSequenceReflectsBatchExecution(s, s_prime, intermediate_states, batch));
        (intermediate_states, batch)
    }
    

    #[verifier::external_body]
    proof fn lemma_DemonstrateRslSystemNextWhenBatchesAdded(
        server_addresses: Set<AbstractEndPoint>,
        s: RSLSystemState,
        s_prime: RSLSystemState,
        batches: Seq<RequestBatch>,
        batches_prime: Seq<RequestBatch>
    ) -> (rc:(Seq<RSLSystemState>, Seq<Request>))
        requires
            s == ProduceAbstractState(server_addresses, batches),
            s_prime == ProduceAbstractState(server_addresses, batches_prime),
            batches.len() <= batches_prime.len(),
            batches_prime.subrange(0, batches.len() as int) == batches,
        ensures
            ({
                let intermediate_states = rc.0;
                let batch = rc.1;
                &&& RslStateSequenceReflectsBatchExecution(s, s_prime, intermediate_states, batch)
                &&& RslSystemNext(s, s_prime)
            })
            
        decreases batches_prime.len()
    {
        if batches.len() == batches_prime.len() {
            assert(batches_prime == batches);
            assert(s==s_prime);
            let intermediate_states = seq![s];
            let batch = Seq::<Request>::empty();
            assert(RslStateSequenceReflectsBatchExecution(s, s_prime, intermediate_states, batch));
            return (intermediate_states, batch);
        }

        let s_middle = ProduceAbstractState(server_addresses, batches_prime.drop_last());
        let (intermediate_states_middle, batch_middle) = 
            lemma_DemonstrateRslSystemNextWhenBatchesAdded(server_addresses, s, s_middle, batches, batches_prime.drop_last());

        lemma_FirstProduceIntermediateAbstractStateProducesAbstractState(server_addresses, batches_prime);
        lemma_LastProduceIntermediateAbstractStateProducesAbstractState(server_addresses, batches_prime);

        let (intermediate_states_next, batch_next) = 
            lemma_DemonstrateRslSystemNextWhenBatchExtended(server_addresses, s_middle, s_prime, batches_prime, batches_prime.last().len() as int);

        let intermediate_states = intermediate_states_middle.drop_last() + intermediate_states_next;
        let batch = batch_middle + batch_next;

        assert(RslStateSequenceReflectsBatchExecution(s, s_prime, intermediate_states, batch));
        (intermediate_states, batch)
    }

    pub proof fn lemma_GetBehaviorRefinementForPrefix(
        b: Behavior<RslState>,
        c: LConstants,
        i: int
    ) -> (high_level_behavior: Seq<RSLSystemState>)
        requires 
            0 <= i, 
            IsValidBehaviorPrefix(b, c, i)
        ensures 
            RslSystemBehaviorRefinementCorrectImap(b, i+1, high_level_behavior),
            SystemRefinementRelation(b[i], high_level_behavior.last())
        decreases i
    {
        if i == 0 {
            let high_level_behavior = lemma_GetBehaviorRefinementForBehaviorOfOneStep(b, c);
            return high_level_behavior;
        }
    
        lemma_ConstantsAllConsistent(b, c, i-1);
        lemma_ConstantsAllConsistent(b, c, i);
        assert(GetServerAddresses(b[i-1]) == GetServerAddresses(b[i]));
        let server_addresses = GetServerAddresses(b[i-1]);
    
        let prev_high_level_behavior = lemma_GetBehaviorRefinementForPrefix(b, c, i-1);
        let prev_rs = prev_high_level_behavior.last();
        let prev_qs = choose |prev_qs:Seq<QuorumOf2bs>| IsMaximalQuorumOf2bsSequence(b[i-1], prev_qs)
                                                        && prev_rs == ProduceAbstractState(server_addresses, GetSequenceOfRequestBatches(prev_qs));
        
        let prev_batches = GetSequenceOfRequestBatches(prev_qs);
    
        let qs = lemma_GetMaximalQuorumOf2bsSequence(b, c, i);
        let batches = GetSequenceOfRequestBatches(qs);
    
        lemma_IfValidQuorumOf2bsSequenceNowThenNext(b, c, i-1, prev_qs);
        lemma_RegularQuorumOf2bSequenceIsPrefixOfMaximalQuorumOf2bSequence(b, c, i, prev_qs, qs);
    
        let s_prime = ProduceAbstractState(server_addresses, batches);
        let (intermediate_states, batch) = lemma_DemonstrateRslSystemNextWhenBatchesAdded(
            server_addresses, prev_high_level_behavior.last(),
            s_prime, prev_batches, batches
        );
    
        let high_level_behavior = prev_high_level_behavior + seq![s_prime];
        
        lemma_ProduceAbstractStateSatisfiesRefinementRelation(b, c, i, qs, high_level_behavior.last());
        assert(RslSystemRefinement(b[i], high_level_behavior.last()));
        high_level_behavior
    }
    
    #[verifier::external_body]
    pub proof fn lemma_GetBehaviorRefinement(
        low_level_behavior: Seq<RslState>,
        c: LConstants
    ) -> (high_level_behavior: Seq<RSLSystemState>)
        requires 
            low_level_behavior.len() > 0,
            RslInit(c, low_level_behavior[0]),
            forall |i: int| #![trigger low_level_behavior[i]] 0 <= i < low_level_behavior.len() - 1 ==> RslNext(low_level_behavior[i], low_level_behavior[i+1])
        ensures 
            RslSystemBehaviorRefinementCorrect(MapSeqToSet(c.config.replica_ids, |x| x), low_level_behavior, high_level_behavior)
    {
        let b = ConvertBehaviorSeqToImap(low_level_behavior);
        lemma_ConvertBehaviorSeqToImap_ensures(low_level_behavior);
        let high_level_behavior = lemma_GetBehaviorRefinementForPrefix(b, c, low_level_behavior.len() - 1);
        high_level_behavior
    }
}
