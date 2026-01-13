use crate::common::collections::vecs::*;
use crate::implementation::common::generic_refinement::*;
use crate::implementation::RSL::appinterface::*;
use crate::implementation::RSL::types_i::*;
use crate::protocol::RSL::state_machine::*;
use crate::protocol::RSL::types::*;
use crate::services::RSL::app_state_machine::*;
use builtin::*;
use builtin_macros::*;
use std::collections::HashMap;
use vstd::{prelude::*, seq::*, seq_lib::*};

verus! {
pub fn CHandleRequest(state:&CAppState, request:&CRequest) -> ( result:(CAppState, CReply))
    requires
        CAppStateIsValid(state),
        request.valid()
    ensures
        AbstractifyCAppStateToAppState(&result.0) == HandleRequest(AbstractifyCAppStateToAppState(state), request.view()).0,
        result.1.view() == HandleRequest(AbstractifyCAppStateToAppState(state), request.view()).1
{
    let (new_state, reply) = HandleAppRequest(&state, &request.request);
    (new_state, CReply { client: request.client.clone_up_to_view(), seqno: request.seqno, reply })
}

// #[verifier(external_body)]
pub fn CHandleRequestBatchHidden(state:&CAppState, batch:&CRequestBatch) -> (result:(Vec<CAppState>, Vec<CReply>))
    requires
        CAppStateIsValid(state),
        crequestbatch_is_valid(batch)
    ensures
        // result.0.len()>0,
        result.0.len() == batch.len()+1,
        (result.0@.map(|i,x:CAppState| x@),result.1@.map(|i,y:CReply| y@)) == HandleRequestBatchHidden(state@, abstractify_crequestbatch(batch)),
        // result.1.len() == batch.len(),
        // ({
        //     let cr0 = result.0;
        //     let cr1 = result.1;
        //     let (lr0, lr1) = HandleRequestBatchHidden(AbstractifyCAppStateToAppState(&state), abstractify_crequestbatch(batch));
        //     &&& cr0.len() == batch.len() + 1
        //     &&& cr1.len() == batch.len()
        //     // &&& forall |i:int| 0 <= i < cr0.len() ==> cr0[i].valid()
        //     &&& forall |i:int| 0 <= i < cr1.len() ==> cr1[i].valid()
        //     &&& cr1@.map(|i, x: CReply| x@) == lr1
        //     &&& cr0@.map(|i, x: CAppState| x@) == lr0
        // })
    // decreases batch.len()
{
    if batch.len() == 0 {
        let states = vec![state.clone()];
        let replies = vec![];
        let ghost s = AbstractifyCAppStateToAppState(state);
        let ghost b = abstractify_crequestbatch(batch);
        let ghost (ss, rs) = HandleRequestBatchHidden(s,b);
        assert(states@.map(|i, x: CAppState| x@)==ss);
        assert(replies@.map(|i, x: CReply| x@)==rs);
        // assert(HandleRequestBatchHidden(s,b)==(states@.map(|i, x: CAppState| x@),replies@.map(|i, x: CReply| x@)));
        (states, replies)
    } else {

        let t_vec = &truncate_vec(batch, 0, batch.len() - 1);
        assert(t_vec@.len()==batch@.len()-1);
        let (rest_states, rest_replies) = CHandleRequestBatchHidden(state, t_vec);

        assert(rest_states@.len() > 0);// rest state will always have one value
        let (new_state, reply) = HandleAppRequest(&rest_states[rest_states.len()-1], &batch[batch.len()-1].clone_up_to_view().request);


        let mut states = rest_states;
        states.push(new_state);
        let mut replies = rest_replies;
        replies.push(CReply{client: batch[batch.len()-1].client.clone(), seqno: batch[batch.len()-1].seqno, reply: reply});

        let ghost s = AbstractifyCAppStateToAppState(&state);
        let ghost b = abstractify_crequestbatch(&batch);
        let ghost b_clone = b;
        assert(b_clone.len()>0);
        let ghost (rs, rp) = HandleRequestBatchHidden(s, b_clone.drop_last());
        assert(rs.len()>0);
        let ghost (s1, r) = AppHandleRequest(rs.last(), b.last().request);
        // assert(b.take(b.len() - 1) == abstractify_crequestbatch(batch[0..batch.len()-1].to_vec()));
        assert(new_state@==s1);
        assert(reply@==r);
        // let ghost s = AbstractifyCAppStateToAppState(state);
        // let ghost b = abstractify_crequestbatch(batch);
        let ghost (ss_prime, rs_prime) = HandleRequestBatchHidden(s, b);
        assert(states@.len()==ss_prime.len());
        assert(replies@.len()==rs_prime.len());
        assert(states@.last()@ == ss_prime.last());

        
        let ghost expected_reply = Reply {
            client: batch[batch.len()-1].client@,
            seqno: batch[batch.len()-1].seqno as int,
            reply: reply@,
        };
        
        let ghost expected = rest_replies@.map(|i, x:CReply| x@) + seq![expected_reply];
        assert(rs_prime == expected);
        
        //Endpoints and Replies are not holding across refinement
        assume(replies@[replies.len()-1]@.client == rs_prime.last().client);
        assert(replies@[replies.len()-1]@.seqno == rs_prime.last().seqno);
        assume(replies@[replies.len()-1]@.reply == rs_prime.last().reply);
        assert(replies@[replies@.len()-1]@ == expected_reply);
        assert(rs_prime[rs_prime.len()-1] == expected_reply);
        
        assert(replies@.last()@ == rs_prime.last()); 
        assert(states@.map(|i, x: CAppState| x@) == ss_prime);
        assert(replies@.map(|i, x: CReply| x@) == rs_prime);
        assert(
            HandleRequestBatchHidden(AbstractifyCAppStateToAppState(state), abstractify_crequestbatch(batch)) ==
            (states@.map(|i, x: CAppState| x@), replies@.map(|i, x: CReply| x@))
        );

        (states, replies)
    }
}


// #[verifier(external_body)]
pub fn CHandleRequestBatch(state:&CAppState, batch:&CRequestBatch) -> (rc:(Vec<CAppState>, Vec<CReply>))
    requires
        CAppStateIsValid(state),
        crequestbatch_is_valid(batch)
    ensures
        (rc.0@.map(|i, x: CAppState| x@), rc.1@.map(|i, x: CReply| x@)) == HandleRequestBatch(state@, batch@.map(|i, x:CRequest| x@))
        // ({
        //     let states = rc.0;
        //     let replies = rc.1;
        //     let (lr0, lr1) = HandleRequestBatch(AbstractifyCAppStateToAppState(state), abstractify_crequestbatch(batch));
        //     &&& states[0] == state
        //     &&& states.len() == batch.len() + 1
        //     &&& replies.len() == batch.len()
        //     // &&& (forall |i:int| 0 <= i < batch.len() ==>
        //     //         replies[i] is CReply
        //     //         && (states[i+1], replies[i].reply) == HandleAppRequest(states[i], batch[i].request)
        //     //         && replies[i].client == batch[i].client
        //     //         && replies[i].seqno == batch[i].seqno
        //     //     )
        //     &&& (forall |i:int| 0 <= i < states@.len() ==> CAppStateIsValid(&states[i]))
        //     &&& (forall |i:int| 0 <= i < replies@.len() ==> replies[i].valid())
        //     &&& states@.map(|i, s:CAppState| AbstractifyCAppStateToAppState(&s)) == lr0
        //     &&& replies@.map(|i, r:CReply| r@) == lr1
        // })
{
    let (states, replies) = CHandleRequestBatchHidden(state, batch);
    (states, replies)
}

} // verus!
