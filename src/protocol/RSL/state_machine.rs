use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
// use crate::protocol::RSL::configuration::*;
// use crate::protocol::RSL::constants::*;
// use crate::protocol::RSL::broadcast::*;
// use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::message::*;
use crate::services::RSL::app_state_machine::*;

verus! {
    pub open spec fn HandleRequest(state:AppState, request:Request) -> (AppState, Reply)
    {
        let (new_state, reply) = AppHandleRequest(state, request.request);
        (new_state, Reply{client:request.client, seqno:request.seqno, reply:reply})
    }

    pub open spec fn HandleRequestBatchHidden(state:AppState, batch:RequestBatch) -> (rc:(Seq<AppState>, Seq<Reply>))
        // ensures 
        //     rc.0.len() == batch.len() + 1,
        //     rc.1.len() == batch.len(),
        //     forall |i:int| 0 <= i < batch.len() ==> rc.1[i] is Reply,
        decreases batch.len()
    {
        if batch.len() == 0 {
            (seq![state], Seq::empty())
        } else {
            let (restStates, restReplies) = HandleRequestBatchHidden(state, batch.drop_last());
            let (new_state, reply) = AppHandleRequest(restStates.last(), batch.last().request);
            (restStates+seq![new_state], restReplies+seq![Reply{client:batch.last().client, seqno:batch.last().seqno, reply}]) 
        }
    }

    // pub proof fn lemma_HandleRequestBatchHidden(state:AppState, batch:RequestBatch)
    //     ensures 
    //         HandleRequestBatchHidden(state, batch).0.len() == batch.len() + 1,
    //         HandleRequestBatchHidden(state, batch).1.len() == batch.len(),
    //         forall |i: int| 0 <= i < batch.len() ==> HandleRequestBatchHidden(state, batch).1.index(i) is Reply
    // {

    // }

    
    pub proof fn lemma_HandleRequestBatchHidden(
        state: AppState,
        batch: RequestBatch,
        states: Seq<AppState>,
        replies: Seq<Reply>
    )
        requires
            (states, replies) == HandleRequestBatchHidden(state, batch),
        ensures
            states[0] == state,
            states.len() == batch.len() + 1,
            replies.len() == batch.len(),
            forall |i: int| 0 <= i < batch.len() ==> {
                replies[i] is Reply &&
                (states[i + 1], replies[i].reply) == AppHandleRequest(states[i], batch[i].request) &&
                replies[i].client == batch[i].client &&
                replies[i].seqno == batch[i].seqno
            },
        decreases batch.len(),
    {
        // reveal(HandleRequestBatchHidden);
        if batch.len() == 0 {
            assert(states.len() == batch.len() + 1);
            assert(replies.len() == batch.len());
            assert(forall |i: int| 0 <= i < batch.len() ==> (states[i + 1], replies[i].reply) == AppHandleRequest(states[i], batch[i].request));
        } else {
            let rest_batch = HandleRequestBatchHidden(state, batch.subrange(0, batch.len() as int - 1));
            let rest_states = rest_batch.0;
            let ahr_result = AppHandleRequest(rest_states[rest_states.len() as int - 1], batch[batch.len() as int - 1].request);
            lemma_HandleRequestBatchHidden(state, batch.subrange(0, batch.len() as int - 1), rest_states, rest_batch.1);
            assert(replies[batch.len() as int - 1].reply == ahr_result.1);
        }
    }

    pub proof fn lemma_HandleRequestBatchTriggerHappy(
        state: AppState,
        batch: RequestBatch,
        states: Seq<AppState>,
        replies: Seq<Reply>
    )
        requires
            (states, replies) == HandleRequestBatch(state, batch),
        ensures
            states[0] == state,
            states.len() == batch.len() + 1,
            replies.len() == batch.len(),
            forall |i: int| 0 <= i < batch.len() ==> {
                replies[i] is Reply &&
                (states[i + 1], replies[i].reply) == AppHandleRequest(states[i], batch[i].request) &&
                replies[i].client == batch[i].client &&
                replies[i].seqno == batch[i].seqno
            },
    {
        assert(states == HandleRequestBatchHidden(state, batch).0);  // OBSERVE
        assert(replies == HandleRequestBatchHidden(state, batch).1); // OBSERVE
        assert((states, replies) == HandleRequestBatchHidden(state, batch));
        lemma_HandleRequestBatchHidden(state, batch, states, replies);
    }

    pub open spec fn HandleRequestBatch(state:AppState, batch:RequestBatch) -> (rc:(Seq<AppState>, Seq<Reply>))
        // ensures
        //     rc.0[0] == state,
        //     rc.0.len() == batch.len() + 1,
        //     rc.1.len() == batch.len(),
        //     forall |i:int| 0 <= i < batch.len() ==> rc.1[i] is Reply
        //                                             && (rc.0[i+1], rc.1[i]) == AppHandleRequest(rc.0[i], batch[i].request)
        //                                             && rc.1[i].client == batch[i].client
        //                                             && rc.1[i].seqno == batch[i].seqno
    {
        let (states, replies) = HandleRequestBatchHidden(state, batch);
        (states, replies)
    }

    // pub proof fn lemma_HandleRequestBatch(state:AppState, batch:RequestBatch)
    //     ensures
    //         HandleRequestBatch(state, batch).0[0] == state,
    //         HandleRequestBatch(state, batch).0.len() == batch.len() + 1,
    //         HandleRequestBatch(state, batch).1.len() == batch.len(),
    //         forall |i: int| 0 <= i < batch.len() ==> HandleRequestBatch(state, batch).1.index(i) is Reply
    //             && (HandleRequestBatch(state, batch).0[i+1], HandleRequestBatch(state, batch).1[i].reply)
    //             == AppHandleRequest(HandleRequestBatch(state, batch).0[i], batch.index(i).request)
    //             && HandleRequestBatch(state, batch).1[i].client == batch.index(i).client
    //             && HandleRequestBatch(state, batch).1[i].seqno == batch.index(i).seqno
    // {

    // }W
}