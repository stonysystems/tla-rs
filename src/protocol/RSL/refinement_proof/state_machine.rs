use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::environment::*;

use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::services::RSL::app_state_machine::*;

verus!{
    pub struct RSLSystemState{
        pub server_addresses:Set<AbstractEndPoint>,
        pub app:AppState,
        pub requests:Set<Request>,
        pub replies:Set<Reply>,
    }

    pub open spec fn RslSystemInit(s:RSLSystemState, server_addresses:Set<AbstractEndPoint>) -> bool
    {
        &&& s.server_addresses == server_addresses
        &&& s.app == AppInitialize()
        &&& s.requests == Set::<Request>::empty()
        &&& s.replies == Set::<Reply>::empty()
    }

    pub open spec fn RslSystemNextServerExecutesRequest(s:RSLSystemState, s_:RSLSystemState, req:Request) -> bool
    {
        && s_.server_addresses == s.server_addresses
        && s_.requests == s.requests + set![req] 
        && s_.app == AppHandleRequest(s.app, req.request).0
        && s_.replies == s.replies + set![Reply{client:req.client, seqno:req.seqno, reply:AppHandleRequest(s.app, req.request).1}]
    }

    pub open spec fn RslStateSequenceReflectsBatchExecution(s:RSLSystemState, s_:RSLSystemState, intermediate_states:Seq<RSLSystemState>,
                                                 batch:Seq<Request>) -> bool 
    {
        &&& intermediate_states.len() == batch.len() + 1
        &&& intermediate_states[0] == s 
        &&& intermediate_states.last() == s_
        &&& forall |i:int| 0 <= i < batch.len() ==> RslSystemNextServerExecutesRequest(intermediate_states[i], intermediate_states[i+1], batch[i])
    }

    pub open spec fn RslSystemNext(s:RSLSystemState, s_:RSLSystemState) -> bool 
    {
        exists |intermediate_states:Seq<RSLSystemState>, batch:Seq<Request>| RslStateSequenceReflectsBatchExecution(s, s_, intermediate_states, batch)
    }

    pub open spec fn RslSystemRefinement(ps:RslState, rs:RSLSystemState) -> bool
    {
        &&& (forall |p:RslPacket| ps.environment.sentPackets.contains(p) && rs.server_addresses.contains(p.src) && p.msg is RslMessageReply
                ==> rs.replies.contains(Reply{client:p.dst, seqno:p.msg->seqno_reply, reply:p.msg->reply}))
        &&& (forall |req:Request| rs.requests.contains(req) ==> exists |p:RslPacket| ps.environment.sentPackets.contains(p) && rs.server_addresses.contains(p.dst) && p.msg is RslMessageRequest
                                                && req == Request{client:p.src, seqno:p.msg->seqno_req, request:p.msg->val})
    }

    pub open spec fn RslSystemBehaviorRefinementCorrect(server_addresses:Set<AbstractEndPoint>, low_level_behavior:Seq<RslState>, high_level_behavior:Seq<RSLSystemState>) -> bool
    {
        &&& high_level_behavior.len() == low_level_behavior.len()
        &&& (forall |i:int| 0 <= i < low_level_behavior.len() ==> RslSystemRefinement(low_level_behavior[i], high_level_behavior[i]))
        &&& high_level_behavior.len() > 0
        &&& RslSystemInit(high_level_behavior[0], server_addresses)
        &&& (forall |i:int| #![trigger high_level_behavior[i]] 0 <= i < high_level_behavior.len()-1 ==> RslSystemNext(high_level_behavior[i], high_level_behavior[i+1]))
    }
}