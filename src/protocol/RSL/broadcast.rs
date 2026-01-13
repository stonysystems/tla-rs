use builtin::*;
use builtin_macros::*;
use vstd::prelude::verus;
use vstd::seq::*;
use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::message::*;
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;

verus! {
    pub open spec fn LBroadcastToEveryone(c:LConfiguration, myidx:int, m:RslMessage, sent_packets:Seq<RslPacket>) -> bool
    {
        &&& sent_packets.len() == c.replica_ids.len()
        &&& 0 <= myidx < c.replica_ids.len()
        &&& forall |idx:int| 0 <= idx < sent_packets.len() ==> sent_packets[idx] =~= LPacket{
                                                                dst:c.replica_ids[idx], 
                                                                src:c.replica_ids[myidx], 
                                                                msg:m}
    }

    pub open spec fn BuildLBroadcast(src: AbstractEndPoint, dsts: Seq<AbstractEndPoint>, m: RslMessage) -> (res:Seq<RslPacket>)
    //     (forall |i: int| 0<=dsts.len()<dsts.len() ==> res[i] == LPacket{dst: dsts[i],src:src, msg:m})
        decreases dsts.len()
    {
        if dsts.len() == 0 {Seq::empty()}
        else {
            seq![LPacket{dst: dsts[0],src: src,msg: m}] + BuildLBroadcast(src, dsts.skip(1), m)}
    }
}