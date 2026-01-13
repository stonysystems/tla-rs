use builtin::*;
use builtin_macros::*;
use vstd::*;
use vstd::seq::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::message::*;
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;

verus! {
    pub type RslEnvironment = LEnvironment<AbstractEndPoint, RslMessage>;
    pub type RslPacket = LPacket<AbstractEndPoint, RslMessage>;
    pub type RslIo = LIoOp<AbstractEndPoint, RslMessage>;

    pub open spec fn ConcatenatePaxosIos(s:Seq<Seq<RslIo>>) -> Seq<RslIo>
        decreases s.len()
    {
        if s.len() == 0 {
            Seq::empty()
        } else {
            s[0] + ConcatenatePaxosIos(s.subrange(1, s.len() as int))
        }
    }
}