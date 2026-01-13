// #![allow(unused_imports)]
// #![allow(unused_attributes)]
use builtin::*;
use builtin_macros::*;
use vstd::map::*;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::pervasive::*;
use vstd::seq::*;

use vstd::{set::*, set_lib::*};

use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::services::RSL::app_state_machine::*;

verus! {
    pub type OperationNumber = int;

    pub struct Ballot {
        pub seqno : int,
        pub proposer_id : int,
    }

    pub struct Request {
        pub client : AbstractEndPoint,
        pub seqno : int,
        pub request : AppMessage,
    }

    pub struct Reply {
        pub client : AbstractEndPoint,
        pub seqno : int,
        pub reply : AppMessage,
    }

    pub type RequestBatch = Seq<Request>;

    pub type ReplyCache = Map<AbstractEndPoint, Reply>;

    pub struct Vote {
        pub max_value_bal : Ballot,
        pub max_val : RequestBatch,
    }

    pub type Votes = Map<OperationNumber, Vote>;

    pub struct LearnerTuple {
        pub received_2b_message_senders:Set<AbstractEndPoint>, 
        pub candidate_learned_value:RequestBatch,
    }

    pub type LearnerState = Map<OperationNumber, LearnerTuple>;

    pub open spec fn BalLt(ba:Ballot, bb:Ballot) -> bool
    {
        ||| ba.seqno < bb.seqno
        ||| (ba.seqno == bb.seqno && ba.proposer_id < bb.proposer_id)
    }

    pub open spec fn BalLeq(ba:Ballot, bb:Ballot) -> bool
    {
        ||| ba.seqno < bb.seqno
        ||| (ba.seqno == bb.seqno && ba.proposer_id <= bb.proposer_id)
    }

    pub proof fn lemma_BalLtMiddle(ba:Ballot, bb:Ballot)
        requires 
            !BalLt(ba, bb),
            ba != bb,
        ensures
            BalLt(bb, ba),
    {

    }

    pub struct ClockReading {
        pub t:int
    }
}