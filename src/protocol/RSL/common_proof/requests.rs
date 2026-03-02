use crate::protocol::RSL::common_proof::assumptions::*;
use crate::protocol::RSL::common_proof::constants::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::election::*;
use crate::protocol::RSL::types::*;
use vstd::prelude::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

use crate::common::collections::maps2::*;
use crate::common::framework::environment_s::LEnvStep;
use crate::common::framework::environment_s::*;
use crate::common::logic::heuristics_i::*;
use crate::common::logic::temporal_s::*;
use crate::common::native::io_s::*;

verus! {

    pub proof fn lemma_RemoveAllSatisfiedRequestsInSequenceProducesSubsequence(
        s_:Seq<Request>,
        s:Seq<Request>,
        r:Request
    )
        requires s_ == RemoveAllSatisfiedRequestsInSequence(s, r)
        ensures  forall |x:Request| s_.contains(x) ==> s.contains(x)
        decreases s.len()
    {
        if s.len() > 0 && !RequestsMatch(s[0], r)
        {
            let s_prev = s.drop_first();
            let s_prev_ = RemoveAllSatisfiedRequestsInSequence(s_prev, r);
            lemma_RemoveAllSatisfiedRequestsInSequenceProducesSubsequence(
                RemoveAllSatisfiedRequestsInSequence(s_prev, r), s_prev, r);
            assert(forall |x:Request| s_prev_.contains(x) ==> s_prev.contains(x));
            assert(forall |x:Request| s_prev.contains(x) ==> s.contains(x));
            assert(forall |x:Request| s_.contains(x) ==> s.contains(x));
        } else if s.len() > 0 && RequestsMatch(s[0], r){
            assert(s_ == RemoveAllSatisfiedRequestsInSequence(s.drop_first(), r));
            assert(s.drop_first().len() == s.len() - 1);
            lemma_RemoveAllSatisfiedRequestsInSequenceProducesSubsequence(s_, s.drop_first(), r);
            assert(forall |x:Request| s_.contains(x) ==> s.drop_first().contains(x));
            assert(forall |x:Request| s_.contains(x) ==> s.contains(x));
        } else {
            assert(forall |x:Request| s_.contains(x) ==> s.contains(x));
        }
    }

    pub proof fn lemma_RemoveExecutedRequestBatchProducesSubsequence(
        s_:Seq<Request>,
        s:Seq<Request>,
        batch:RequestBatch
    )
        requires s_ == RemoveExecutedRequestBatch(s, batch)
        ensures  forall |x:Request| s_.contains(x) ==> s.contains(x)
        decreases batch.len()
    {
        if batch.len() > 0
        {
            let s__ = RemoveAllSatisfiedRequestsInSequence(s, batch[0]);
            lemma_RemoveAllSatisfiedRequestsInSequenceProducesSubsequence(s__, s, batch[0]);
            lemma_RemoveExecutedRequestBatchProducesSubsequence(s_, s__, batch.drop_first());
        }
    }
}
