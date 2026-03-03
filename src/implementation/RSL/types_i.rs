use crate::common::collections::hashsets::clone_hashset;
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::implementation::common::marshalling::*;
use crate::implementation::RSL::appinterface::*;
use std::collections::*;
use vstd::prelude::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

use crate::protocol::RSL::types::*;
use crate::services::RSL::app_state_machine::*;
verus! {
    pub type COperationNumber = u64;

    pub open spec fn AbstractifyCOperationNumberToOperationNumber(s:COperationNumber) -> int
        recommends
            COperationNumberIsAbstractable(s)
    {
        s as int
    }

    pub open spec fn COperationNumberIsAbstractable(s:COperationNumber) -> bool {
        true
    }

    pub open spec fn COperationNumberIsValid(s:COperationNumber) -> bool {
        COperationNumberIsAbstractable(s)
    }

    define_struct_and_derive_marshalable!{
        #[derive(Eq, Clone, Copy, PartialEq, Hash)]
        pub struct CBallot {
            pub seqno : u64,
            pub proposer_id : u64,
        }
    }

    pub fn CBalLt(ba:&CBallot, bb:&CBallot) -> (r:bool)
        requires
            ba.valid(),
            bb.valid(),
        ensures r == BalLt(ba@, bb@)
    {
        ba.seqno < bb.seqno
        || (ba.seqno == bb.seqno && ba.proposer_id < bb.proposer_id)
    }

    pub fn CBalLeq(ba:&CBallot, bb:&CBallot) -> (r:bool)
        requires
            ba.valid(),
            bb.valid(),
        ensures r == BalLeq(ba@, bb@)
    {
        ba.seqno < bb.seqno
        || (ba.seqno == bb.seqno && ba.proposer_id <= bb.proposer_id)
    }

    pub fn CBalEq(ba:&CBallot, bb:&CBallot) -> (r:bool)
        requires
            ba.valid(),
            bb.valid(),
        ensures r == (ba@ == bb@)
    {
        ba.seqno == bb.seqno
        && ba.proposer_id == bb.proposer_id
    }

    impl CBallot {

        pub fn is_equal(&self, other: &CBallot) -> (result: bool)
            ensures
                result == (self@ == other@)
        {
            self.seqno == other.seqno && self.proposer_id == other.proposer_id
        }

        pub fn clone_up_to_view(&self) -> (res: CBallot)
        ensures res@ == self@
        {
            CBallot {
                seqno: self.seqno,
                proposer_id: self.proposer_id,
            }
        }

        pub open spec fn abstractable(self) -> bool
        {
            self.proposer_id < 0xFFFF_FFFF_FFFF_FFFF
        }

        pub open spec fn valid(self) -> bool
        {
            self.abstractable()
        }

        pub open spec fn view(self) -> Ballot
            recommends self.abstractable()
        {
            Ballot{seqno:self.seqno as int, proposer_id:self.proposer_id as int}
        }
    }

    define_struct_and_derive_marshalable!{
        #[derive(Clone, PartialEq, Eq, Hash)]
        pub struct CRequest {
            pub client : EndPoint,
            pub seqno : u64,
            pub request : CAppMessage,
        }
    }

    impl View for CRequest {
        type V = Request;
        open spec fn view(&self) -> Request
        {
            Request{
                client : self.client@,
                seqno : self.seqno as int,
                request : self.request@,
            }
        }
    }

    impl CRequest {

        pub fn clone_up_to_view(&self) -> (res: CRequest)
            ensures
            res@ == self@,
            res==self
        {
            let res = CRequest {
                client: self.client.clone_up_to_view(),
                seqno: self.seqno,
                request: self.request.clone_up_to_view()
            };
            proof {
                // EndPoint::clone_up_to_view ensures res.client@ == self.client@
                // axiom_endpoint_view: e1@ == e2@ ==> e1 == e2, so res.client == self.client
                broadcast use crate::common::native::io_s::axiom_endpoint_view;
                // CAppMessage::clone_up_to_view ensures res.request == *(&self.request)
                // seqno is u64 (Copy): res.seqno == self.seqno
                // All fields equal => res == *self
            }
            res
        }

        pub open spec fn abstractable(self) -> bool {
            &&& self.client.abstractable()
            &&& self.request.abstractable()
        }

        pub open spec fn valid(self) -> bool {
            &&& self.abstractable()
            &&& self.request.valid()
        }

    }

    define_struct_and_derive_marshalable!{
        #[derive(Clone, Eq, PartialEq, Hash)]
        pub struct CReply {
            pub client : EndPoint,
            pub seqno : u64,
            pub reply : CAppMessage,
        }
    }

    impl CReply {

        pub fn clone_up_to_view(&self) -> (res: CReply)
            ensures res@ == self@
        {
            CReply {
                client: self.client.clone_up_to_view(),
                seqno: self.seqno,
                reply: self.reply.clone_up_to_view(),
            }
        }

        pub open spec fn abstractable(self) -> bool {
            &&& self.client.abstractable()
            &&& self.reply.abstractable()
        }

        pub open spec fn valid(self) -> bool {
            &&& self.abstractable()
            &&& self.client.valid_public_key()
            &&& self.reply.valid()
        }

    }

    impl View for CReply{
        type V = Reply;

        open spec fn view(&self) -> Reply
            // recommends self.abstractable()
        {
            Reply{
                client : self.client@,
                seqno : self.seqno as int,
                reply : self.reply@,
            }
        }
    }

    pub type CRequestBatch = Vec<CRequest>;

    pub fn clone_request_batch_up_to_view(batch: &CRequestBatch) -> (res: CRequestBatch)
        ensures
            res@ == batch@,
            forall |i: int| 0 <= i < batch.len() ==> res[i]@ == batch[i]@,
            forall |i: int| 0 <= i < batch.len() ==> res[i].valid() == batch[i].valid(),
    {
        let mut cloned:Vec<CRequest> = Vec::new();
        let mut i = 0;
        while i < batch.len()
            invariant
                0 <= i <= batch.len(),
                cloned.len() == i,
                cloned@ == batch@.subrange(0, i as int),
            decreases batch.len() - i,
        {
            let item = batch[i].clone_up_to_view();
            cloned.push(item);
            i += 1;
            assert(cloned@ == batch@.subrange(0, i as int));
        }
        cloned
    }


    pub open spec fn crequestbatch_is_abstractable(s:&CRequestBatch) -> bool {
        forall |i:int| #![auto] 0 <= i < s.len() ==> s[i].abstractable()
    }

    pub open spec fn crequestbatch_is_valid(s:&CRequestBatch) -> bool {
        &&& crequestbatch_is_abstractable(s)
        &&& (forall |i:int| #![auto] 0 <= i < s.len() ==> s[i].valid())
    }

    pub open spec fn abstractify_crequestbatch(s:&CRequestBatch) -> RequestBatch
        recommends crequestbatch_is_abstractable(s)
    {
        s@.map(|i, r:CRequest| r@)
    }

    pub open spec fn RequestBatchSizeLimit() -> int { 1000 }

    pub type CReplyCache = HashMap<EndPoint, CReply>;

    #[verifier(external_body)]
    pub fn clone_creply_cache_up_to_view(cache: &CReplyCache) -> (res: CReplyCache)
        ensures
            res@ == cache@,
            forall |k| cache@.contains_key(k) ==> res@.contains_key(k),
            forall |k| res@.contains_key(k) ==> cache@.contains_key(k),
            forall |k| res@.contains_key(k) ==> res@[k] == cache@[k]
    {
        let mut cloned:HashMap<EndPoint, CReply> = HashMap::new();

        // Manually collect keys to avoid iterator issues
        let mut keys: Vec<EndPoint> = Vec::new();
        let mut i = 0;

        for k in cache.keys() {
            keys.push(k.clone_up_to_view());
        }

        let mut j = 0;
        while j < keys.len()
            invariant
                0 <= j <= keys.len(),
                forall |k: int| 0 <= k < j ==> cloned.contains_key(&keys[k]) && cloned@[keys[k]] == cache@[keys[k]]
        {
            let key = keys[j].clone_up_to_view();
            let val = cache.get(&key).unwrap();
            cloned.insert(key, val.clone_up_to_view());
            j += 1;
        }

        cloned
    }


    pub open spec fn creplycache_is_abstractable(m:&CReplyCache) -> bool {
        forall |i| #![auto] m@.contains_key(i) ==> i.abstractable() && m@[i].abstractable()
    }

    pub open spec fn creplycache_is_valid(m:&CReplyCache) -> bool {
        &&& creplycache_is_abstractable(m)
        &&& (forall |i| #![auto] m@.contains_key(i) ==> m@[i].valid())
    }

    pub open spec fn abstractify_creplycache(m:&CReplyCache) -> ReplyCache
        recommends creplycache_is_abstractable(m)
    {
        Map::new(
            |ak: AbstractEndPoint| exists |k:EndPoint| m@.contains_key(k) && k@ == ak, // m@.contains_key(k) k@,
            |ak: AbstractEndPoint| {
                let k = choose |k: EndPoint| m@.contains_key(k) && k@ == ak;
                m@[k]@
            }
        )
    }

    define_struct_and_derive_marshalable!{
        #[derive(Clone, Eq, PartialEq, Hash)]
        pub struct CVote {
            pub max_value_bal : CBallot,
            pub max_val : CRequestBatch,
        }
    }

    impl CVote{

        pub fn clone_up_to_view(&self) -> (res: CVote)
        ensures res@ == self@
        {
            CVote {
                max_value_bal: self.max_value_bal.clone_up_to_view(),
                max_val: clone_request_batch_up_to_view(&self.max_val),
            }
        }

        pub open spec fn abstractable(self) -> bool{
            &&& self.max_value_bal.abstractable()
            &&& crequestbatch_is_abstractable(&self.max_val)
        }

        pub open spec fn valid(self) -> bool{
            &&& self.abstractable()
            &&& self.max_value_bal.valid()
            &&& crequestbatch_is_valid(&self.max_val)
        }

        pub open spec fn view(self) -> Vote
            recommends self.abstractable()
        {
            Vote{
                max_value_bal : self.max_value_bal@,
                max_val : abstractify_crequestbatch(&self.max_val),
            }
        }
    }

    pub type CVotes = HashMap<COperationNumber, CVote>;

    #[verifier(external_body)]
    pub fn clone_cvotes_up_to_view(votes: &CVotes) -> (res: CVotes)
        ensures
            res@ == votes@,
            res == votes,
            forall |k| votes@.contains_key(k) ==> res@.contains_key(k),
            forall |k| res@.contains_key(k) ==> votes@.contains_key(k),
            forall |k| res@.contains_key(k) ==> res@.index(k) == votes@.index(k)
    {
        let mut cloned:HashMap<COperationNumber, CVote> = HashMap::new();

        // Avoid borrow issues by collecting keys separately
        let mut keys: Vec<COperationNumber> = Vec::new();
        for &k in votes.keys() {
            keys.push(k);
        }

        let mut i = 0;
        while i < keys.len()
            invariant
                i <= keys.len(),
                forall |j: int| 0 <= j < i ==> {
                    let k = keys[j];
                    cloned.contains_key(&k) && cloned@.index(k) == votes@.index(k)
                }
        {
            let k = keys[i];
            let v = votes.get(&k).unwrap();
            cloned.insert(k, v.clone_up_to_view());
            i += 1;
        }
        cloned
    }


    pub open spec fn cvotes_is_abstractable(m:&CVotes) -> bool {
        forall |i| #![auto] m@.contains_key(i) ==> COperationNumberIsAbstractable(i) && m@[i].abstractable()
    }

    pub open spec fn cvotes_is_valid(m:&CVotes) -> bool {
        &&& cvotes_is_abstractable(m)
        &&& (forall |i| #![auto] m@.contains_key(i) ==> COperationNumberIsValid(i) && m@[i].valid())
    }

    /// Helper lemma to instantiate the cvotes_is_valid quantifier for a specific key.
    /// Verus's #![auto] trigger in cvotes_is_valid doesn't always fire,
    /// so we provide direct access via external_body.
    pub proof fn lemma_cvotes_valid_key(m: &CVotes, k: u64)
    requires
        cvotes_is_valid(m),
        m@.contains_key(k),
    ensures
        m@[k].valid(),
    {
        // cvotes_is_valid(m) includes:
        //   forall |i| #![auto] m@.contains_key(i) ==> COperationNumberIsValid(i) && m@[i].valid()
        // Create trigger terms to instantiate with i = k.
        assert(m@.contains_key(k));
        let ghost _v = m@[k];
        assert(COperationNumberIsValid(k));
    }

    pub open spec fn abstractify_cvotes(m:&CVotes) -> Votes
        recommends cvotes_is_abstractable(m)
    {
        Map::new(
            |ak: int| exists |k: u64| m@.contains_key(k) && k@ == ak,
            |ak: int| {
                let k = choose |k: u64| m@.contains_key(k) && k@ == ak;
                m@[k]@
            }
        )
    }

    pub open spec fn max_votes_len() -> int{1001}

    pub struct CLearnerTuple {
        pub received_2b_message_senders:HashSet<EndPoint>,
        pub candidate_learned_value:CRequestBatch,
    }

    impl Clone for CLearnerTuple {
        #[verifier::external_body]
        fn clone(&self) -> Self {
            CLearnerTuple {
                received_2b_message_senders: self.received_2b_message_senders.clone(),
                candidate_learned_value: self.candidate_learned_value.clone(),
            }
        }
    }


    impl CLearnerTuple{
        pub fn clone_up_to_view(&self) -> (res:CLearnerTuple)
            ensures
                res@ == self@,
                (self.abstractable() ==> res.abstractable()),
        {
            let new_senders = clone_hashset(&self.received_2b_message_senders);
            // clone_hashset ensures: new_senders@ == self.received_2b_message_senders@
            let new_batch = clone_request_batch_up_to_view(&self.candidate_learned_value);
            // clone_request_batch_up_to_view ensures: new_batch@ == self.candidate_learned_value@

            CLearnerTuple{
                received_2b_message_senders: new_senders,
                candidate_learned_value: new_batch,
            }
        }

        pub open spec fn abstractable(self) -> bool{
            &&& (forall |p| self.received_2b_message_senders@.contains(p) ==> p.abstractable())
            &&& crequestbatch_is_abstractable(&self.candidate_learned_value)
        }

        pub open spec fn valid(self) -> bool{
            &&& self.abstractable()
            // &&& (forall |p| self.received_2b_message_senders@.contains(p) ==> p.valid())
            &&& crequestbatch_is_valid(&self.candidate_learned_value)
        }

        pub open spec fn view(self) -> LearnerTuple
        {
            LearnerTuple{
                received_2b_message_senders:self.received_2b_message_senders@.map(|i:EndPoint| i@),
                candidate_learned_value:abstractify_crequestbatch(&self.candidate_learned_value),
            }
        }
    }

    impl View for CLearnerTuple{
        type V = LearnerTuple;

        open spec fn view(&self) -> LearnerTuple
        {
            LearnerTuple{
                received_2b_message_senders:self.received_2b_message_senders@.map(|i:EndPoint| i@),
                candidate_learned_value:abstractify_crequestbatch(&self.candidate_learned_value),
            }
        }
    }

    pub type CLearnerState = HashMap<COperationNumber, CLearnerTuple>;

    pub open spec fn clearnerstate_is_abstractable(m:CLearnerState) -> bool {
        forall |i| #![auto] m@.contains_key(i) ==> COperationNumberIsAbstractable(i) && m@[i].abstractable()
    }

    pub open spec fn clearnerstate_is_valid(m:CLearnerState) -> bool {
        &&& clearnerstate_is_abstractable(m)
        &&& (forall |i| #![auto] m@.contains_key(i) ==> COperationNumberIsValid(i) && m@[i].valid())
    }

    pub open spec fn abstractify_clearnerstate(m:CLearnerState) -> LearnerState
        recommends clearnerstate_is_abstractable(m)
    {
        Map::new(
            |ak: int| exists |k: u64| m@.contains_key(k) && k@ == ak,
            |ak: int| {
                let k = choose |k: u64| m@.contains_key(k) && k@ == ak;
                m@[k]@
            }
        )
    }

    pub fn clone_vec_coperationnumber(v: &Vec<COperationNumber>) -> (res: Vec<COperationNumber>)
        ensures
            res@ == v@,
            res.len() == v.len(),
    {
        let mut result:Vec<COperationNumber> = Vec::new();
        let mut i = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                result.len() == i,
                result@ == v@.subrange(0, i as int),
            decreases v.len() - i,
        {
            let item = v[i];
            result.push(item);
            i += 1;
            assert(result@ == v@.subrange(0, i as int));
        }

        result
    }

}
