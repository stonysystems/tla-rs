use crate::common::collections::seq_is_unique_v::*;
use crate::common::collections::sets::*;
use crate::common::collections::{hashsets::*, vecs::*};
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::implementation::common::{generic_refinement::*, upper_bound::*, upper_bound_i::*};
use crate::implementation::RSL::{cconfiguration::*, cconstants::*, cmessage::*, types_i::*};
use crate::protocol::common::upper_bound::*;
use crate::protocol::RSL::{
    configuration::*, constants::*, election::*, environment::*, executor::*, message::*, types::*,
};
use std::collections::hash_set::Iter;
use std::collections::HashSet;
use std::collections::*;
use std::result;
use vstd::hash_set::HashSetWithView;
use vstd::invariant;
use vstd::prelude::*;
use vstd::std_specs::hash::*;
use vstd::{hash_map::*, map::*, prelude::*, seq::*, set::*};
// Generated wrappers live in `crate::generated::RSL::election_gen`.
// This module owns concrete election-side type infrastructure:
// CElectionState/COutstandingOperation plus clone/hashset helper functions.

verus! {
pub struct CElectionState {
    pub constants: CReplicaConstants,
    pub current_view: CBallot,
    pub current_view_suspectors: HashSet<u64>,
    pub epoch_end_time: u64,
    pub epoch_length: u64,
    pub requests_received_this_epoch: Vec<CRequest>,
    pub requests_received_prev_epochs: Vec<CRequest>,
    pub cur_req_set: HashSet<CRequestHeader>,
    pub prev_req_set: HashSet<CRequestHeader>,
}

impl CElectionState {
    pub open spec fn abstractable(self) -> bool {
        &&& self.constants.abstractable()
        &&& self.current_view.abstractable()
        &&& (forall |i:int| 0 <= i < self.requests_received_this_epoch@.len() ==> self.requests_received_this_epoch@[i].abstractable())
        &&& (forall |i:int| 0 <= i < self.requests_received_prev_epochs@.len() ==> self.requests_received_prev_epochs@[i].abstractable())
    }

    pub open spec fn valid(self) -> bool {
        &&& self.abstractable()
        &&& self.constants.valid()
        &&& self.current_view.valid()
        &&& (forall |i:int| 0 <= i < self.requests_received_this_epoch@.len() ==> self.requests_received_this_epoch@[i].valid())
        &&& (forall |i:int| 0 <= i < self.requests_received_prev_epochs@.len() ==> self.requests_received_prev_epochs@[i].valid())
    }

    pub open spec fn view(self) -> ElectionState
        recommends self.abstractable()
    {
        ElectionState{
            constants: self.constants@,
            current_view: self.current_view@,
            current_view_suspectors: self.current_view_suspectors@.map(|x:u64| x as int),
            epoch_end_time: self.epoch_end_time as int,
            epoch_length: self.epoch_length as int,
            requests_received_this_epoch: self.requests_received_this_epoch@.map(|i, r:CRequest| r@),
            requests_received_prev_epochs: self.requests_received_prev_epochs@.map(|i, r:CRequest| r@)
        }
    }
}

impl View for CElectionState {
    type V = ElectionState;

    open spec fn view(&self) -> ElectionState {
        ElectionState {
            constants: self.constants@,
            current_view: self.current_view@,
            current_view_suspectors: self.current_view_suspectors@.map(|u:u64| u as int),
            epoch_end_time: self.epoch_end_time as int,
            epoch_length: self.epoch_length as int,
            requests_received_this_epoch: self.requests_received_this_epoch@.map(|i, r:CRequest| r.view()),
            requests_received_prev_epochs: self.requests_received_prev_epochs@.map(|i, r:CRequest| r.view()),
        }
    }
}

#[derive(Clone)]
pub enum COutstandingOperation {
    COutstandingOpKnown {
        v: CRequestBatch,
        bal: CBallot,
    },
    COutstandingOpUnknown {
    },
}

impl COutstandingOperation {
    pub open spec fn valid(&self) -> bool {
        match self {
            COutstandingOperation::COutstandingOpKnown{v, bal} => {
                self.abstractable()
                    && crequestbatch_is_valid(v)
                    && bal.valid()
            }
            COutstandingOperation::COutstandingOpUnknown{} => self.abstractable()
        }
    }

    pub open spec fn abstractable(&self) -> bool {
        match self {
            COutstandingOperation::COutstandingOpKnown{v, bal} => {
                crequestbatch_is_abstractable(v) && bal.abstractable()
            }
            COutstandingOperation::COutstandingOpUnknown{} => true
        }
    }

    pub open spec fn view(self) -> OutstandingOperation
        recommends
            self.abstractable()
    {
        match self {
            COutstandingOperation::COutstandingOpKnown{v,bal} => {
                OutstandingOperation::OutstandingOpKnown{
                    v: abstractify_crequestbatch(&v),
                    bal: bal@,
                }
            }
            COutstandingOperation::COutstandingOpUnknown{} => {
                OutstandingOperation::OutstandingOpUnknown{}
            }
        }
    }
}

impl View for COutstandingOperation {
    type V = OutstandingOperation;

    open spec fn view(&self) -> OutstandingOperation {
        match self {
            COutstandingOperation::COutstandingOpKnown{v, bal} => OutstandingOperation::OutstandingOpKnown {
                v: abstractify_crequestbatch(v),
                bal: bal@,
            },
            COutstandingOperation::COutstandingOpUnknown{} => OutstandingOperation::OutstandingOpUnknown{},
        }
    }
}

// CElectionState contains HashSet<u64> and HashSet<CRequestHeader>, so Clone can't be derived by Verus.
impl Clone for CElectionState {
    #[verifier(external_body)]
    fn clone(&self) -> (result: Self)
    ensures
        result@ == self@,
        result.valid() == self.valid(),
    {
        CElectionState {
            constants: self.constants.clone(),
            current_view: self.current_view,
            current_view_suspectors: self.current_view_suspectors.clone(),
            epoch_end_time: self.epoch_end_time,
            epoch_length: self.epoch_length,
            requests_received_this_epoch: self.requests_received_this_epoch.clone(),
            requests_received_prev_epochs: self.requests_received_prev_epochs.clone(),
            cur_req_set: self.cur_req_set.clone(),
            prev_req_set: self.prev_req_set.clone(),
        }
    }
}

#[derive(Clone, Eq, Hash)]
pub struct CRequestHeader {
    pub client : EndPoint,
    pub seqno : u64,
}

impl PartialEq for CRequestHeader {
    #[verifier(external_body)]
    fn eq(&self, other: &Self) -> bool {
        self.client.eq(&other.client) && self.seqno == other.seqno
    }
}

impl CElectionState
{

    #[verifier(external_body)]
    pub fn clone_up_to_view(&self) -> (result:Self)
        ensures
            self==result,
            self@ == result@,
    {
        CElectionState {
            constants: self.constants.clone_up_to_view(),
            current_view: self.current_view.clone_up_to_view(),
            current_view_suspectors: clone_hashset_u64(&self.current_view_suspectors),
            epoch_end_time: self.epoch_end_time,
            epoch_length: self.epoch_length,
            requests_received_this_epoch: clone_request_batch_up_to_view(&self.requests_received_this_epoch),
            requests_received_prev_epochs: clone_request_batch_up_to_view(&self.requests_received_prev_epochs),
            cur_req_set : self.cur_req_set.clone(),
            prev_req_set : self.prev_req_set.clone(),
        }
    }

    pub fn CBoundRequestSequence(s:&Vec<CRequest>, lengthBound: u64) -> (rc: Vec<CRequest>)
        requires
            s@.len() < 0x1_0000_0000_0000_0000,
            forall |i: int| 0 <= i < s@.len() ==> s@[i].valid(),
        ensures
            forall |i: int| 0 <= i < rc@.len() ==> rc@[i].valid(),
            rc@.map(|i, r: CRequest| r@) == BoundRequestSequence(s@.map(|i, r: CRequest| r@), UpperBound::UpperBoundFinite{n: lengthBound as int}),
    {
        let s_len = s.len() as u64;
        assert(s_len == s@.len() as u64);
        if 0 <= lengthBound && lengthBound < s_len {
            let rc = truncate_vec(&s, 0, lengthBound as usize);
            assert(rc@.map(|i, r: CRequest| r@) == BoundRequestSequence(s@.map(|i, r: CRequest| r@), UpperBound::UpperBoundFinite{n: lengthBound as int}));
            rc
        } else {
            let rc = clone_vec_crequest(s);
            assert(rc@.map(|i, r: CRequest| r@) == BoundRequestSequence(s@.map(|i, r: CRequest| r@), UpperBound::UpperBoundFinite{n: lengthBound as int}));
            rc
        }
    }

}

    #[verifier(external_body)]
    pub fn clone_hashset_u64(s: &HashSet<u64>) -> (res: HashSet<u64>)
    ensures
        res == s,
        res@ == s@
    {
        let mut cloned = HashSet::new();
        for &val in s {
            cloned.insert(val);
        }
        cloned
    }

    #[verifier(external_body)]
    pub fn clone_vec_crequest(v: &Vec<CRequest>) -> (res: Vec<CRequest>)
        requires
            forall |i: int| 0 <= i < v.len() ==> v[i].valid()
        ensures
            res==v,
            res@ == v@,
            res.len() == v.len(),
            forall |i: int| 0 <= i < res.len() ==> res[i].valid(),
            forall |i: int| 0 <= i < res.len() ==> res@[i] == v@[i]
    {
        let mut result:Vec<CRequest> = Vec::new();
        let mut i = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                result.len() == i,
                forall |j: int| 0 <= j < i ==> result[j].valid(),
                result@ == v@.subrange(0, i as int),
                forall |j: int| 0 <= j < i ==> result@[j] == v@[j]
        {
            let item = v[i].clone_up_to_view();
            result.push(item);
            i += 1;
            assert(result@ == v@.subrange(0, i as int));
        }

        result
    }

}
