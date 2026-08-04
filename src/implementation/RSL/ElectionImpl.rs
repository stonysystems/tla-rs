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
use vstd::std_specs::cmp::PartialEqSpecImpl;
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
        &&& (forall |i:int| #![trigger self.requests_received_this_epoch@[i]] 0 <= i < self.requests_received_this_epoch@.len() ==> self.requests_received_this_epoch@[i].abstractable())
        &&& (forall |i:int| #![trigger self.requests_received_prev_epochs@[i]] 0 <= i < self.requests_received_prev_epochs@.len() ==> self.requests_received_prev_epochs@[i].abstractable())
    }

    pub open spec fn valid(self) -> bool {
        &&& self.abstractable()
        &&& self.constants.valid()
        &&& self.current_view.valid()
        &&& (forall |i:int| #![trigger self.requests_received_this_epoch@[i]] 0 <= i < self.requests_received_this_epoch@.len() ==> self.requests_received_this_epoch@[i].valid())
        &&& (forall |i:int| #![trigger self.requests_received_prev_epochs@[i]] 0 <= i < self.requests_received_prev_epochs@.len() ==> self.requests_received_prev_epochs@[i].valid())
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
// Delegation to clone_up_to_view() which uses verified clone helpers (clone_hashset_u64, clone_hashset,
// clone_request_batch_up_to_view) instead of raw HashSet::clone().
impl Clone for CElectionState {
    fn clone(&self) -> (result: Self)
    ensures
        result@ == self@,
        result.valid() == self.valid(),
    {
        self.clone_up_to_view()
    }
}

#[derive(Clone, Eq, Hash)]
pub struct CRequestHeader {
    pub client : EndPoint,
    pub seqno : u64,
}

impl PartialEqSpecImpl for CRequestHeader {
    open spec fn obeys_eq_spec() -> bool {
        true
    }

    open spec fn eq_spec(&self, other: &CRequestHeader) -> bool {
        self.client@ == other.client@ && self.seqno == other.seqno
    }
}

impl PartialEq for CRequestHeader {
    fn eq(&self, other: &Self) -> bool {
        self.client.eq(&other.client) && self.seqno == other.seqno
    }
}

impl CElectionState
{

    pub fn clone_up_to_view(&self) -> (result:Self)
        ensures
            result@ == self@,
            result.valid() == self.valid(),
    {
        let constants_clone = self.constants.clone();
        let suspectors_clone = clone_hashset_u64(&self.current_view_suspectors);
        let this_epoch_clone = clone_request_batch_up_to_view(&self.requests_received_this_epoch);
        let prev_epochs_clone = clone_request_batch_up_to_view(&self.requests_received_prev_epochs);
        let cur_set_clone = clone_hashset(&self.cur_req_set);
        let prev_set_clone = clone_hashset(&self.prev_req_set);
        CElectionState {
            constants: constants_clone,
            current_view: self.current_view,
            current_view_suspectors: suspectors_clone,
            epoch_end_time: self.epoch_end_time,
            epoch_length: self.epoch_length,
            requests_received_this_epoch: this_epoch_clone,
            requests_received_prev_epochs: prev_epochs_clone,
            cur_req_set: cur_set_clone,
            prev_req_set: prev_set_clone,
        }
    }

    pub fn CBoundRequestSequence(s:&Vec<CRequest>, lengthBound: u64) -> (rc: Vec<CRequest>)
        requires
            s@.len() < 0x1_0000_0000_0000_0000,
            forall |i: int| #![trigger s@[i]] 0 <= i < s@.len() ==> s@[i].valid(),
        ensures
            forall |i: int| #![trigger rc@[i]] 0 <= i < rc@.len() ==> rc@[i].valid(),
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

    pub fn clone_vec_crequest(v: &Vec<CRequest>) -> (res: Vec<CRequest>)
        requires
            forall |i: int| #![trigger v[i]] 0 <= i < v.len() ==> v[i].valid()
        ensures
            res@ == v@,
            res.len() == v.len(),
            forall |i: int| #![trigger res[i]] 0 <= i < res.len() ==> res[i].valid(),
            forall |i: int| 0 <= i < res.len() ==> res@[i] == v@[i]
    {
        let mut result:Vec<CRequest> = Vec::new();
        let mut i = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                result.len() == i,
                forall |j: int| #![trigger v[j]] 0 <= j < v.len() ==> v[j].valid(),
                forall |j: int| #![trigger result[j]] 0 <= j < i ==> result[j].valid(),
                result@ == v@.subrange(0, i as int),
                forall |j: int| 0 <= j < i ==> result@[j] == v@[j]
            decreases v.len() - i,
        {
            let item = v[i].clone_up_to_view();
            result.push(item);
            i += 1;
            assert(result@ == v@.subrange(0, i as int));
        }

        result
    }

}
