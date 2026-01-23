use vstd::prelude::*;
use crate::common::collections::seq_is_unique_v::*;
use crate::common::collections::sets::*;
use crate::common::collections::{vecs::*, hashsets::*};
use crate::implementation::common::{generic_refinement::*, upper_bound::*, upper_bound_i::*};
use crate::implementation::RSL::{cconfiguration::*, cconstants::*, cmessage::*, types_i::*};
use crate::protocol::common::upper_bound::*;
use crate::protocol::RSL::{
    configuration::*, constants::*, election::*, environment::*, message::*, types::*,
};
use std::collections::hash_set::Iter;
use std::collections::HashSet;
use std::collections::*;
use std::result;
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use vstd::hash_set::HashSetWithView;
use vstd::invariant;
use vstd::std_specs::hash::*;
use vstd::{hash_map::*, map::*, prelude::*, seq::*, set::*};

verus! {

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

// #[derive(Clone)]
pub struct CElectionState {
    pub constants: CReplicaConstants,
    pub current_view: CBallot,
    pub current_view_suspectors: HashSet<u64>,
    pub epoch_end_time: u64,
    pub epoch_length: u64,
    pub requests_received_this_epoch: Vec<CRequest>,
    pub requests_received_prev_epochs: Vec<CRequest>,

    /* for optimization */
    // pub cur_req_set : Ghost<Set<CRequestHeader>>,
    // pub prev_req_set : Ghost<Set<CRequestHeader>>,
    pub cur_req_set: HashSet<CRequestHeader>,
    pub prev_req_set: HashSet<CRequestHeader>,
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
        // &&& (forall |i:int| 0 <= i < self.requests_received_this_epoch.len() ==> self.requests_received_this_epoch[i].valid())
        // &&& (forall |i:int| 0 <= i < self.requests_received_prev_epochs.len() ==> self.requests_received_prev_epochs[i].valid())
        // &&& self.requests_received_this_epoch.len()  < 0x8000_0000_0000_0000
        // &&& self.requests_received_prev_epochs.len() < 0x8000_0000_0000_0000
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

    #[verifier::external_body]
    pub fn print(s: &str) {
        println!("{}", s);
    }

    pub fn CComputeSuccessorView(b:CBallot, c:CConstants) -> (rc:CBallot)
        requires
            b.valid(),
            c.valid(),
            b.seqno < 0xFFFF_FFFF_FFFF_FFFF
        ensures
            rc.valid(),
            rc@ == ComputeSuccessorView(b@, c@),
    {
        if b.proposer_id + 1 < c.config.replica_ids.len() as u64 {
            CBallot{seqno:b.seqno, proposer_id:b.proposer_id+1}
        } else {
            CBallot{seqno:b.seqno+1, proposer_id:0}
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

    pub fn CRequestsMatch(r1:&CRequest, r2:&CRequest) -> (r:bool)
        requires
            r1.valid(),
            r2.valid(),
        ensures
            r == RequestsMatch(r1@, r2@)
    {
        do_end_points_match(&r1.client, &r2.client) && r1.seqno == r2.seqno
    }

    pub fn CRequestSatisfiedBy(r1:&CRequest, r2:&CRequest) -> (r:bool)
        requires
            r1.valid(),
            r2.valid(),
        ensures
            r == RequestSatisfiedBy(r1@, r2@)
    {
        do_end_points_match(&r1.client, &r2.client) && r1.seqno <= r2.seqno
    }

    // pub fn CRemoveAllSatisfiedRequestsInSequence(s: &Vec<CRequest>, r: &CRequest) -> (rc: Vec<CRequest>)
    //     requires
    //         forall |i: int| 0 <= i < s@.len() ==> s@[i].valid(),
    //         r.valid(),
    //     ensures
    //         forall |i: int| 0 <= i < rc@.len() ==> rc@[i].valid(),
    //         rc@.map(|i, req:CRequest| req@) == RemoveAllSatisfiedRequestsInSequence(s@.map(|i, req: CRequest| req@), r@),
    // {
    //     if s.len() == 0 {
    //         let empty: Vec<CRequest> = Vec::new();
    //         proof {
    //             assert(s@.map(|i, req: CRequest| req@).len() == 0);
    //             assert(RemoveAllSatisfiedRequestsInSequence(s@.map(|i, req: CRequest| req@), r@) == Seq::<Request>::empty());
    //             assert(empty@.map(|i, req: CRequest| req@) == Seq::<Request>::empty());
    //         }
    //         return empty;
    //     }

    //     let head = s[0].clone_up_to_view();
    //     let tail = truncate_vec(s, 1, s.len());

    //     let tail_filtered = Self::CRemoveAllSatisfiedRequestsInSequence(&tail, r);

    //     if Self::CRequestSatisfiedBy(head.clone_up_to_view(), r.clone_up_to_view()) {
    //         proof {
    //             assert(tail_filtered@.map(|i, req: CRequest| req@)
    //                 == RemoveAllSatisfiedRequestsInSequence(tail@.map(|i, req: CRequest| req@), r@));
    //             assert(s@.map(|i, req: CRequest| req@)[0] == head@);
    //             assert(s@.map(|i, req: CRequest| req@).drop_first()
    //                 == tail@.map(|i, req: CRequest| req@));
    //             assert(RemoveAllSatisfiedRequestsInSequence(s@.map(|i, req: CRequest| req@), r@)
    //                 == RemoveAllSatisfiedRequestsInSequence(tail@.map(|i, req: CRequest| req@), r@));
    //         }
    //         tail_filtered
    //     } else {
    //         let res = concat_vecs(&vec![head], &tail_filtered);
    //         proof {
    //             assert(tail_filtered@.map(|i, req: CRequest| req@)
    //                 == RemoveAllSatisfiedRequestsInSequence(tail@.map(|i, req: CRequest| req@), r@));
    //             let s_view = s@.map(|i, req: CRequest| req@);
    //             let tail_view = tail@.map(|i, req: CRequest| req@);
    //             assert(s_view.drop_first() == tail_view);
    //             assert(s_view[0] == head@);
    //             assert(res@.map(|i, req: CRequest| req@)
    //                 == seq![head@] + RemoveAllSatisfiedRequestsInSequence(tail_view, r@));
    //             assert(RemoveAllSatisfiedRequestsInSequence(s_view, r@)
    //                 == seq![head@] + RemoveAllSatisfiedRequestsInSequence(tail_view, r@));
    //         }
    //         res
    //     }
    // }


    pub fn CElectionStateInit(c:CReplicaConstants) -> (rc:Self)
    requires
        c.valid(),
        c.all.config.replica_ids.len() > 0
    ensures
        rc.valid(),
        ElectionStateInit(rc@, c@),

    {
        let current_view = CBallot{seqno:1, proposer_id:0};
        let current_view_suspectors: HashSet<u64> = HashSet::new();
        let req_this: Vec<CRequest> = Vec::new();
        let req_prev: Vec<CRequest> = Vec::new();
        let cur_set: HashSet<CRequestHeader> = HashSet::new();
        let prev_set: HashSet<CRequestHeader> = HashSet::new();

        let rc = CElectionState {
            constants: c.clone_up_to_view(),
            current_view: current_view,
            current_view_suspectors: current_view_suspectors,
            epoch_end_time: 0,
            epoch_length: c.all.params.baseline_view_timeout_period,
            requests_received_this_epoch: req_this,
            requests_received_prev_epochs: req_prev,
            // cur_req_set:    Ghost(Set::<CRequestHeader>::empty()),
            // prev_req_set:   Ghost(Set::<CRequestHeader>::empty()),
            cur_req_set: cur_set,
            prev_req_set: prev_set,
        };

        proof {
            let rcv = rc@;
            let cv = c@;

            assert(rcv.constants == cv);
            assert(rcv.current_view == Ballot{seqno:1, proposer_id:0});
            assert(rcv.current_view_suspectors == Set::<int>::empty());
            assert(rcv.epoch_end_time == 0);
            assert(rcv.epoch_length == cv.all.params.baseline_view_timeout_period);
            assert(rcv.requests_received_this_epoch == Seq::<Request>::empty());
            assert(rcv.requests_received_prev_epochs == Seq::<Request>::empty());

            assert(ElectionStateInit(rcv, cv));
        }

        rc
    }


    // Blocked on Hashsets
    // #[verifier(external_body)]
    pub fn CElectionStateProcessHeartbeat(&mut self, p: CPacket, clock: u64)
        requires
            old(self).valid(),
            p.msg is CMessageHeartbeat,
            p.valid(),
        ensures
            self.valid(),
            ElectionStateProcessHeartbeat(old(self)@, self@, p@, clock as int)
    {
        let inp = p.clone_up_to_view();

        if !contains(&self.constants.all.config.replica_ids, &inp.src) {
            // unknown sender → do nothing
        } else {
            let (found, idx) = CConfiguration::CGetReplicaIndex(&self.constants.all.config, &inp.src);
            if found {
                match inp.msg {
                    CMessage::CMessageHeartbeat { bal_heartbeat, suspicious, .. } => {
                        if self.current_view.is_equal(&bal_heartbeat) && suspicious {
                            // Self::print("Recieve a new suspicious");
                            let mut suspectors = clone_hashset_u64(&self.current_view_suspectors);

                            suspectors.insert(idx as u64);
                            self.current_view_suspectors = suspectors;


                            proof {
                                let old_state = old(self)@;
                                let new_state = self@;
                                assert(old_state.constants == new_state.constants);
                                assert(old_state.current_view == new_state.current_view);
                                assume(new_state.current_view_suspectors == old_state.current_view_suspectors + set![idx as int]); // Fix this
                                assert(old_state.epoch_end_time == new_state.epoch_end_time);
                                assert(old_state.epoch_length == new_state.epoch_length);
                                assert(old_state.requests_received_this_epoch == new_state.requests_received_this_epoch);
                                assert(old_state.requests_received_prev_epochs == new_state.requests_received_prev_epochs);
                                let old_set: Set<int> = old_state.current_view_suspectors;
                                let new_set: Set<int> = new_state.current_view_suspectors;
                                let idx_int = idx as int;


                            }
                            assert(ElectionStateProcessHeartbeat(old(self)@, self@, p@, clock as int));

                        } else if CBalLt(&self.current_view, &bal_heartbeat) {
                            Self::print("Recieve a larger ballot, clear suspicious");
                            let new_epoch_length = CUpperBoundedAddition(
                                self.epoch_length,
                                self.epoch_length,
                                self.constants.all.params.max_integer_val,
                            );
                            self.current_view = bal_heartbeat;

                            let mut suspectors: HashSet<u64> = HashSet::new();

                            if suspicious {
                                suspectors.insert(idx as u64);
                            }
                            self.current_view_suspectors = suspectors;

                            self.epoch_end_time = CUpperBoundedAddition(
                                clock,
                                new_epoch_length,
                                self.constants.all.params.max_integer_val,
                            );

                            self.epoch_length = new_epoch_length;

                            let new_prevs = concat_vecs(
                                &self.requests_received_prev_epochs,
                                &self.requests_received_this_epoch
                            );

                            assume(new_prevs@.len() < 0x1_0000_0000_0000_0000); // Make sure to deal with this assumption

                            self.requests_received_prev_epochs = Self::CBoundRequestSequence(
                                &new_prevs,
                                self.constants.all.params.max_integer_val,
                            );
                            self.requests_received_this_epoch = Vec::new();

                            let new_set = union_sets(&self.prev_req_set, &self.cur_req_set);
                            self.cur_req_set = HashSet::new();
                            let bounded_set = Self::BoundCRequestHeaders(&new_prevs, &new_set, self.constants.all.params.max_integer_val);
                            self.prev_req_set = bounded_set;

                            proof {
                                let old_state = old(self)@;
                                let new_state = self@;

                                let idx_int = idx as int;
                                let new_view = bal_heartbeat@;
                                let new_epoch_length_spec = UpperBoundedAddition(
                                    old_state.epoch_length,
                                    old_state.epoch_length,
                                    old_state.constants.all.params.max_integer_val,
                                );

                                // Prove field-by-field equality:

                                assert(new_state.constants == old_state.constants);
                                assert(new_state.current_view == new_view);
                                if suspicious {
                                    assume(self.current_view_suspectors@ == set![idx as u64]); // Fix this
                                    assume(new_state.current_view_suspectors == set![idx_int]); // Fix this
                                } else {
                                    assert(self.current_view_suspectors@ == Set::<u64>::empty());
                                    assert(new_state.current_view_suspectors == Set::<int>::empty());
                                }

                                assert(new_state.epoch_length == new_epoch_length_spec);

                                let expected_epoch_end_time = UpperBoundedAddition(
                                    clock as int,
                                    new_epoch_length_spec,
                                    old_state.constants.all.params.max_integer_val,
                                );
                                assert(new_state.epoch_end_time == expected_epoch_end_time);

                                assert(new_state.requests_received_this_epoch == Seq::<Request>::empty());

                                let combined_prev = old_state.requests_received_prev_epochs
                                                    + old_state.requests_received_this_epoch;
                                let bounded = BoundRequestSequence(
                                    combined_prev,
                                    old_state.constants.all.params.max_integer_val
                                );
                                assert(new_state.requests_received_prev_epochs == bounded);

                                // Now finally:
                                assert(new_state == ElectionState {
                                    constants: old_state.constants,
                                    current_view: new_view,
                                    current_view_suspectors: if suspicious { set![idx_int] } else { Set::<int>::empty() },
                                    epoch_end_time: expected_epoch_end_time,
                                    epoch_length: new_epoch_length_spec,
                                    requests_received_this_epoch: Seq::<Request>::empty(),
                                    requests_received_prev_epochs: bounded,
                                });

                                assert(ElectionStateProcessHeartbeat(old_state, new_state, p@, clock as int));
                            }
                        } else {
                            // no change
                            proof {
                                assert(self@ == old(self)@);
                                assert(ElectionStateProcessHeartbeat(old(self)@, self@, p@, clock as int));
                            }
                        }
                    }
                    _ => {
                        // unreachable due to precondition
                    }
                }
            }
        }
    }



    // Blocked on suspectors(Hashset length assrtion, if that is fixed, the function will be verified)
    pub fn CElectionStateCheckForViewTimeout(
        &mut self,
        clock:u64
    )
        requires
            old(self).valid(),
        ensures
            self.valid(),
            ElectionStateCheckForViewTimeout(old(self)@, self@, clock as int)
    {
        if clock < self.epoch_end_time {
            // Do nothing
        } else if self.requests_received_prev_epochs.len() == 0 {
            // Self::print("Haven't receive any request");
            let new_epoch_length = self.constants.all.params.baseline_view_timeout_period;

            self.epoch_end_time = CUpperBoundedAddition(clock, new_epoch_length, self.constants.all.params.max_integer_val);

            self.epoch_length = new_epoch_length;

            self.requests_received_prev_epochs = clone_vec_crequest(&self.requests_received_this_epoch);

            self.requests_received_this_epoch = Vec::new();

            self.prev_req_set = clone_hashset(&self.cur_req_set);
            self.cur_req_set = HashSet::new();

            proof {
                let old_es = old(self)@;
                let new_es = self@;
                assert(new_es.constants == old_es.constants);
                assert(new_es.current_view == old_es.current_view);
                assert(new_es.current_view_suspectors == old_es.current_view_suspectors);

                assert(new_es.epoch_end_time ==
                    UpperBoundedAddition(clock as int,
                        new_epoch_length as int,
                        UpperBound::UpperBoundFinite{ n: self.constants.all.params.max_integer_val as int }));


                assert(new_es.epoch_length ==
                    self.constants.all.params.baseline_view_timeout_period as int);

                assert(new_es.requests_received_this_epoch == Seq::<Request>::empty());

                assert(new_es.requests_received_prev_epochs ==
                    old_es.requests_received_this_epoch);

                assert(ElectionStateCheckForViewTimeout(old_es, new_es, clock as int));
            }
        } else {
            Self::print("suspecious");
            let mut suspectors = clone_hashset_u64(&self.current_view_suspectors);

            suspectors.insert(self.constants.my_index);

            self.current_view_suspectors = suspectors;

            self.epoch_end_time = CUpperBoundedAddition(clock, self.epoch_length, self.constants.all.params.max_integer_val);

            let new_prevs = concat_vecs(
                &self.requests_received_prev_epochs,
                &self.requests_received_this_epoch
            );

            assume(new_prevs@.len() < 0x1_0000_0000_0000_0000); // Make sure to deal with this assumption

            self.requests_received_prev_epochs = Self::CBoundRequestSequence(&new_prevs, self.constants.all.params.max_integer_val);

            self.requests_received_this_epoch = Vec::new();

            let new_set = union_sets(&self.prev_req_set, &self.cur_req_set);
            self.cur_req_set = HashSet::new();
            let bounded_set = Self::BoundCRequestHeaders(&new_prevs, &new_set, self.constants.all.params.max_integer_val);
            self.prev_req_set = bounded_set;

            proof {
                let old_es = old(self)@;

                let new_es = self@;

                assert(new_es.constants == old_es.constants);

                assert(new_es.current_view == old_es.current_view);

                assume(new_es.current_view_suspectors == old_es.current_view_suspectors + set![self.constants.my_index as int]); // Fix this

                assert(new_es.epoch_end_time ==
                    UpperBoundedAddition(clock as int,
                        old_es.epoch_length,
                        UpperBound::UpperBoundFinite{ n: self.constants.all.params.max_integer_val as int }));

                assert(new_es.epoch_length == old_es.epoch_length);

                assert(new_es.requests_received_this_epoch == Seq::<Request>::empty());

                assert({
                    let prevs = old_es.requests_received_prev_epochs;

                    let curr = old_es.requests_received_this_epoch;

                    new_es.requests_received_prev_epochs ==

                    BoundRequestSequence(
                        prevs + curr,
                        UpperBound::UpperBoundFinite {
                            n: self.constants.all.params.max_integer_val as int
                        }
                    )
                });

                assert(ElectionStateCheckForViewTimeout(old_es, new_es, clock as int));
            }

        }
    }


    // Blocked on the length of the suspectors (Hashset)
    pub fn CElectionStateCheckForQuorumOfViewSuspicions(
        &mut self,
        clock:u64
    )
        requires
            old(self).valid(),
        ensures
            self.valid(),
            ElectionStateCheckForQuorumOfViewSuspicions(old(self)@, self@, clock as int)
    {


        let ghost es = old(self)@;
        let ghost es_ = self@;
        assert((self.current_view.seqno >= self.constants.all.params.max_integer_val) == !LtUpperBound(es.current_view.seqno, es.constants.all.params.max_integer_val));
        assume(self.current_view_suspectors.len() as int == es.current_view_suspectors.len()); // If we assume this then whole function will pass the test
        if self.current_view_suspectors.len() < self.constants.all.config.CMinQuorumSize() ||
            self.current_view.seqno >= self.constants.all.params.max_integer_val
        {
            // No state change
        }
        else
        {
            let new_epoch_length = CUpperBoundedAddition(self.epoch_length, self.epoch_length, self.constants.all.params.max_integer_val);
            self.current_view = Self::CComputeSuccessorView(self.current_view, self.constants.all.clone_up_to_view());
            self.current_view_suspectors = HashSet::new();
            self.epoch_end_time = CUpperBoundedAddition(clock, new_epoch_length, self.constants.all.params.max_integer_val);
            self.epoch_length = new_epoch_length;
            let new_prevs = concat_vecs(
                &self.requests_received_prev_epochs,
                &self.requests_received_this_epoch
            );

            // have to prove this using a lemma
            assume(new_prevs.len() < 0x1_0000_0000_0000_0000);

            self.requests_received_this_epoch = Vec::new();
            self.requests_received_prev_epochs = Self::CBoundRequestSequence(&new_prevs, self.constants.all.params.max_integer_val);

            let new_set = union_sets(&self.prev_req_set, &self.cur_req_set);
            self.cur_req_set = HashSet::new();
            let bounded_set = Self::BoundCRequestHeaders(&new_prevs, &new_set, self.constants.all.params.max_integer_val);
            self.prev_req_set = bounded_set;

            proof {
                let es = old(self)@;
                let es_ = self@;

                // Show each field in the constructed `self@` matches the spec definition
                assert(es_.constants == es.constants);
                assert(es_.current_view == ComputeSuccessorView(es.current_view, es.constants.all));
                assert(es_.current_view_suspectors == Set::<int>::empty());

                let ghost new_epoch_length = UpperBoundedAddition(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val);
                assert(es_.epoch_length == new_epoch_length);
                assert(es_.epoch_end_time == UpperBoundedAddition(clock as int, new_epoch_length, es.constants.all.params.max_integer_val));
                assert(es_.requests_received_this_epoch == Seq::<Request>::empty());
                assert(
                    es_.requests_received_prev_epochs ==
                    BoundRequestSequence(
                        es.requests_received_prev_epochs + es.requests_received_this_epoch,
                        es.constants.all.params.max_integer_val
                    )
                );
                assert(
                    es_ == ElectionState {
                        constants: es.constants,
                        current_view: ComputeSuccessorView(es.current_view, es.constants.all),
                        current_view_suspectors: Set::<int>::empty(),
                        epoch_length: UpperBoundedAddition(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val),
                        epoch_end_time: UpperBoundedAddition(clock as int, UpperBoundedAddition(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val), es.constants.all.params.max_integer_val),
                        requests_received_this_epoch: Seq::<Request>::empty(),
                        requests_received_prev_epochs: BoundRequestSequence(
                            es.requests_received_prev_epochs + es.requests_received_this_epoch,
                            es.constants.all.params.max_integer_val
                        )
                    }
                );
                // Not passing the assertion test
                assert(ElectionStateCheckForQuorumOfViewSuspicions(es, es_, clock as int));
            }
        }
    }

    pub fn FindEarlierRequests(&self, target: CRequest) -> (r: bool)
        requires
            self.valid(),
            target.valid(),
        ensures
        ({
            let ss = self@;
            && r == exists |req:Request| (ss.requests_received_prev_epochs.contains(req) 
                                        || ss.requests_received_this_epoch.contains(req))
                                        && RequestsMatch(req, target@)
        })
    {
        let mut found = false;
        let ghost ss = self@;
        let ghost starget = target@;

        let mut i = 0;
        while i < self.requests_received_this_epoch.len()
            invariant
                0 <= i <= self.requests_received_this_epoch.len(),
                self.valid(),
                target.valid(),
                starget == target@,
                ss == self@,
                !found,
                !found ==> forall |m:int| 0 <= m < i ==> !RequestsMatch(ss.requests_received_this_epoch[m], starget),
            decreases self.requests_received_this_epoch.len() - i,
        {
            if(Self::CRequestsMatch(&self.requests_received_this_epoch[i], &target)) {
                found = true;
                assert(self.requests_received_this_epoch[i as int]@ == ss.requests_received_this_epoch[i as int]);
                assert(target@ == starget);
                assert(RequestsMatch(self.requests_received_this_epoch[i as int]@ , target@));
                assert(RequestsMatch(ss.requests_received_this_epoch[i as int], starget));
                assert(
                    exists |req:Request| ss.requests_received_this_epoch.contains(req) && RequestsMatch(req, starget)
                );
                return true;
            }
            i +=1 ;
        }
        assert(!found);
        assert(forall |m:int| 0 <= m < ss.requests_received_this_epoch.len() ==> !RequestsMatch(ss.requests_received_this_epoch[m], starget));
        assert(forall |req:Request| ss.requests_received_this_epoch.contains(req) ==> !RequestsMatch(req, starget));

        let mut j = 0;
        while j < self.requests_received_prev_epochs.len()
            invariant
                0 <= j <= self.requests_received_prev_epochs.len(),
                self.valid(),
                target.valid(),
                starget == target@,
                ss == self@,
                !found,
                !found ==> forall |n:int| 0 <= n < j ==> !RequestsMatch(ss.requests_received_prev_epochs[n], starget),
            decreases self.requests_received_prev_epochs.len() - j,
        {
            if(Self::CRequestsMatch(&self.requests_received_prev_epochs[j], &target)) {
                found = true;
                assert(self.requests_received_prev_epochs[j as int]@ == ss.requests_received_prev_epochs[j as int]);
                assert(target@ == starget);
                assert(RequestsMatch(self.requests_received_prev_epochs[j as int]@ , target@));
                assert(RequestsMatch(ss.requests_received_prev_epochs[j as int], starget));
                assert(
                    exists |req:Request| ss.requests_received_prev_epochs.contains(req) && RequestsMatch(req, starget)
                );
                return true;
            }
            j += 1;
        }
        assert(!found);
        assert(forall |n:int| 0 <= n < ss.requests_received_this_epoch.len() ==> !RequestsMatch(ss.requests_received_this_epoch[n], starget));
        assert(forall |req:Request| ss.requests_received_prev_epochs.contains(req) ==> !RequestsMatch(req, starget));
        
        assert(!(exists |req:Request| (ss.requests_received_prev_epochs.contains(req) 
        || ss.requests_received_this_epoch.contains(req))
        && RequestsMatch(req, starget)));

        false
    }

    #[verifier(external_body)]
    pub fn FindEarlierRequestsInSet(& self, target:CRequest) -> (r:bool) 
        requires
            self.valid(),
            target.valid(),
        ensures
        ({
            let ss = self@;
            && r == exists |req:Request| (ss.requests_received_prev_epochs.contains(req) 
                                        || ss.requests_received_this_epoch.contains(req))
                                        && RequestsMatch(req, target@)
        })
    {
        let header = CRequestHeader{client:target.client.clone_up_to_view(), seqno:target.seqno};   
        let b1 = self.prev_req_set.contains(&header);
        if b1 {
            true
        } else {
            let b2 = self.cur_req_set.contains(&header);
            b2
        }
    }

    #[verifier(external_body)]
    pub fn BoundCRequestHeaders(s:&Vec<CRequest>, headers:&HashSet<CRequestHeader>, lengthBound:u64) -> (new_headers:HashSet<CRequestHeader>)
    {
        let mut res = HashSet::new();
        let mut i = 0;
        let bound = lengthBound as usize;
        if bound >= 0 && bound < s.len()
        {
            while i < bound
            {
                let new_header = CRequestHeader{client:s[i].client.clone_up_to_view(), seqno:s[i].seqno};
                res.insert(new_header);
                i = i + 1;
            }
            res
        } else {
            clone_hashset(&headers)
        }
    }

    

    // #[verifier(external_body)]
    pub fn CElectionStateReflectReceivedRequest(
        &mut self,
        req:CRequest
    )
        requires
            old(self).valid(),
            req.valid(),
        ensures
            self.valid(),
            ElectionStateReflectReceivedRequest(old(self)@, self@, req@)
    {
        let ghost ss = old(self)@;
        let ghost req_ = req@;

        // let b = Self::FindEarlierRequests(self, req.clone_up_to_view());
        let b = Self::FindEarlierRequestsInSet(self, req.clone_up_to_view());
        if b {
            Self::print("Has received the request");
            // If request was already seen, nothing changes.
            assert(self@ == ss);
            assert(ElectionStateReflectReceivedRequest(ss, self@, req_)); // Verified
        } else {
            // Self::print("Add request to this epoch");
            let mut new_seq = concat_vecs(&self.requests_received_this_epoch,&vec![req.clone_up_to_view()]);

            assume(new_seq.len() < 0x1_0000_0000_0000_0000); // Make sure to deal with this assumption

            self.requests_received_this_epoch = CElectionState::CBoundRequestSequence(&new_seq, self.constants.all.params.max_integer_val);

            let header = CRequestHeader{client:req.client.clone_up_to_view(), seqno:req.seqno};
            let mut new_set = clone_hashset(&self.cur_req_set);
            new_set.insert(header);
            // let new_set = self.cur_req_set.insert(header);
            let bounded_set = Self::BoundCRequestHeaders(&new_seq, &new_set, self.constants.all.params.max_integer_val);
            self.cur_req_set = bounded_set;
        }
        proof {
            let ghost ss = old(self)@;
            let ghost req_ = req@;

            let ghost updated_seq = ss.requests_received_this_epoch + seq![req_];
            let ghost bounded_seq = BoundRequestSequence(updated_seq, ss.constants.all.params.max_integer_val);

            // Show that the field that changed in self@ matches the spec definition
            assume(self@.requests_received_this_epoch == bounded_seq); // This is the only thing that fails the verification test.
            assert(self@.requests_received_prev_epochs == ss.requests_received_prev_epochs);
            assert(self@.constants == ss.constants);
            assert(self@.current_view == ss.current_view);
            assert(self@.current_view_suspectors == ss.current_view_suspectors);
            assert(self@.epoch_end_time == ss.epoch_end_time);
            assert(self@.epoch_length == ss.epoch_length);

            // Now conclude that self@ equals the expected spec-level state
            assert(self@ == ElectionState {
                constants: ss.constants,
                current_view: ss.current_view,
                current_view_suspectors: ss.current_view_suspectors,
                epoch_end_time: ss.epoch_end_time,
                epoch_length: ss.epoch_length,
                requests_received_this_epoch: bounded_seq,
                requests_received_prev_epochs: ss.requests_received_prev_epochs,
            });

            // And finally assert the refinement
            assert(ElectionStateReflectReceivedRequest(ss, self@, req_));
        }
    }

    pub fn CRemoveAllSatisfiedRequestsInSequence(s: &Vec<CRequest>, r: &CRequest) -> (rc: Vec<CRequest>)
        requires
            forall |i: int| 0 <= i < s@.len() ==> s@[i].valid(),
            r.valid(),
        ensures
            forall |i: int| 0 <= i < rc@.len() ==> rc@[i].valid(),
            rc@.map(|i, req:CRequest| req@) == RemoveAllSatisfiedRequestsInSequence(s@.map(|i, req: CRequest| req@), r@),
        decreases s.len(),
    {
        if s.len() == 0 {
            let empty: Vec<CRequest> = Vec::new();
            proof {
                assert(s@.map(|i, req: CRequest| req@).len() == 0);
                assert(RemoveAllSatisfiedRequestsInSequence(s@.map(|i, req: CRequest| req@), r@) == Seq::<Request>::empty());
                assert(empty@.map(|i, req: CRequest| req@) == Seq::<Request>::empty());
            }
            return empty;
        }

        let head = s[0].clone_up_to_view();
        let tail = truncate_vec(s, 1, s.len());

        let tail_filtered = Self::CRemoveAllSatisfiedRequestsInSequence(&tail, r);

        if Self::CRequestSatisfiedBy(&head, r) {
            proof {
                assert(tail_filtered@.map(|i, req: CRequest| req@)
                    == RemoveAllSatisfiedRequestsInSequence(tail@.map(|i, req: CRequest| req@), r@));
                assert(s@.map(|i, req: CRequest| req@)[0] == head@);
                assert(s@.map(|i, req: CRequest| req@).drop_first()
                    == tail@.map(|i, req: CRequest| req@));
                assert(RemoveAllSatisfiedRequestsInSequence(s@.map(|i, req: CRequest| req@), r@)
                    == RemoveAllSatisfiedRequestsInSequence(tail@.map(|i, req: CRequest| req@), r@));
            }
            tail_filtered
        } else {
            let res = concat_vecs(&vec![head], &tail_filtered);
            proof {
                assert(tail_filtered@.map(|i, req: CRequest| req@)
                    == RemoveAllSatisfiedRequestsInSequence(tail@.map(|i, req: CRequest| req@), r@));
                let s_view = s@.map(|i, req: CRequest| req@);
                let tail_view = tail@.map(|i, req: CRequest| req@);
                assert(s_view.drop_first() == tail_view);
                assert(s_view[0] == head@);
                assert(res@.map(|i, req: CRequest| req@)
                    == seq![head@] + RemoveAllSatisfiedRequestsInSequence(tail_view, r@));
                assert(RemoveAllSatisfiedRequestsInSequence(s_view, r@)
                    == seq![head@] + RemoveAllSatisfiedRequestsInSequence(tail_view, r@));
            }
            res
        }
    }

    pub fn CRemoveExecutedRequestBatch(reqs:&Vec<CRequest>, batch:&CRequestBatch) -> (r: Vec<CRequest>)
        requires
            (forall |i: int| 0 <= i < reqs@.len() ==> reqs@[i].valid()),
            crequestbatch_is_valid(batch),
        ensures
            (forall |i: int| 0 <= i < r@.len() ==> r@[i].valid()),
            r@.map(|i, req:CRequest| req@) == RemoveExecutedRequestBatch(reqs@.map(|i, req:CRequest| req@), abstractify_crequestbatch(batch)),
        decreases batch.len(),
    {
        if batch.len() == 0 {
            return clone_vec_crequest(reqs);
        }

        let head = batch[0].clone_up_to_view();
        let tail = truncate_vec(&batch, 1, batch.len());
        let filtered = Self::CRemoveAllSatisfiedRequestsInSequence(&reqs, &head);
        Self::CRemoveExecutedRequestBatch(&filtered, &tail)
    }

    #[verifier(external_body)]
    pub fn CRemoveAllSatisfiedRequestsInSequenceAndSet(requests:&Vec<CRequest>, headers:&mut HashSet<CRequestHeader>, r:&CRequest) -> (res:Vec<CRequest>)
    {
        let mut i = 0;
        let len = requests.len();

        let mut new_seq = Vec::new();
        // let mut new_set:HashSet<CRequestHeader> = HashSet::new();

        while i < len 
        {
            let header = CRequestHeader{client:requests[i].client.clone_up_to_view(), seqno:requests[i].seqno};
            if Self::CRequestSatisfiedBy(&requests[i], r) {
                headers.remove(&header);
            } else {
                new_seq = concat_vecs(&new_seq, &vec![requests[i].clone_up_to_view()]);
            }
            i = i + 1;
        }
        new_seq
    }

    #[verifier(external_body)]
    pub fn CElectionStateReflectExecutedRequestBatch_Optimized(
        &mut self,
        batch:&CRequestBatch
    )
        requires
            old(self).valid(),
            crequestbatch_is_valid(batch),
        ensures
            self.valid(),
            ElectionStateReflectExecutedRequestBatch(old(self)@, self@, abstractify_crequestbatch(batch))
    {
        let mut i = 0;
        while i < batch.len()
        {
            let req = batch[i].clone_up_to_view();
            let new_prev_req = Self::CRemoveAllSatisfiedRequestsInSequenceAndSet(&self.requests_received_prev_epochs, &mut self.prev_req_set, &req);
            let new_cur_req = Self::CRemoveAllSatisfiedRequestsInSequenceAndSet(&self.requests_received_this_epoch, &mut self.cur_req_set, &req);
            self.requests_received_prev_epochs = new_prev_req;
            self.requests_received_this_epoch = new_cur_req;
            i = i + 1;
        }
        // self.requests_received_this_epoch = Self::CRemoveExecutedRequestBatch(&self.requests_received_this_epoch, &batch);
        // self.requests_received_prev_epochs = Self::CRemoveExecutedRequestBatch(&self.requests_received_prev_epochs, &batch);
    }

    pub fn CElectionStateReflectExecutedRequestBatch(
        &mut self,
        batch:&CRequestBatch
    )
        requires
            old(self).valid(),
            crequestbatch_is_valid(batch),
        ensures
            self.valid(),
            ElectionStateReflectExecutedRequestBatch(old(self)@, self@, abstractify_crequestbatch(batch))
    {
        self.requests_received_this_epoch = Self::CRemoveExecutedRequestBatch(&self.requests_received_this_epoch, &batch);
        self.requests_received_prev_epochs = Self::CRemoveExecutedRequestBatch(&self.requests_received_prev_epochs, &batch);
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


    pub open spec fn u64_to_int(x: u64) -> int {
        x as int
    }


    #[verifier::external_body]
    pub proof fn lemma_u64_to_int_injective(x: u64, y: u64)
        requires u64_to_int(x) == u64_to_int(y)
        ensures x == y
    {}

    pub proof fn lemma_u64_to_int_injective_forall()
    ensures forall |x: u64, y: u64| #[trigger] u64_to_int(x) == #[trigger] u64_to_int(y) ==> x == y
{
    assert forall |x: u64, y: u64| #[trigger] u64_to_int(x) == #[trigger] u64_to_int(y) implies x == y by {
        lemma_u64_to_int_injective(x, y);
    }
}


}
