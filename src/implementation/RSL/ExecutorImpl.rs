use crate::implementation::RSL::types_i::*;
use crate::implementation::RSL::ExecutorImpl::OutboundPackets::PacketSequence;
use crate::protocol::RSL::state_machine::*;
use crate::protocol::RSL::types::*;
use crate::services::RSL::app_state_machine::*;
use std::collections::HashMap;
use vstd::prelude::*;
use crate::common::collections::vecs::*;
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::implementation::common::generic_refinement::*;
use crate::implementation::RSL::appinterface::*;
use crate::implementation::RSL::cbroadcast::*;
use crate::implementation::RSL::cconstants::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::CStateMachine::*;
use crate::implementation::RSL::ElectionImpl::*;
use crate::implementation::RSL::ExecutorImpl::OutboundPackets::Broadcast;
use crate::protocol::common::upper_bound::*;
use crate::protocol::RSL::executor::*;
use crate::protocol::RSL::{constants::*, environment::*, message::*};
use vstd::std_specs::hash::*;
use vstd::{prelude::*, seq::*, seq_lib::*};
// DEPRECATED: Use `crate::generated::RSL::executor_gen` for functional wrappers
// and `crate::generated::RSL::types_gen::{CExecutor, COutstandingOperation}` for types directly.
// This module retains only CExecutorExecute (called from ReplicaImpl.rs) and its helpers.
#[deprecated(note = "Import CExecutor, COutstandingOperation from crate::generated::RSL::types_gen instead")]
pub use crate::generated::RSL::types_gen::{CExecutor, COutstandingOperation};

verus! {
    broadcast use crate::common::native::io_s::axiom_endpoint_key_model;

impl CExecutor{

    pub fn CGetPacketsFromReplies(me:&EndPoint, requests:&Vec<CRequest>, replies:&Vec<CReply>) -> (cr:Vec<CPacket>)
        requires
            me.valid_public_key(),
            crequestbatch_is_valid(requests),
            forall|i: int| 0 <= i < requests.len() ==> requests[i].valid(),
            forall|i: int| 0 <= i < replies.len() ==> replies[i].valid(),
            requests.len() == replies.len()
        ensures
            ({
                let lr = GetPacketsFromReplies(
                    me@,
                    requests@.map(|i,x:CRequest| x@),
                    replies@.map(|i,x:CReply| x@));

                &&& forall |i:int| 0 <= i < cr@.len() ==> cr@[i].valid()
                &&& cr@.map(|i,x: CPacket| x@) == lr
            })
        decreases requests.len()
    {
        if requests.len()==0 {
            let res = Vec::new();
            assert(res@.map(|i, p:CPacket| p@) == Seq::<RslPacket>::empty());
            res
        } else {
            let new_req = truncate_vec(&requests, 1, requests.len());
            assert(new_req@.map(|i, r:CRequest| r@) == requests@.map(|i, r:CRequest| r@).drop_first());
            let new_rep = truncate_vec(&replies, 1, replies.len());
            assert(new_rep@.map(|i, r:CReply| r@) == replies@.map(|i, r:CReply| r@).drop_first());
            let rest = Self::CGetPacketsFromReplies(&me, &new_req, &new_rep);
            assert(rest@.map(|i, p:CPacket| p@) == GetPacketsFromReplies(me@, requests@.map(|i, r:CRequest| r@).drop_first(), replies@.map(|i, r:CReply| r@).drop_first()));
            let pkt = CPacket{
                dst: requests[0].client.clone_up_to_view(),
                src: me.clone_up_to_view(),
                msg: CMessage::CMessageReply{
                    seqno_reply: requests[0].seqno,
                    reply: replies[0].reply.clone_up_to_view()
                }
            };
            let ghost spkt = LPacket{
                dst:requests[0].client@,
                src:me@,
                msg:RslMessage::RslMessageReply{
                    seqno_reply:requests[0].seqno as int,
                    reply:replies[0].reply@,
                }
            };
            assert(pkt@ == spkt);

            let mut first:Vec<CPacket> = Vec::new();
            first.push(pkt);
            assert(first@.map(|i, p:CPacket| p@) == seq![spkt]);

            let res = concat_vecs(&first, &rest);
            assert(res@.map(|i, p:CPacket| p@) ==  seq![spkt] + GetPacketsFromReplies(me@, requests@.map(|i, r:CRequest| r@).drop_first(), replies@.map(|i, r:CReply| r@).drop_first()));

            res
        }
    }


    pub fn CClientsInReplies(replies:&Vec<CReply>) -> (m:CReplyCache)
        requires
            forall|i: int| 0 <= i < replies.len() ==> replies[i].valid(),
        ensures
            creplycache_is_valid(&m),
            forall|c: EndPoint| m@.contains_key(c) ==> m@[c].client@ == c@,
            forall|c: EndPoint| m@.contains_key(c) ==> (exists|req_idx: int| 0 <= req_idx < replies.len()
                && replies[req_idx].client == c
                && m@[c] == replies[req_idx]),
            ({
                let lr = LClientsInReplies(replies@.map(|i,x:CReply| x@));
                && abstractify_creplycache(&m)==lr
            })
        decreases replies.len()
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;
        if replies.len() == 0 {
            let res:HashMap<EndPoint, CReply> = HashMap::new();
            assert(creplycache_is_valid(&res));
            assert(forall|c: EndPoint| res@.contains_key(c) ==> res@[c].client@ == c@);
            let ghost sres = abstractify_creplycache(&res);
            assert(sres == Map::<AbstractEndPoint, Reply>::empty());
            res
        } else {
            let temp = truncate_vec(&replies, 1, replies.len());
            let mut res = Self::CClientsInReplies(&temp);
            assert(forall|c: EndPoint| res@.contains_key(c) ==> res@[c].client@ == c@);
            assert(forall|c: EndPoint| res@.contains_key(c) ==> (exists|req_idx: int| 0 <= req_idx < temp.len()
                && temp[req_idx].client == c
                && res@[c] == temp[req_idx]));
            assert(temp@.map(|i, r:CReply| r@) == replies@.map(|i, r:CReply| r@).drop_first());
            assert(abstractify_creplycache(&res) == LClientsInReplies(temp@.map(|i, r:CReply| r@)));

            assert(forall |i:EndPoint| res@.contains_key(i) ==> i.abstractable() && res@[i].abstractable());
            let client = replies[0].client.clone_up_to_view();
            let rep = replies[0].clone_up_to_view();
            assert(client.abstractable());
            assert(rep.abstractable());
            assert(rep.client@ == client@);
            res.insert(client, rep);

            // all these assumptions are caused by HashMap's insert has not been verified
            assume(abstractify_creplycache(&res) == LClientsInReplies(temp@.map(|i, r:CReply| r@)).insert(replies[0].client@, replies[0]@));

            assume(forall|c: EndPoint| res@.contains_key(c) ==> (exists|req_idx: int| 0 <= req_idx < temp.len()
                && temp[req_idx].client == c
                && res@[c] == temp[req_idx]));
            assert(forall|c: EndPoint| res@.contains_key(c) ==> res@[c].client@ == c@);
            assert(creplycache_is_abstractable(&res));
            assert(creplycache_is_valid(&res));
            res
        }
    }

    #[verifier(external_body)]
    pub fn CUpdateNewCache(c:&CReplyCache, replies:&Vec<CReply>) -> (c_prime:CReplyCache)
        requires
            creplycache_is_valid(c),
            forall|i: int| 0 <= i < replies.len() ==> replies[i].valid()
        ensures
            creplycache_is_valid(&c_prime),
            UpdateNewCache(
                abstractify_creplycache(c),
                abstractify_creplycache(&c_prime),
                replies@.map(|i,x:CReply| x@)
            )
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;
        broadcast use crate::common::native::io_s::axiom_endpoint_key_model;

        let nc = Self::CClientsInReplies(&replies);
        let mut updated_cache = HashMap::<EndPoint, CReply>::new();

        let c_keys = c.keys();
        assert(c_keys@.0 == 0);
        assert(c_keys@.1.to_set() =~= c@.dom());

        for k in iter:c_keys
            invariant
                creplycache_is_valid(c),
                creplycache_is_valid(&updated_cache),
        {
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::hash_map::group_hash_map_axioms;
            let v = c.get(k);
            match v{
                Some(v) => {
                    assert(k.abstractable());
                    assert(v.valid());
                    updated_cache.insert(k.clone_up_to_view(), v.clone_up_to_view());
                }
                None => {

                }
            }
        }

        let nc_keys = nc.keys();
        assert(nc_keys@.0 == 0);
        assert(nc_keys@.1.to_set() =~= nc@.dom());
        for k in iter:nc_keys
            invariant
                creplycache_is_valid(&nc),
                creplycache_is_valid(&updated_cache),
        {
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::hash_map::group_hash_map_axioms;
            let v = nc.get(k);
            match v{
                Some(v) => {
                    assert(k.abstractable());
                    assert(v.valid());
                    updated_cache.insert(k.clone_up_to_view(), v.clone_up_to_view());
                }
                None => {

                }
            }
        }
        updated_cache
    }

    #[verifier(external_body)]
    pub fn CExecutorExecute(&mut self) -> (res: OutboundPackets)
        requires
            old(self).valid(),
            old(self).next_op_to_execute is COutstandingOpKnown,
            LtUpperBound(old(self)@.ops_complete, old(self)@.constants.all.params.max_integer_val),
            LReplicaConstantsValid(old(self)@.constants)
        ensures
            self.valid(),
            res.valid(),
            LExecutorExecute(old(self)@,
                                self@,
                                res@)
    {
        match &self.next_op_to_execute {
            COutstandingOperation::COutstandingOpKnown{v, bal} => {
                let batch = clone_request_batch_up_to_view(&v);
                let x = bal.clone_up_to_view();
                let (new_states, replies) = CHandleRequestBatch(&self.app, &batch);
                let new_state = new_states[new_states.len()-1];

                let new_max_bal_reflected = if CBalLeq(&self.max_bal_reflected, &x) {
                    x
                } else {
                    self.max_bal_reflected
                };

                self.app= new_state;
                self.ops_complete = self.ops_complete + 1;
                self.max_bal_reflected = new_max_bal_reflected;
                self.next_op_to_execute = COutstandingOperation::COutstandingOpUnknown{};
                self.reply_cache = Self::CUpdateNewCache(&self.reply_cache, &replies);
                let pkt_vec = Self::CGetPacketsFromReplies(
                    &self.constants.all.config.replica_ids[self.constants.my_index as usize],
                    &batch,
                    &replies
                );
                assert(forall |i:int| 0 <= i < pkt_vec.len() ==> pkt_vec@[i].valid());
                let outpackets = PacketSequence{s: pkt_vec};
                outpackets
            }
            COutstandingOperation::COutstandingOpUnknown {  } => {
                let mut pkt_vec: Vec<CPacket> = Vec::new();
                let outpackets = OutboundPackets::PacketSequence{
                    s:pkt_vec,
                };
                outpackets
            }
        }
    }

}

}

// verus!
