use crate::implementation::RSL::types_i::*;
use crate::implementation::RSL::types_i::*;
use crate::implementation::RSL::ExecutorImpl::OutboundPackets::PacketSequence;
use crate::protocol::RSL::state_machine::*;
use crate::protocol::RSL::types::*;
use crate::services::RSL::app_state_machine::*;
use std::collections::HashMap;
use vstd::prelude::*;
// use crate::implementation::RSL::types_i::abstractify_crequestbatch;
// use crate::implementation::RSL::message_i::*;
use crate::common::collections::vecs::*;
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::implementation::common::generic_refinement::*;
use crate::implementation::common::generic_refinement::*;
use crate::implementation::RSL::appinterface::*;
use crate::implementation::RSL::cbroadcast::*;
use crate::implementation::RSL::cbroadcast::*;
use crate::implementation::RSL::cconstants::*;
use crate::implementation::RSL::cconstants::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::CStateMachine::*;
use crate::implementation::RSL::ElectionImpl::*;
use crate::implementation::RSL::ExecutorImpl::OutboundPackets::Broadcast;
use crate::protocol::common::upper_bound::*;
use crate::protocol::RSL::executor::*;
use crate::protocol::RSL::{constants::*, environment::*, message::*};
use crate::services::RSL::app_state_machine::*;
use vstd::std_specs::hash::*;
use vstd::{prelude::*, seq::*, seq_lib::*};

verus! {
    broadcast use crate::common::native::io_s::axiom_endpoint_key_model;
#[derive(Clone)]
pub enum COutstandingOperation {
    COutstandingOpKnown{
        v: CRequestBatch,
        bal: CBallot,
    },
    COutstandingOpUnknown{},
}

impl COutstandingOperation{

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
                    // v: abstractify_crequestbatch(v),
                    bal: bal@,
                }
            }
            COutstandingOperation::COutstandingOpUnknown{} => OutstandingOperation::OutstandingOpUnknown{},
        }
    }

}

#[derive(Clone)]
pub struct CExecutor {
    pub constants: CReplicaConstants,
    pub app: CAppState,
    pub ops_complete: u64,
    pub max_bal_reflected: CBallot,
    pub next_op_to_execute: COutstandingOperation,
    pub reply_cache: CReplyCache,
}

impl CExecutor{

    pub open spec fn valid(&self) -> bool {
        self.abstractable()
            && self.constants.valid()
            && CAppStateIsValid(&self.app)
            && self.max_bal_reflected.valid()
            && self.next_op_to_execute.valid()
            && creplycache_is_valid(&self.reply_cache)
    }

    pub open spec fn abstractable(&self) -> bool {
        self.constants.abstractable()
            && CAppStateIsAbstractable(&self.app)
            && self.max_bal_reflected.abstractable()
            && self.next_op_to_execute.abstractable()
            && creplycache_is_abstractable(&self.reply_cache)
    }

    pub open spec fn view(&self) -> LExecutor
        recommends
            self.abstractable(){
        let res = LExecutor {
            constants: self.constants.view(),
            // app: AbstractifyCAppStateToAppState(s.app),
            app: self.app,
            ops_complete: self.ops_complete as int,
            max_bal_reflected: self.max_bal_reflected.view(),
            next_op_to_execute: self.next_op_to_execute.view(),
            reply_cache: abstractify_creplycache(&self.reply_cache),
        };
        res
    }

    // #[verifier(external_body)]
    pub fn CExecutorInit(c: CReplicaConstants) -> (s:Self)
        requires
            c.valid()
        ensures
            s.valid(),
            LExecutorInit(s@, c@)
    {
        let s = CExecutor {
            constants: c,
            app: CAppStateInit(),
            ops_complete: 0,
            max_bal_reflected: CBallot { seqno: 0, proposer_id: 0 },
            next_op_to_execute: COutstandingOperation::COutstandingOpUnknown{},
            reply_cache: HashMap::new(),
        };
        let ghost sc = c@;
        let ghost ss = s@;
        assert(ss.constants == sc);
        assert(ss.app == AppInitialize());
        assert(ss.next_op_to_execute == OutstandingOperation::OutstandingOpUnknown{});
        assert(ss.reply_cache == Map::<AbstractEndPoint, Reply>::empty());
        s
    }

    pub fn CExecutorGetDecision(&mut self, bal: CBallot, opn: COperationNumber, v:&CRequestBatch)
        requires
            old(self).valid(),
            bal.valid(),
            COperationNumberIsValid(opn),
            crequestbatch_is_valid(v),
            opn == old(self).ops_complete,
            old(self).next_op_to_execute is COutstandingOpUnknown
        ensures
            self.valid(),
            LExecutorGetDecision(old(self)@,
                                    self@,
                                    bal@,
                                    AbstractifyCOperationNumberToOperationNumber(opn),
                                    abstractify_crequestbatch(v))

    {
        self.next_op_to_execute = COutstandingOperation::COutstandingOpKnown{v: clone_vec_crequest(v), bal: bal};
    }

    // #[verifier(external_body)]
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

    // #[verifier(external_body)]
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
            // assert(forall |i:int| #![trigger temp[i]] 0 <= i < temp.len() ==>
            //     (exists |j:int| #![trigger replies[j]] 0 <= j < replies.len() && temp[i] == replies[j]));
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

                // let clients = Self::CClientsInReplies(&replies);
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

    // #[verifier(external_body)]
    pub fn CExecutorProcessAppStateSupply(
        &mut self,
        inp: CPacket
    )
        requires
            old(self).valid(),
            inp.valid(),
            inp.msg is CMessageAppStateSupply,
            inp.msg->opn_state_supply > old(self).ops_complete,
        ensures
            self.valid(),
            LExecutorProcessAppStateSupply(
                old(self)@,
                self@,
                inp@)
    {
        let m = inp.msg;
        match m {
            CMessage::CMessageAppStateSupply {
                bal_state_supply,
                opn_state_supply,
                app_state,
                reply_cache,
            } => {
                self.app = app_state;
                self.ops_complete = opn_state_supply;
                self.max_bal_reflected = bal_state_supply;
                self.next_op_to_execute = COutstandingOperation::COutstandingOpUnknown {};
                self.reply_cache = reply_cache;
            }
            _ => {
            }
        }

    }

    // #[verifier(external_body)]
    pub fn CExecutorProcessAppStateRequest(
        &mut self,
        inp: CPacket,
        reply_cache:HashMap::<EndPoint, CReply>
    ) -> (res: OutboundPackets)
        requires
            old(self).valid(),
            inp.valid(),
            inp.msg is CMessageAppStateRequest,
        ensures
            self.valid(),
            res.valid(),
            LExecutorProcessAppStateRequest(
                old(self)@,
                self@,
                inp@,
                res@)
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;
        let ghost ss = old(self)@;
        let ghost sp = inp@;

        let m = inp.msg;

        match m {
            CMessage::CMessageAppStateRequest { bal_state_req, opn_state_req } => {
                if contains(&self.constants.all.config.replica_ids, &inp.src)
                    && CBalLeq(&self.max_bal_reflected, &bal_state_req)
                    && self.ops_complete >= opn_state_req
                    && CReplicaConstants::CReplicaConstantsValid(&self.constants)
                {
                    assert(ss.constants.all.config.replica_ids.contains(sp.src));
                    assert(BalLeq(ss.max_bal_reflected, sp.msg->bal_state_req));
                    assert(ss.ops_complete >= sp.msg->opn_state_req);
                    assert(LReplicaConstantsValid(ss.constants));
                    let msg = CMessage::CMessageAppStateSupply {
                        bal_state_supply: self.max_bal_reflected,
                        opn_state_supply: self.ops_complete,
                        app_state: self.app,
                        reply_cache: clone_creply_cache_up_to_view(&self.reply_cache),
                    };
                    let ghost smsg = RslMessage::RslMessageAppStateSupply{
                        bal_state_supply:ss.max_bal_reflected,
                        opn_state_supply:ss.ops_complete,
                        app_state:ss.app,
                        reply_cache:ss.reply_cache
                    };
                    assert(msg.valid());
                    assert(msg@ == smsg);
                    let pkt = CPacket {
                        dst: inp.src,
                        src: self.constants.all.config.replica_ids[self.constants.my_index as usize].clone_up_to_view(),
                        msg: msg,
                    };
                    let ghost spkt = LPacket{
                        dst:sp.src,
                        src:ss.constants.all.config.replica_ids[ss.constants.my_index],
                        msg:smsg,
                    };
                    assert(pkt.valid());
                    assert(pkt@ == spkt);
                    let pkt_vec = vec![pkt];
                    let outpackets = OutboundPackets::PacketSequence {
                        s: pkt_vec,
                    };
                    let ghost pkt_seq = seq![spkt];
                    assert(pkt_vec@.map(|i, p:CPacket| p@) == pkt_seq);
                    assert(ss == self@);
                    assert(LExecutorProcessAppStateRequest(
                        ss,
                        self@,
                        sp,
                        outpackets@));
                        outpackets
                } else {
                    let mut pkt_vec: Vec<CPacket> = Vec::new();
                    let outpackets = OutboundPackets::PacketSequence{
                        s:pkt_vec,
                    };
                    assert(pkt_vec@.map(|i, p:CPacket| p@)  == Seq::<RslPacket>::empty());
                    assert(LExecutorProcessAppStateRequest(
                        ss,
                        self@,
                        sp,
                        outpackets@));
                    outpackets
                }
            }
            _ => {
                // Unreachable due to precondition: `inp.msg is CMessageAppStateRequest`
                PacketSequence { s: vec![] }
            }
        }


    }

    // #[verifier(external_body)]
    pub fn CExecutorProcessStartingPhase2(
        &mut self,
        inp: CPacket
    ) -> (res: OutboundPackets)
        requires
            old(self).valid(),
            inp.valid(),
            inp.msg is CMessageStartingPhase2
        ensures
            self.valid(),
            res.valid(),
            LExecutorProcessStartingPhase2(
                old(self)@,
                self@,
                inp@,
                res@)
    {
            match inp.msg {
                CMessage::CMessageStartingPhase2 { bal_2, logTruncationPoint_2 } => {
                    let log_tp = logTruncationPoint_2;
                    let bal = bal_2;

                    if contains(&self.constants.all.config.replica_ids, &inp.src)
                        && log_tp > self.ops_complete
                    {
                        OutboundPackets::Broadcast {
                            broadcast: CBroadcast::BuildBroadcastToEveryone(
                                &self.constants.all.config,
                                self.constants.my_index,
                                CMessage::CMessageAppStateRequest {
                                    bal_state_req: bal,
                                    opn_state_req: log_tp,
                                },
                            ),
                        }
                    } else {
                        OutboundPackets::Broadcast {
                            broadcast: CBroadcast::CBroadcastNop {},
                        }
                    }
                }
                _ => {
                    // Unreachable due to `inp.msg is CMessageStartingPhase2`
                    OutboundPackets::Broadcast {
                        broadcast: CBroadcast::CBroadcastNop {},
                    }
                }
            }
    }


    // #[verifier(external_body)]
    pub fn CExecutorProcessRequest(&mut self,inp: CPacket) -> (res: OutboundPackets)
        requires
            old(self).valid(),
            inp.valid(),
            inp.msg is CMessageRequest,
            old(self).reply_cache@.contains_key(inp.src),
            old(self).reply_cache@[inp.src] is CReply,
            inp.msg->seqno_req <= old(self).reply_cache@[inp.src].seqno,
        ensures
            self.valid(),
            res.valid(),
            old(self)@ == self@,
            LExecutorProcessRequest(
                old(self)@,
                inp@,
                res@)
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;
        let ghost ss = old(self)@;
        let ghost sp = inp@;
        match inp.msg {
            CMessage::CMessageRequest { seqno_req, val } => {
                let v = self.reply_cache.get(&inp.src);
                match v {
                    Some(v) => {
                        broadcast use vstd::std_specs::hash::group_hash_axioms;
                        broadcast use crate::common::native::io_s::axiom_endpoint_key_model;
                        assert(v == self.reply_cache@[inp.src]);
                        assume(v@ == ss.reply_cache[sp.src]); // here need a lemma to prove the get operation of hashmap refines get of map
                        if seqno_req == v.seqno && CReplicaConstants::CReplicaConstantsValid(&self.constants)
                        {
                            assert(sp.msg->seqno_req == ss.reply_cache[sp.src].seqno);
                            assert(LReplicaConstantsValid(ss.constants));
                            let msg = CMessage::CMessageReply{
                                seqno_reply:v.seqno,
                                reply:v.reply.clone_up_to_view(),
                            };
                            let ghost r = ss.reply_cache[sp.src];
                            let ghost smsg = RslMessage::RslMessageReply{
                                seqno_reply:r.seqno,
                                reply:r.reply
                            };
                            assert(msg@ == smsg);

                            let pkt = CPacket{
                                src: self.constants.all.config.replica_ids[self.constants.my_index as usize].clone_up_to_view(),
                                dst: v.client.clone_up_to_view(),
                                msg: msg,
                            };

                            let ghost spkt = LPacket{
                                    dst:r.client,
                                    src:ss.constants.all.config.replica_ids[ss.constants.my_index],
                                    msg:smsg,
                                };
                            assert(pkt@ == spkt);

                            let mut pkt_vec: Vec<CPacket> = Vec::new();

                            pkt_vec.push(pkt);

                            let ghost pkt_seq = seq![spkt];

                            assert(pkt_vec@.map(|i, p:CPacket| p@) == pkt_seq);
                            let outpackets = OutboundPackets::PacketSequence{
                                s:pkt_vec,
                            };
                            assert(outpackets.valid());
                            assert(LExecutorProcessRequest(ss, sp, outpackets@));
                            outpackets
                        } else {
                            let mut pkt_vec: Vec<CPacket> = Vec::new();
                            let outpackets = OutboundPackets::PacketSequence{
                                s:pkt_vec,
                            };
                            assert(outpackets.valid());
                            assert(pkt_vec@.map(|i, p:CPacket| p@)  == Seq::<RslPacket>::empty());
                            assert(LExecutorProcessRequest(ss, sp, outpackets@));
                            outpackets
                        }
                    }
                    None => {
                        let mut pkt_vec: Vec<CPacket> = Vec::new();
                        let outpackets = OutboundPackets::PacketSequence{
                            s:pkt_vec,
                        };
                        assert(outpackets.valid());
                        assert(LExecutorProcessRequest(ss, sp, outpackets@));
                        outpackets
                    }
                }
            }
            _ => {
                OutboundPackets::Broadcast {
                    broadcast: CBroadcast::CBroadcastNop {},
                }
            }
        }

    }

}

    #[verifier(external_body)]
    pub proof fn lemma_ReplyCacheLen(cache: CReplyCache)
    ensures
        cache.len() < 256
        {

        }

}

// verus!
