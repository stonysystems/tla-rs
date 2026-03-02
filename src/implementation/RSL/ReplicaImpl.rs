use crate::common::collections::vecs::*;
use crate::common::framework::environment_s::{LIoOp, LPacket};
use crate::common::native::io_s::EndPoint;
use crate::generated::RSL::acceptor_gen as generated_acceptor;
use crate::generated::RSL::executor_gen as generated_executor;
use crate::generated::RSL::learner_gen as generated_learner;
use crate::generated::RSL::proposer_gen as generated_proposer;
use crate::generated::RSL::types_gen::CRslIo;
use crate::implementation::common::upper_bound::*;
use crate::implementation::common::upper_bound_i::*;
use crate::implementation::RSL::acceptorimpl::*;
use crate::implementation::RSL::cbroadcast::*;
use crate::implementation::RSL::cconstants::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::learnerimpl::*;
use crate::implementation::RSL::types_i::*;
use crate::implementation::RSL::ElectionImpl::COutstandingOperation;
use crate::implementation::RSL::ExecutorImpl::*;
use crate::implementation::RSL::ProposerImpl::*;
use crate::implementation::RSL::{cconfiguration::*, ProposerImpl::*};
use crate::protocol::common::upper_bound::*;
use crate::protocol::RSL::{
    acceptor::*, configuration::*, constants::*, executor::*, learner::*, message::*, proposer::*,
    types::*,
};
use crate::protocol::RSL::{environment::*, replica::*};
use std::collections::*;
use vstd::prelude::*;
use vstd::std_specs::hash::*;
use vstd::{map::*, map_lib::*, prelude::*, seq::*};

verus! {
    broadcast use crate::common::native::io_s::axiom_endpoint_key_model;

#[derive(Clone)]
pub struct CReplica {
    pub constants: CReplicaConstants,
    pub nextHeartbeatTime: u64,
    pub proposer: CProposer,
    pub acceptor: CAcceptor,
    pub learner: CLearner,
    pub executor: CExecutor,
}

impl CReplica{
    pub open spec fn valid(self) -> bool {
        self.abstractable()
        &&
        self.constants.valid()
        &&
        self.proposer.valid()
        &&
        self.acceptor.valid()
        &&
        self.learner.valid()
        &&
        self.executor.valid()
        &&
        self.constants@ == self.acceptor.constants@
        &&
        self.constants@ == self.proposer.constants@
        &&
        self.constants@ == self.learner.constants@
        &&
        self.constants@ == self.executor.constants@
    }

    pub open spec fn abstractable(self) -> bool{
        self.constants.abstractable()
        &&
        self.proposer.abstractable()
        &&
        self.acceptor.abstractable()
        &&
        self.learner.abstractable()
        &&
        self.executor.abstractable()
    }

    pub open spec fn view(self) -> LReplica
    recommends
        self.abstractable()
    {
        LReplica{
            constants:self.constants@,
            nextHeartbeatTime:self.nextHeartbeatTime as int,
            proposer:self.proposer@,
            acceptor:self.acceptor@,
            learner:self.learner@,
            executor:self.executor@
        }
    }
}

impl CReplica {
    #[verifier(external_body)]
    pub fn clone_up_to_view(&self) -> (result: Self)
        ensures
            self == result,
            result@ == self@,
            result.valid() == self.valid(),
    {
        self.clone()
    }
}

impl View for CReplica {
    type V = LReplica;

    open spec fn view(&self) -> LReplica {
        LReplica{
            constants:self.constants@,
            nextHeartbeatTime:self.nextHeartbeatTime as int,
            proposer:self.proposer@,
            acceptor:self.acceptor@,
            learner:self.learner@,
            executor:self.executor@
        }
    }
}

#[derive(Clone)]
pub struct CScheduler {
    pub replica: CReplica,
    pub nextActionIndex: u64,
}

impl CScheduler {
    pub open spec fn valid(&self) -> bool {
        &&& self.replica.valid()
        &&& 0 <= self.nextActionIndex < 10  // LReplicaNumActions() == 10
    }
}

impl View for CScheduler {
    type V = LScheduler;

    open spec fn view(&self) -> LScheduler {
        LScheduler {
            replica: self.replica@,
            nextActionIndex: self.nextActionIndex as int,
        }
    }
}

/// Convert a concrete LPacket<EndPoint, CMessage> to spec RslPacket
pub open spec fn abstractify_clpacket(p: LPacket<EndPoint, CMessage>) -> RslPacket {
    LPacket {
        dst: p.dst@,
        src: p.src@,
        msg: p.msg.view(),
    }
}

/// Convert a concrete CRslIo to spec RslIo
pub open spec fn abstractify_crslio(io: CRslIo) -> RslIo {
    match io {
        LIoOp::Send{s} => LIoOp::Send{s: abstractify_clpacket(s)},
        LIoOp::Receive{r} => LIoOp::Receive{r: abstractify_clpacket(r)},
        LIoOp::TimeoutReceive => LIoOp::TimeoutReceive,
        LIoOp::ReadClock{t} => LIoOp::ReadClock{t: t},
    }
}

/// Convert a sequence of CRslIo to Seq<RslIo>
pub open spec fn abstractify_crslio_seq(ios: Seq<CRslIo>) -> Seq<RslIo> {
    ios.map(|i, io: CRslIo| abstractify_crslio(io))
}

impl CReplica{


    pub fn CReplicaInit(c: CReplicaConstants) -> (result: Self)
        requires
            c.valid()
        ensures
            result.valid(),
            LReplicaInit(result@,c@)
    {
        let s = CReplica{
            constants: c.clone_up_to_view(),
            nextHeartbeatTime: 0,
            proposer: generated_proposer::CProposerInit(&c),
            acceptor: generated_acceptor::CAcceptorInit(&c),
            learner: generated_learner::CLearnerInit(&c),
            executor: generated_executor::CExecutorInit(&c)
        };
        s
    }


    pub fn CReplicaNextProcessInvalid(&mut self, received_packet: CPacket) -> (res: OutboundPackets)
        requires
            old(self).valid(),
            received_packet.valid(),
            received_packet.msg is CMessageInvalid,
        ensures
            self.valid(),
            res.valid(),
            LReplicaNextProcessInvalid(old(self)@,
            self@,
            received_packet@,
            res@)
    {
        let mut pkt_vec: Vec<CPacket> = Vec::new();
        let outpackets = OutboundPackets::PacketSequence{
            s:pkt_vec,
        };
        assert(self@ == old(self)@);
        assert(outpackets@ == Seq::<RslPacket>::empty());
        outpackets
    }


    pub fn CReplicaNextProcessRequest(&mut self, received_packet: CPacket) -> (res: OutboundPackets)
        requires
            old(self).valid(),
            received_packet.valid(),
            received_packet.msg is CMessageRequest
        ensures
            self.valid(),
            Replica_Common_Postconditions(old(self)@, *self, received_packet,res),
            res.valid(),
            LReplicaNextProcessRequest(old(self)@,
            self@,
            received_packet@,
            res@)
    {
        let ghost ss = old(self)@;
        let ghost sp = received_packet@;

        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;
        broadcast use crate::common::native::io_s::axiom_endpoint_key_model;

        match received_packet.msg {
            CMessage::CMessageRequest { seqno_req, .. } => {
                broadcast use vstd::std_specs::hash::group_hash_axioms;
                broadcast use vstd::hash_map::group_hash_map_axioms;
                broadcast use crate::common::native::io_s::axiom_endpoint_key_model;

                if self.executor.reply_cache.contains_key(&received_packet.src)
                {
                    assert(ss.executor.reply_cache.contains_key(sp.src));
                    let v = self.executor.reply_cache.get(&received_packet.src);
                    match v {
                        Some(v) => {
                            broadcast use vstd::std_specs::hash::group_hash_axioms;
                            broadcast use crate::common::native::io_s::axiom_endpoint_key_model;
                            assert(received_packet.src@ == sp.src);
                            proof {
                                broadcast use crate::common::native::io_s::axiom_endpoint_view;
                                // HashMap::get gives *v == m@[received_packet.src], so v@ == m@[received_packet.src]@
                                // abstractify_creplycache uses choose |k| m@.contains_key(k) && k@ == sp.src
                                // By axiom_endpoint_view (k@ == received_packet.src@ ==> k == received_packet.src),
                                // the chosen k must be received_packet.src
                                let m = self.executor.reply_cache;
                                assert(m@.contains_key(received_packet.src) && received_packet.src@ == sp.src);
                                let k = choose |k: EndPoint| m@.contains_key(k) && k@ == sp.src;
                                assert(k@ == received_packet.src@);
                                assert(k == received_packet.src);
                            }
                            if v.seqno >= seqno_req {
                                assert(ss.executor.reply_cache.contains_key(sp.src));
                                assert(sp.msg->seqno_req <= ss.executor.reply_cache[sp.src].seqno);
                                let sent_packets = generated_executor::CExecutorProcessRequest(&self.executor, &received_packet);
                                assert(forall |i:int| 0 <= i < sent_packets@.len() ==> sent_packets@[i].valid());
                                assert(forall |i:int| 0 <= i < sent_packets@.len() ==> sent_packets@[i].abstractable());
                                let outpackets = OutboundPackets::PacketSequence { s: sent_packets };
                                assert(outpackets.valid());
                                assert(outpackets.abstractable());
                                assert(ss == self@);
                                assert(LExecutorProcessRequest(ss.executor, sp, outpackets@));
                                assert(LReplicaNextProcessRequest(ss, self@, sp, outpackets@));
                                outpackets
                            }
                            else
                            {
                                assert(ss.executor.reply_cache.contains_key(sp.src));
                                assert(sp.msg->seqno_req > ss.executor.reply_cache[sp.src].seqno);

                                self.proposer = generated_proposer::CProposerProcessRequest(&self.proposer, &received_packet);

                                let mut pkt_vec: Vec<CPacket> = Vec::new();
                                let outpackets = OutboundPackets::PacketSequence{
                                    s:pkt_vec,
                                };
                                assert(LProposerProcessRequest(ss.proposer, self@.proposer, sp));
                                assert(self@ == LReplica {
                                    constants:ss.constants,
                                    nextHeartbeatTime:ss.nextHeartbeatTime,
                                    proposer:self@.proposer,
                                    acceptor:ss.acceptor,
                                    learner:ss.learner,
                                    executor:ss.executor
                                });
                                assert(outpackets@ == Seq::<RslPacket>::empty());
                                assert(LReplicaNextProcessRequest(ss, self@, sp, outpackets@));
                                outpackets
                            }
                        }
                        None => {
                            let mut pkt_vec: Vec<CPacket> = Vec::new();
                            let outpackets = OutboundPackets::PacketSequence{
                                s:pkt_vec,
                            };
                            assert(LReplicaNextProcessRequest(ss, self@, sp, outpackets@));
                            outpackets
                        }
                    }
                } else {
                    proof {
                        broadcast use crate::common::native::io_s::axiom_endpoint_view;
                        // HashMap::contains_key returned false: !m@.contains_key(received_packet.src)
                        // Need: !abstractify_creplycache(&m).contains_key(sp.src)
                        // abstractify domain: exists |k: EndPoint| m@.contains_key(k) && k@ == sp.src
                        // By contradiction: any witness k with k@ == sp.src must be received_packet.src
                        // (axiom_endpoint_view), but !m@.contains_key(received_packet.src)
                        let m = self.executor.reply_cache;
                        assert(!abstractify_creplycache(&m).contains_key(sp.src)) by {
                            if abstractify_creplycache(&m).contains_key(sp.src) {
                                let k = choose |k: EndPoint| m@.contains_key(k) && k@ == sp.src;
                                assert(k@ == received_packet.src@);
                                assert(k == received_packet.src);
                                assert(m@.contains_key(received_packet.src)); // contradiction
                            }
                        };
                    }
                    // Self::print("receive request");
                    self.proposer = generated_proposer::CProposerProcessRequest(&self.proposer, &received_packet);
                    let mut pkt_vec: Vec<CPacket> = Vec::new();
                    let outpackets = OutboundPackets::PacketSequence{
                        s:pkt_vec,
                    };
                    assert(outpackets@ == Seq::<RslPacket>::empty());
                    assert(LReplicaNextProcessRequest(ss, self@, sp, outpackets@));
                    outpackets
                }
            }
            _ => {
                let mut pkt_vec: Vec<CPacket> = Vec::new();
                let outpackets = OutboundPackets::PacketSequence{
                    s:pkt_vec,
                };
                assert(LReplicaNextProcessRequest(ss, self@, sp, outpackets@));
                outpackets
            } // Shouldn't happen due to precondition
        }

    }


    pub fn CReplicaNextProcess1a(&mut self, received_packet: CPacket ) -> (res: OutboundPackets)
        requires
            old(self).valid(),
            received_packet.valid(),
            received_packet.msg is CMessage1a
        ensures
            self.valid(),
            Replica_Common_Postconditions(old(self)@, *self, received_packet,res),
            res.valid(),
            LReplicaNextProcess1a(old(self)@,
            self@,
            received_packet@,
            res@)
    {
        let ghost ss = old(self)@;
        let ghost sp = received_packet@;

        let (next_acceptor, sent_packets) =
            generated_acceptor::CAcceptorProcess1a(&self.acceptor, &received_packet);
        self.acceptor = next_acceptor;
        assert(forall |i:int| 0 <= i < sent_packets@.len() ==> sent_packets@[i].valid());
        assert(forall |i:int| 0 <= i < sent_packets@.len() ==> sent_packets@[i].abstractable());
        let outpackets = OutboundPackets::PacketSequence { s: sent_packets };
        assert(outpackets.valid());
        assert(outpackets.abstractable());
        assert(LReplicaNextProcess1a(ss, self@, sp, outpackets@));
        outpackets

    }

    #[verifier(external_body)]
    pub fn Packet1bHasUniqueSrc(s:&HashSet<CPacket>, pkt:&CPacket) -> (res:bool)
        requires
            // forall |p:CPacket| s@.contains(p) ==> p.msg is CMessage1b,
            pkt.msg is CMessage1b,
        ensures
            res == (forall |op:CPacket| s@.contains(op) ==> op.src@ != pkt.src@)
    {
        let mut res = true;
        let m_iter = s.iter();
        assert(m_iter@.0 == 0);

        for p in iter: m_iter
        {
            if p.src == pkt.src {
                res = false;
            }
        }
        res
    }

    #[verifier::external_body]
    pub fn print(s: &str) {
        println!("{}", s);
    }


    pub fn CReplicaNextProcess1b(&mut self, received_packet:CPacket ) -> (res: OutboundPackets)
        requires
            old(self).valid(),
            received_packet.valid(),
            received_packet.msg is CMessage1b
        ensures
            self.valid(),
            Replica_Common_Postconditions(old(self)@,*self, received_packet,res),
            res.valid(),
            LReplicaNextProcess1b(
                old(self)@,
                self@,
                received_packet@,
                res@)
    {
        let ghost ss = old(self)@;
        let ghost sp = received_packet@;

        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;
        broadcast use crate::common::native::io_s::axiom_endpoint_key_model;

        match received_packet.msg {
            CMessage::CMessage1b { bal_1b, log_truncation_point, .. } => {
                let samesrc = Self::Packet1bHasUniqueSrc(&self.proposer.received_1b_packets, &received_packet);
                // Pre-compute all sub-conditions so their postconditions are available
                // in both if and else branches (avoids short-circuit postcondition loss).
                let in_config = contains(&self.proposer.constants.all.config.replica_ids, &received_packet.src);
                let bal_eq = CBalEq(&bal_1b, &self.proposer.max_ballot_i_sent_1a);
                let state_ok = self.proposer.current_state == 1;

                if in_config && bal_eq && state_ok && samesrc
                {
                    Self::print("receive valid 1b");
                    assert(ss.proposer.constants.all.config.replica_ids.contains(sp.src));
                    assert(sp.msg->bal_1b == ss.proposer.max_ballot_i_sent_1a);
                    assert(ss.proposer.current_state == 1);
                    assert(forall |op:RslPacket| ss.proposer.received_1b_packets.contains(op) ==> op.src != sp.src);
                    self.acceptor = generated_acceptor::CAcceptorTruncateLog(
                        &self.acceptor,
                        &log_truncation_point,
                    );
                    self.proposer = generated_proposer::CProposerProcess1b(&self.proposer, &received_packet);
                    let mut pkt_vec: Vec<CPacket> = Vec::new();
                    let outpackets = OutboundPackets::PacketSequence{
                        s:pkt_vec,
                    };
                    let ghost ns = self@;
                    assert(LProposerProcess1b(ss.proposer, ns.proposer, sp));
                    assert(LAcceptorTruncateLog(ss.acceptor, ns.acceptor, sp.msg->log_truncation_point));
                    assert(outpackets@ == Seq::<RslPacket>::empty());
                    assert(LReplicaNextProcess1b(ss, self@, sp, outpackets@));
                    outpackets
                }
                else
                {
                    // Ensure spec-level message type is known
                    assert(sp.msg is RslMessage1b);
                    // Bridge exec sub-conditions to spec equivalents:
                    // contains() postcondition: in_config == v@.map(|i,t:EndPoint| t@).contains(received_packet.src@)
                    assert(in_config == ss.proposer.constants.all.config.replica_ids.contains(sp.src));
                    // CBalEq postcondition: bal_eq == (bal_1b@ == max_ballot@)
                    assert(bal_eq == (sp.msg->bal_1b == ss.proposer.max_ballot_i_sent_1a));
                    // state comparison is identity
                    assert(state_ok == (ss.proposer.current_state == 1));
                    // Bridge samesrc (exec forall over CPacket) to spec forall (over RslPacket)
                    // via Set::map: spec_set == exec_set@.map(|p:CPacket| p@)
                    proof {
                        let exec_set = self.proposer.received_1b_packets@;
                        let spec_set = ss.proposer.received_1b_packets;
                        // Establish the set equivalence via CProposer view mapping
                        assert(exec_set.map(|p: CPacket| p@) =~= spec_set);

                        if samesrc {
                            // samesrc == true → forall CPacket op in exec_set: op.src@ != pkt.src@
                            // Bridge to spec forall via Set::map
                            assert forall |rp: RslPacket| spec_set.contains(rp) implies rp.src != sp.src by {
                                // spec_set.contains(rp) → exec_set.map(|p| p@).contains(rp)
                                // → exists |op| exec_set.contains(op) && op@ == rp
                                let op = choose |op: CPacket| exec_set.contains(op) && op@ == rp;
                                assert(exec_set.contains(op));
                                // rp.src = op@.src = op.src@, which != pkt.src@ = sp.src
                            };
                        } else {
                            // samesrc == false → exists op in exec_set: op.src@ == pkt.src@
                            let bad_op = choose |op: CPacket| exec_set.contains(op) && !(op.src@ != received_packet.src@);
                            assert(exec_set.contains(bad_op));
                            // bad_op@ is in spec_set via Set::map
                            assert(spec_set.contains(bad_op@));
                            assert(bad_op@.src == sp.src);
                            assert(!(forall |rp: RslPacket| spec_set.contains(rp) ==> rp.src != sp.src));
                        }
                    }
                    let mut pkt_vec: Vec<CPacket> = Vec::new();
                    let outpackets = OutboundPackets::PacketSequence{
                        s:pkt_vec,
                    };
                    assert(ss == self@);
                    assert(outpackets@ == Seq::<RslPacket>::empty());
                    assert(LReplicaNextProcess1b(ss, self@, sp, outpackets@));
                    outpackets
                }
            }
            _ => {
                let mut pkt_vec: Vec<CPacket> = Vec::new();
                let outpackets = OutboundPackets::PacketSequence{
                    s:pkt_vec,
                };
                assert(outpackets@ == Seq::<RslPacket>::empty());
                assert(LReplicaNextProcess1b(ss, self@, sp, outpackets@));
                outpackets
            }
        }
    }


    pub fn CReplicaNextProcessStartingPhase2(&mut self, received_packet: CPacket ) -> (res: OutboundPackets)
        requires
            old(self).valid(),
            received_packet.valid(),
            received_packet.msg is CMessageStartingPhase2
        ensures
            self.valid(),
            Replica_Common_Postconditions(old(self)@,*self, received_packet,res),
            res.valid(),
            LReplicaNextProcessStartingPhase2(old(self)@,
            self@,
            received_packet@,
            res@)
    {
        let (next_executor, sent_packets) =
            generated_executor::CExecutorProcessStartingPhase2(&self.executor, &received_packet);
        self.executor = next_executor;
        assert(forall |i:int| 0 <= i < sent_packets@.len() ==> sent_packets@[i].valid());
        assert(forall |i:int| 0 <= i < sent_packets@.len() ==> sent_packets@[i].abstractable());
        let outpackets = OutboundPackets::PacketSequence { s: sent_packets };
        assert(outpackets.valid());
        assert(outpackets.abstractable());
        outpackets
    }


    pub fn CReplicaNextProcess2a(&mut self, received_packet: CPacket ) -> (res: OutboundPackets)
        requires
            old(self).valid(),
            received_packet.valid(),
            received_packet.msg is CMessage2a
        ensures
            self.valid(),
            Replica_Common_Postconditions(old(self)@,*self, received_packet,res),
            res.valid(),
            LReplicaNextProcess2a(old(self)@,
            self@,
            received_packet@,
            res@)
    {
        let ghost ss = old(self)@;
        let ghost sp = received_packet@;
        match received_packet.msg {
            CMessage::CMessage2a { bal_2a, opn_2a, .. } => {
                if contains(&self.proposer.constants.all.config.replica_ids, &received_packet.src)
                    && CBalLeq(&self.acceptor.max_bal, &bal_2a)
                    && opn_2a <= self.acceptor.constants.all.params.max_integer_val
                {
                    assert(ss.constants.all.config.replica_ids.contains(sp.src));
                    assert(BalLeq(ss.acceptor.max_bal, sp.msg->bal_2a));
                    assert(LeqUpperBound(sp.msg->opn_2a, ss.acceptor.constants.all.params.max_integer_val));
                    let (next_acceptor, sent_packets) =
                        generated_acceptor::CAcceptorProcess2a(&self.acceptor, &received_packet);
                    self.acceptor = next_acceptor;
                    assert(forall |i:int| 0 <= i < sent_packets@.len() ==> sent_packets@[i].valid());
                    assert(forall |i:int| 0 <= i < sent_packets@.len() ==> sent_packets@[i].abstractable());
                    let outpackets = OutboundPackets::PacketSequence { s: sent_packets };
                    assert(outpackets.valid());
                    assert(outpackets.abstractable());
                    // let outpackets = self.acceptor.CAcceptorProcess2a_optimized(received_packet);
                    assert(LReplicaNextProcess2a(ss, self@, sp, outpackets@));
                    outpackets
                } else {
                    let mut pkt_vec: Vec<CPacket> = Vec::new();
                    let outpackets = OutboundPackets::PacketSequence{
                        s:pkt_vec,
                    };
                    assert(outpackets@ == Seq::<RslPacket>::empty());
                    assert(LReplicaNextProcess2a(ss, self@, sp, outpackets@));
                    outpackets
                }
            }
            _ => {
                let mut pkt_vec: Vec<CPacket> = Vec::new();
                let outpackets = OutboundPackets::PacketSequence{
                    s:pkt_vec,
                };
                assert(LReplicaNextProcess2a(ss, self@, sp, outpackets@));
                outpackets
            }
        }

    }


    pub fn CReplicaNextProcess2b(&mut self, received_packet: CPacket ) -> (res: OutboundPackets)
        requires
            old(self).valid(),
            received_packet.valid(),
            received_packet.msg is CMessage2b
        ensures
            self.valid(),
            Replica_Common_Postconditions(old(self)@,*self, received_packet,res),
            res.valid(),
            LReplicaNextProcess2b(old(self)@,
            self@,
            received_packet@,
            res@)
    {
        match received_packet.msg {
            CMessage::CMessage2b { opn_2b, .. } => {
                match &self.executor.next_op_to_execute {
                    COutstandingOperation::COutstandingOpUnknown{} => {
                        if self.executor.ops_complete < opn_2b || self.executor.ops_complete == opn_2b{
                            self.learner = generated_learner::CLearnerProcess2b(&self.learner, &received_packet);
                        }
                    }
                    COutstandingOperation::COutstandingOpKnown{v, bal} => {
                        if self.executor.ops_complete < opn_2b {
                            self.learner = generated_learner::CLearnerProcess2b(&self.learner, &received_packet);
                        }
                    }
                }
                let mut pkt_vec: Vec<CPacket> = Vec::new();
                let outpackets = OutboundPackets::PacketSequence{
                    s:pkt_vec,
                };
                assert(outpackets@ == Seq::<RslPacket>::empty());

                outpackets
            }
            _ => {
                let mut pkt_vec: Vec<CPacket> = Vec::new();
                let outpackets = OutboundPackets::PacketSequence{
                    s:pkt_vec,
                };
                assert(outpackets@ == Seq::<RslPacket>::empty());

                outpackets
            }
        }

    }


    pub fn CReplicaNextProcessReply(&mut self, received_packet: CPacket ) -> (res: OutboundPackets)
        requires
            old(self).valid(),
            received_packet.valid(),
            received_packet.msg is CMessageReply
        ensures
            self.valid(),
            Replica_Common_Postconditions(old(self)@,*self, received_packet,res),
            res.valid(),
            LReplicaNextProcessReply(old(self)@,
            self@,
            received_packet@,
            res@)
    {
        let mut pkt_vec: Vec<CPacket> = Vec::new();
        let outpackets = OutboundPackets::PacketSequence{
            s:pkt_vec,
        };
        assert(outpackets@ == Seq::<RslPacket>::empty());

        outpackets
    }


    pub fn CReplicaNextProcessAppStateSupply(&mut self, received_packet: CPacket ) -> (res: OutboundPackets)
        requires
            old(self).valid(),
            received_packet.valid(),
            received_packet.msg is CMessageAppStateSupply
        ensures
            self.valid(),
            Replica_Common_Postconditions(old(self)@,*self, received_packet,res),
            res.valid(),
            LReplicaNextProcessAppStateSupply(old(self)@,
            self@,
            received_packet@,
            res@)
    {
        match received_packet.msg {
            CMessage::CMessageAppStateSupply { opn_state_supply, .. } => {
                if contains(&self.executor.constants.all.config.replica_ids, &received_packet.src)
                    && opn_state_supply > self.executor.ops_complete
                {
                    self.learner = generated_learner::CLearnerForgetOperationsBefore(&self.learner, &opn_state_supply);
                    self.executor = generated_executor::CExecutorProcessAppStateSupply(&self.executor, &received_packet);
                }

                let mut pkt_vec: Vec<CPacket> = Vec::new();
                let outpackets = OutboundPackets::PacketSequence{
                    s:pkt_vec,
                };
                assert(outpackets@ == Seq::<RslPacket>::empty());

                outpackets
            }
            _ => {
                let mut pkt_vec: Vec<CPacket> = Vec::new();
                let outpackets = OutboundPackets::PacketSequence{
                    s:pkt_vec,
                };
                assert(outpackets@ == Seq::<RslPacket>::empty());

                outpackets
            }
        }
    }


    pub fn CReplicaNextProcessAppStateRequest(&mut self, received_packet: CPacket ) -> (res: OutboundPackets)
        requires
            old(self).valid(),
            received_packet.valid(),
            received_packet.msg is CMessageAppStateRequest
        ensures
            self.valid(),
            Replica_Common_Postconditions(old(self)@,*self, received_packet,res),
            res.valid(),
            LReplicaNextProcessAppStateRequest(old(self)@,
            self@,
            received_packet@,
            res@)
    {
        let (next_executor, sent_packets) =
            generated_executor::CExecutorProcessAppStateRequest(&self.executor, &received_packet);
        self.executor = next_executor;
        assert(forall |i:int| 0 <= i < sent_packets@.len() ==> sent_packets@[i].valid());
        assert(forall |i:int| 0 <= i < sent_packets@.len() ==> sent_packets@[i].abstractable());
        let outpackets = OutboundPackets::PacketSequence { s: sent_packets };
        assert(outpackets.valid());
        assert(outpackets.abstractable());
        outpackets
    }


    pub fn CReplicaNextProcessHeartbeat(&mut self, received_packet: CPacket ,clock: u64) -> (res: OutboundPackets)
        requires
            old(self).valid(),
            received_packet.valid(),
            received_packet.msg is CMessageHeartbeat
        ensures
            self.valid(),
            Replica_Common_Postconditions(old(self)@,*self, received_packet,res),
            res.valid(),
            LReplicaNextProcessHeartbeat(old(self)@,
            self@,
            received_packet@,
            clock as int,
            res@)
    {
        self.proposer = generated_proposer::CProposerProcessHeartbeat(&self.proposer, &received_packet, &clock);
        self.acceptor =
            generated_acceptor::CAcceptorProcessHeartbeat(&self.acceptor, &received_packet);
        let mut pkt_vec: Vec<CPacket> = Vec::new();
        let outpackets = OutboundPackets::PacketSequence{
            s:pkt_vec,
        };
        assert(outpackets@ == Seq::<RslPacket>::empty());

        outpackets
    }


    pub fn CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(&mut self) -> (res: OutboundPackets)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            Replica_Common_Postconditions_NoPacket(old(self)@,*self,res),
            res.valid(),
            LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(old(self)@,
            self@,
            res@)
    {
        let (next_proposer, sent_packets) = generated_proposer::CProposerMaybeEnterNewViewAndSend1a(&self.proposer);
        self.proposer = next_proposer;
        let res = OutboundPackets::PacketSequence { s: sent_packets };
        res
    }


    pub fn CReplicaNextSpontaneousMaybeEnterPhase2(&mut self) -> (res: OutboundPackets)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            Replica_Common_Postconditions_NoPacket(old(self)@,*self,res),
            res.valid(),
            LReplicaNextSpontaneousMaybeEnterPhase2(old(self)@,
            self@,
            res@)
    {
        let (next_proposer, sent_packets) = generated_proposer::CProposerMaybeEnterPhase2(&self.proposer, &self.acceptor.log_truncation_point);
        self.proposer = next_proposer;
        let res = OutboundPackets::PacketSequence { s: sent_packets };
        res
    }


    pub fn CReplicaNextSpontaneousMaybeMakeDecision(&mut self) -> (res: OutboundPackets)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            Replica_Common_Postconditions_NoPacket(old(self)@,*self,res),
            res.valid(),
            LReplicaNextSpontaneousMaybeMakeDecision(old(self)@,
            self@,
            res@)
    {
        let ghost ss = old(self)@;
        assert(self.learner.valid());
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;
        let opn = self.executor.ops_complete;
        match &self.executor.next_op_to_execute {
            COutstandingOperation::COutstandingOpUnknown{} => {
                assert(clearnerstate_is_valid(self.learner.unexecuted_learner_state));
                // clearnerstate_is_valid provides: forall |i| #![auto] m@.contains_key(i) ==> COperationNumberIsValid(i) && m@[i].valid()
                // Re-derive with explicit trigger to ensure SMT matches:
                proof {
                    let m = self.learner.unexecuted_learner_state;
                    assert forall |i: COperationNumber| m@.contains_key(i) implies COperationNumberIsValid(i) && (#[trigger] m@[i]).valid() by {
                        assert(clearnerstate_is_valid(m));
                        let ghost _ = m@[i];
                        let ghost _ = COperationNumberIsValid(i);
                    };
                }
                if self.learner.unexecuted_learner_state.contains_key(&opn) {
                    let v = self.learner.unexecuted_learner_state.get(&opn);
                    match v {
                        Some(v) => {
                            broadcast use vstd::std_specs::hash::group_hash_axioms;
                            assert(ss.learner.unexecuted_learner_state.contains_key(opn as int));
                            assert(v@ == ss.learner.unexecuted_learner_state[opn as int]);
                            assert(v.valid());
                            let quorum = self.learner.constants.all.config.CMinQuorumSize();
                            if v.received_2b_message_senders.len() >= quorum {
                                assert(ss.executor.next_op_to_execute is OutstandingOpUnknown);
                                assert(ss.learner.unexecuted_learner_state.contains_key(opn as int));
                                assert(quorum as int == LMinQuorumSize(ss.learner.constants.all.config));
                                assert(self.learner.unexecuted_learner_state@[opn]@ == ss.learner.unexecuted_learner_state[opn as int]);
                                // Bridge EndPoint set cardinality: HashSet<EndPoint>.len() == Set<AbstractEndPoint>.len()
                                proof {
                                    crate::common::collections::hashsets::lemma_set_view_map_len::<EndPoint>(v.received_2b_message_senders@);
                                }
                                assert(ss.learner.unexecuted_learner_state[opn as int].received_2b_message_senders.len() >= LMinQuorumSize(ss.learner.constants.all.config));
                                self.executor = generated_executor::CExecutorGetDecision(
                                    &self.executor, &self.learner.max_ballot_seen, &opn, &v.candidate_learned_value
                                );
                                let mut pkt_vec: Vec<CPacket> = Vec::new();
                                let outpackets = OutboundPackets::PacketSequence{
                                    s:pkt_vec,
                                };
                                assert(outpackets@ == Seq::<RslPacket>::empty());
                                assert(LReplicaNextSpontaneousMaybeMakeDecision(ss, self@, outpackets@));
                                outpackets
                            }
                            else {
                                proof {
                                    crate::common::collections::hashsets::lemma_set_view_map_len::<EndPoint>(v.received_2b_message_senders@);
                                }
                                let mut pkt_vec: Vec<CPacket> = Vec::new();
                                let outpackets = OutboundPackets::PacketSequence{
                                    s:pkt_vec,
                                };
                                assert(outpackets@ == Seq::<RslPacket>::empty());
                                assert(LReplicaNextSpontaneousMaybeMakeDecision(ss, self@, outpackets@));
                                outpackets
                            }
                        }
                        None => {
                            let mut pkt_vec: Vec<CPacket> = Vec::new();
                            let outpackets = OutboundPackets::PacketSequence{
                                s:pkt_vec,
                            };
                            assert(outpackets@ == Seq::<RslPacket>::empty());
                            assert(LReplicaNextSpontaneousMaybeMakeDecision(ss, self@, outpackets@));
                            outpackets
                        }
                    }
                } else {
                    let mut pkt_vec: Vec<CPacket> = Vec::new();
                    let outpackets = OutboundPackets::PacketSequence{
                        s:pkt_vec,
                    };
                    assert(outpackets@ == Seq::<RslPacket>::empty());
                    assert(LReplicaNextSpontaneousMaybeMakeDecision(ss, self@, outpackets@));
                    outpackets
                }
            }
            COutstandingOperation::COutstandingOpKnown{v, bal} => {
                let mut pkt_vec: Vec<CPacket> = Vec::new();
                let outpackets = OutboundPackets::PacketSequence{
                    s:pkt_vec,
                };
                assert(outpackets@ == Seq::<RslPacket>::empty());

                outpackets
            }
        }
    }


    pub fn CReplicaNextSpontaneousMaybeExecute(&mut self) -> (res: OutboundPackets)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            Replica_Common_Postconditions_NoPacket(old(self)@,*self,res),
            res.valid(),
            LReplicaNextSpontaneousMaybeExecute(old(self)@,
            self@,
            res@)
    {
        match &self.executor.next_op_to_execute {
            COutstandingOperation::COutstandingOpKnown { v,.. } => {
                if self.executor.ops_complete < self.executor.constants.all.params.max_integer_val
                    && self.executor.constants.CReplicaConstantsValid()
                {
                    self.proposer = generated_proposer::CProposerResetViewTimerDueToExecution(&self.proposer, &v);
                    self.learner = generated_learner::CLearnerForgetDecision(&self.learner, &self.executor.ops_complete);
                    self.executor.CExecutorExecute()
                } else {
                    let mut pkt_vec: Vec<CPacket> = Vec::new();
                    let outpackets = OutboundPackets::PacketSequence{
                        s:pkt_vec,
                    };
                    assert(outpackets@ == Seq::<RslPacket>::empty());

                    outpackets
                }
            }
            _ => {
                let mut pkt_vec: Vec<CPacket> = Vec::new();
                let outpackets = OutboundPackets::PacketSequence{
                    s:pkt_vec,
                };
                assert(outpackets@ == Seq::<RslPacket>::empty());

                outpackets
            }
        }
    }


    pub fn CReplicaNextReadClockMaybeSendHeartbeat(&mut self, clock: u64) -> (res: OutboundPackets)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            Replica_Common_Postconditions_NoPacket(old(self)@,*self,res),
            res.valid(),
            LReplicaNextReadClockMaybeSendHeartbeat(old(self)@,
            self@,
            ClockReading{t: clock as int},
            res@)
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;
        let ghost ss = old(self)@;
        let ghost sclock = ClockReading{t: clock as int};
        if clock < self.nextHeartbeatTime{
            let mut pkt_vec: Vec<CPacket> = Vec::new();
            let outpackets = OutboundPackets::PacketSequence{
                s:pkt_vec,
            };
            assert(outpackets@ == Seq::<RslPacket>::empty());
            assert(LReplicaNextReadClockMaybeSendHeartbeat(ss, self@, sclock, outpackets@));
            outpackets
        } else {
            let t = CUpperBoundedAddition(clock, self.constants.all.params.heartbeat_period, self.constants.all.params.max_integer_val);
            self.nextHeartbeatTime = t;
            let msg = CMessage::CMessageHeartbeat {
                bal_heartbeat: self.proposer.election_state.current_view,
                suspicious: self.proposer.election_state.current_view_suspectors.contains(&self.constants.my_index),
                opn_ckpt: self.executor.ops_complete
            };
            let broadcast = CBroadcast::BuildBroadcastToEveryone(&self.constants.all.config, self.constants.my_index, msg);
            let outpackets = OutboundPackets::Broadcast{broadcast:broadcast};
            let ghost ns = self@;
            assert(ns.nextHeartbeatTime == UpperBoundedAddition(sclock.t, ss.constants.all.params.heartbeat_period, ss.constants.all.params.max_integer_val));
            assert(LReplicaNextReadClockMaybeSendHeartbeat(ss, self@, sclock, outpackets@));
            outpackets
        }

    }


    pub fn CReplicaNextReadClockCheckForViewTimeout(&mut self, clock: u64) -> (res: OutboundPackets)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            Replica_Common_Postconditions_NoPacket(old(self)@,*self,res),
            res.valid(),
            LReplicaNextReadClockCheckForViewTimeout(old(self)@,
            self@,
            ClockReading{t: clock as int},
            res@)
    {
        self.proposer = generated_proposer::CProposerCheckForViewTimeout(&self.proposer, &clock);
        let mut pkt_vec: Vec<CPacket> = Vec::new();
        let outpackets = OutboundPackets::PacketSequence{
            s:pkt_vec,
        };
        assert(outpackets@ == Seq::<RslPacket>::empty());

        outpackets
    }


    pub fn CReplicaNextReadClockCheckForQuorumOfViewSuspicions(&mut self, clock: u64) -> (res: OutboundPackets)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            Replica_Common_Postconditions_NoPacket(old(self)@,*self,res),
            res.valid(),
            LReplicaNextReadClockCheckForQuorumOfViewSuspicions(old(self)@,
            self@,
            ClockReading{t: clock as int},
            res@)
    {
        self.proposer = generated_proposer::CProposerCheckForQuorumOfViewSuspicions(&self.proposer, &clock);
        let mut pkt_vec: Vec<CPacket> = Vec::new();
        let outpackets = OutboundPackets::PacketSequence{
            s:pkt_vec,
        };
        assert(outpackets@ == Seq::<RslPacket>::empty());

        outpackets
    }


    pub fn CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(&mut self) -> (res:OutboundPackets)
        requires
            old(self).valid()
        ensures
            self.valid(),
            Replica_Common_Postconditions_NoPacket(old(self)@,*self,res),
            res.valid(),
            LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(
                old(self)@,
                self@,
                res@)
    {
        let ghost ss = old(self)@;
        assert(self.valid());
        assert(self.constants.all.config.valid());
        let mut i = 0;
        let mut find = false;
        let mut target = 0;
        while i < self.acceptor.last_checkpointed_operation.len()
            invariant
                self.valid(),
                ss == self@,
                find ==> ss.acceptor.last_checkpointed_operation.contains(target as int),
                find ==> IsLogTruncationPointValid(target as int, ss.acceptor.last_checkpointed_operation, ss.constants.all.config),
            decreases self.acceptor.last_checkpointed_operation.len() - i
        {
            let opn = self.acceptor.last_checkpointed_operation[i];
            assert(self.acceptor.last_checkpointed_operation@.contains(opn));
            if CIsLogTruncationPointValid(opn, &self.acceptor.last_checkpointed_operation, &self.constants.all.config)
            {
                find = true;
                target = opn;
                assert(self.acceptor.last_checkpointed_operation@.contains(target));
                let valid = CIsLogTruncationPointValid(target, &self.acceptor.last_checkpointed_operation, &self.constants.all.config);
                assert(valid == true);
                assert(valid == IsLogTruncationPointValid(target as int, self.acceptor.last_checkpointed_operation@.map(|i, x| (x as int)), self.constants.all.config@));
                assert(ss.acceptor.last_checkpointed_operation == self.acceptor.last_checkpointed_operation@.map(|i, x| (x as int)));
                assert(ss.constants.all.config == self.constants.all.config@);
                assert(ss.acceptor.last_checkpointed_operation.contains(target as int));
                assert(IsLogTruncationPointValid(target as int, ss.acceptor.last_checkpointed_operation, ss.constants.all.config));
                break;
            }
            i = i + 1;
        }

        if find {
            if target > self.acceptor.log_truncation_point{
                assert(ss.acceptor.last_checkpointed_operation.contains(target as int)
                        && IsLogTruncationPointValid(target as int, ss.acceptor.last_checkpointed_operation, ss.constants.all.config));

                assert(target as int > ss.acceptor.log_truncation_point);
                assert(exists |op:OperationNumber| ss.acceptor.last_checkpointed_operation.contains(op)
                            && IsLogTruncationPointValid(op, ss.acceptor.last_checkpointed_operation, ss.constants.all.config)
                            && op > ss.acceptor.log_truncation_point);
                self.acceptor =
                    generated_acceptor::CAcceptorTruncateLog(&self.acceptor, &target);
                let mut pkt_vec: Vec<CPacket> = Vec::new();
                let outpackets = OutboundPackets::PacketSequence{
                    s:pkt_vec,
                };
                assert(outpackets@ == Seq::<RslPacket>::empty());
                assert(LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(ss, self@, outpackets@));
                outpackets
            } else {
                let mut pkt_vec: Vec<CPacket> = Vec::new();
                let outpackets = OutboundPackets::PacketSequence{
                    s:pkt_vec,
                };
                assert(outpackets@ == Seq::<RslPacket>::empty());
                assert(LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(ss, self@, outpackets@));
                outpackets
            }
        }
        else {
            // this brunch cannot be reached, use assume to pass the verification.
            let mut pkt_vec: Vec<CPacket> = Vec::new();
            let outpackets = OutboundPackets::PacketSequence{
                s:pkt_vec,
            };
            assert(outpackets@ == Seq::<RslPacket>::empty());
            assume(LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(ss, self@, outpackets@));
            outpackets
        }
    }



    pub fn CReplicaNextReadClockMaybeNominateValueAndSend2a(&mut self, clock: u64) -> (res: OutboundPackets)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            Replica_Common_Postconditions_NoPacket(old(self)@,*self,res),
            res.valid(),
            LReplicaNextReadClockMaybeNominateValueAndSend2a(
                old(self)@,
                self@,
                ClockReading{t: clock as int},
                res@)
    {
        let ghost ss = old(self)@;
        let ghost sclock = ClockReading{t: clock as int};
        let (next_proposer, sent_packets) = generated_proposer::CProposerMaybeNominateValueAndSend2a(&self.proposer, &clock, &self.acceptor.log_truncation_point);
        self.proposer = next_proposer;
        let res = OutboundPackets::PacketSequence { s: sent_packets };
        assert(LProposerMaybeNominateValueAndSend2a(ss.proposer, self@.proposer, clock as int, self.acceptor.log_truncation_point as int, res@));
        res
    }

}

pub open spec fn ConstantsStayConstant_Replica(replica: LReplica, replica_: CReplica) -> bool
    recommends
        replica_.constants.abstractable()
    {
        replica_.constants@ == replica.constants
        && replica.constants == replica.proposer.constants
        && replica.constants == replica.acceptor.constants
        && replica.constants == replica.learner.constants
        && replica.constants == replica.executor.constants
        && replica_.constants@ == replica_.proposer.constants@
        && replica_.constants@ == replica_.acceptor.constants@
        && replica_.constants@ == replica_.learner.constants@
        && replica_.constants@ == replica_.executor.constants@

    }

// Pre-Conditions


pub open spec fn Replica_Common_Preconditions(replica:CReplica, inp:CPacket) ->bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_Process_Heartbeat_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessageHeartbeat
    && replica.valid()
    && inp.valid()
  }

  pub open spec fn Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_ReadClock_CheckForViewTimeout_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_ReadClock_MaybeSendHeartbeat_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_MaybeEnterNewViewAndSend1a_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_MaybeEnterPhase2_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_Spontaneous_MaybeMakeDecision_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_Spontaneous_MaybeExecute_Preconditions(replica:CReplica) -> bool
  {
    replica.valid()
  }

  pub open spec fn Replica_Next_Process_Request_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessageRequest
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_Process_1a_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessage1a
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_Process_1b_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessage1b
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_Process_StartingPhase2_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessageStartingPhase2
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_Process_2a_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessage2a
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_Process_2b_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessage2b
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_Process_AppStateRequest_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessageAppStateRequest
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

  pub open spec fn Replica_Next_Process_AppStateSupply_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {

    inp.msg is CMessageAppStateSupply
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
  }

// // Post-Conditions predicates

pub open spec fn CReplicaConstantsIsValid(s:CReplicaConstants) -> bool
{
    s.abstractable()
    && s.valid()
    && 0 <= s.my_index < s.all.config.replica_ids.len()
}

pub open spec fn Replica_Common_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    CReplicaConstantsIsValid(replica_.constants)
    // CPacketIsSendable(inp) has to be implemented in packetparsing.rs
    && replica_.abstractable()
    && ConstantsStayConstant_Replica(replica, replica_)
    && replica_.valid()
    && packets_sent.valid()
    // && packets_sent.OutboundPacketsHasCorrectSrc(replica_.constants.all.config.replica_ids[replica_.constants.my_index as int])
    && packets_sent.abstractable()
}

pub open spec fn Replica_Common_Postconditions_NoPacket(replica: LReplica, replica_: CReplica, packets_sent: OutboundPackets) -> bool {
    replica_.constants.valid()
    // CPacketIsSendable(inp) has to be implemented in packetparsing.rs
    && replica_.abstractable()
    && ConstantsStayConstant_Replica(replica, replica_)
    && replica_.valid()
    && packets_sent.valid()
    // && packets_sent.OutboundPacketsHasCorrectSrc(replica_.constants.all.config.replica_ids[replica_.constants.my_index as int])
    && packets_sent.abstractable()
}

pub open spec fn Replica_Next_Process_AppStateSupply_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessageAppStateSupply
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcessAppStateSupply(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_AppStateRequest_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessageAppStateRequest
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcessAppStateRequest(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_2b_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessage2b
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcess2b(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_2a_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessage2a
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcess2a(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_StartingPhase2_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessageStartingPhase2
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcessStartingPhase2(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_1b_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessage1b
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcess1b(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_1a_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessage1a
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcess1a(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_Request_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessageRequest
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcessRequest(
        replica,
        replica_@,
        inp.view(),
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_Process_Heartbeat_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, clock: u64, packets_sent: OutboundPackets) -> bool {
    inp.abstractable()
    && inp.msg is CMessageHeartbeat
    && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
    && LReplicaNextProcessHeartbeat(
        replica,
        replica_@,
        inp.view(),
        clock as int,
        packets_sent.view()
    )
}

pub open spec fn Replica_Next_ReadClock_MaybeNominateValueAndSend2a_Postconditions(replica: LReplica, replica_: CReplica, clock: ClockReading, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextReadClockMaybeNominateValueAndSend2a(replica,
         replica_@,
        clock,
        packets_sent@)
}

pub open spec fn Replica_Next_ReadClock_CheckForViewTimeout_Postconditions(replica: LReplica, replica_: CReplica, clock: ClockReading, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextReadClockCheckForViewTimeout(replica,
         replica_@,
        clock,
        packets_sent@)
}

pub open spec fn Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Postconditions(replica: LReplica, replica_: CReplica, clock: ClockReading, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextReadClockCheckForQuorumOfViewSuspicions(replica,
         replica_@,
        clock,
        packets_sent@)
}

pub open spec fn Replica_Next_ReadClock_MaybeSendHeartbeat_Postconditions(replica: LReplica, replica_: CReplica, clock: ClockReading, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextReadClockMaybeSendHeartbeat(replica,
         replica_@,
        clock,
        packets_sent@)
}

pub open spec fn Replica_Next_MaybeEnterNewViewAndSend1a_Postconditions(replica: LReplica, replica_: CReplica, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(replica,
         replica_@,
        packets_sent@)
}

pub open spec fn Replica_Next_MaybeEnterPhase2_Postconditions(replica: LReplica, replica_: CReplica, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextSpontaneousMaybeEnterPhase2(replica,
         replica_@,
        packets_sent@)
}

pub open spec fn Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Postconditions(replica: LReplica, replica_: CReplica, clock: ClockReading, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(replica,
         replica_@,
        packets_sent@)
}

pub open spec fn Replica_Next_Spontaneous_MaybeMakeDecision_Postconditions(replica: LReplica, replica_: CReplica, clock: ClockReading, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextSpontaneousMaybeMakeDecision(replica,
         replica_@,
        packets_sent@)
}

pub open spec fn Replica_Next_Spontaneous_MaybeExecute_Postconditions(replica: LReplica, replica_: CReplica, clock: ClockReading, packets_sent: OutboundPackets) -> bool {
    Replica_Common_Postconditions_NoPacket(replica, replica_, packets_sent)
    && LReplicaNextSpontaneousMaybeExecute(replica,
         replica_@,
        packets_sent@)
}

} // verus!
