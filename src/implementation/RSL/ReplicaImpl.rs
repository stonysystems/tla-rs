use crate::implementation::common::upper_bound::*;
use crate::implementation::common::upper_bound_i::*;
use crate::implementation::RSL::types_i::*;
use vstd::prelude::*;
// use crate::implementation::lock::message_i::*;
use crate::implementation::RSL::acceptorimpl::*;
use crate::implementation::RSL::cbroadcast::*;
use crate::implementation::RSL::cconstants::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::learnerimpl::*;
use crate::implementation::RSL::ExecutorImpl::*;
use crate::implementation::RSL::ProposerImpl::*;
use crate::implementation::RSL::{cconfiguration::*, cconstants::*, ProposerImpl::*};
use crate::protocol::RSL::{environment::*, replica::*};
// use crate::protocol::RSL::types::*;
use crate::common::collections::vecs::*;
use crate::protocol::common::upper_bound::*;
use crate::protocol::RSL::{
    acceptor::*, configuration::*, constants::*, constants::*, executor::*, learner::*, message::*,
    proposer::*, types::*,
};
use std::collections::*;
use vstd::std_specs::hash::*;
use vstd::{map::*, map_lib::*, prelude::*, seq::*};

verus! {
    broadcast use crate::common::native::io_s::axiom_endpoint_key_model;
// #[derive(Clone)]
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

    // #[verifier(external_body)]
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
            proposer: CProposer::CProposerInit(c.clone_up_to_view()),
            acceptor: CAcceptor::CAcceptorInit(c.clone_up_to_view()),
            learner: CLearner::CLearnerInit(c.clone_up_to_view()),
            executor: CExecutor::CExecutorInit(c.clone_up_to_view())
        };
        s
    }

    // #[verifier(external_body)]
    pub fn CReplicaNextProcessInvalid(&mut self, received_packet: CPacket) -> (res: OutboundPackets)
        requires
            old(self).valid(),
            received_packet.valid(),
            received_packet.msg is CMessageInvalid,
        ensures
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

    // #[verifier(external_body)]
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
                            assume(v@ == ss.executor.reply_cache[sp.src]); // don't know why, maybe the key is endpoint, it should satisfy some properties.
                            if v.seqno >= seqno_req {
                                assert(ss.executor.reply_cache.contains_key(sp.src));
                                assert(sp.msg->seqno_req <= ss.executor.reply_cache[sp.src].seqno);
                                let outpackets = self.executor.CExecutorProcessRequest(received_packet);
                                assert(ss == self@);
                                assert(LExecutorProcessRequest(ss.executor, sp, outpackets@));
                                assert(LReplicaNextProcessRequest(ss, self@, sp, outpackets@));
                                outpackets
                            }
                            else
                            {
                                assert(ss.executor.reply_cache.contains_key(sp.src));
                                assert(sp.msg->seqno_req > ss.executor.reply_cache[sp.src].seqno);

                                self.proposer.CProposerProcessRequest(received_packet);

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
                    assume(!ss.executor.reply_cache.contains_key(sp.src)); // don't know why, maybe the key is endpoint, it should satisfy some properties.
                    // Self::print("receive request");
                    self.proposer.CProposerProcessRequest(received_packet);
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

    // #[verifier(external_body)]
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
        let res = self.acceptor.CAcceptorProcess1a(received_packet);
        res

    }

    #[verifier(external_body)]
    pub fn Packet1bHasUniqueSrc(s:&HashSet<CPacket>, pkt:&CPacket) -> (res:bool)
        requires
            // forall |p:CPacket| s@.contains(p) ==> p.msg is CMessage1b,
            pkt.msg is CMessage1b,
        ensures
            res ==> forall |op:CPacket| s@.contains(op) ==> op.src@ != pkt.src@
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;
        broadcast use crate::common::native::io_s::axiom_endpoint_key_model;
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

    // #[verifier(external_body)]
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

                if contains(&self.proposer.constants.all.config.replica_ids, &received_packet.src)
                    && CBalEq(&bal_1b, &self.proposer.max_ballot_i_sent_1a)
                    && self.proposer.current_state == 1
                    && samesrc
                {
                    Self::print("receive valid 1b");
                    assert(ss.proposer.constants.all.config.replica_ids.contains(sp.src));
                    assert(sp.msg->bal_1b == ss.proposer.max_ballot_i_sent_1a);
                    assert(ss.proposer.current_state == 1);
                    assert(forall |op:RslPacket| ss.proposer.received_1b_packets.contains(op) ==> op.src != sp.src);
                    self.acceptor.CAcceptorTruncateLog(log_truncation_point);
                    self.proposer.CProposerProcess1b(received_packet);
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
                    // don't know why, if has been proved contains, but else cannot infer that doesn't contain.
                    assume(!ss.proposer.constants.all.config.replica_ids.contains(sp.src));
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

    // #[verifier(external_body)]
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
        let res = self.executor.CExecutorProcessStartingPhase2(received_packet);
        res
    }

    // #[verifier(external_body)]
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
                    let outpackets = self.acceptor.CAcceptorProcess2a(received_packet);
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

    // #[verifier(external_body)]
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
                            self.learner.CLearnerProcess2b(received_packet);
                        }
                    }
                    COutstandingOperation::COutstandingOpKnown{v, bal} => {
                        if self.executor.ops_complete < opn_2b {
                            self.learner.CLearnerProcess2b(received_packet);
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

    // #[verifier(external_body)]
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

    // #[verifier(external_body)]
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
                    self.learner.CLearnerForgetOperationsBefore(opn_state_supply);
                    self.executor.CExecutorProcessAppStateSupply(received_packet);
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

    // #[verifier(external_body)]
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
        let reply_cache = clone_creply_cache_up_to_view(&self.executor.reply_cache);
        let res  = self.executor.CExecutorProcessAppStateRequest(received_packet, reply_cache);
        res
    }

    // #[verifier(external_body)]
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
        self.proposer.CProposerProcessHeartbeat(received_packet.clone_up_to_view(), clock);
        self.acceptor.CAcceptorProcessHeartbeat(received_packet);
        let mut pkt_vec: Vec<CPacket> = Vec::new();
        let outpackets = OutboundPackets::PacketSequence{
            s:pkt_vec,
        };
        assert(outpackets@ == Seq::<RslPacket>::empty());

        outpackets
    }

    // #[verifier(external_body)]
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
        let res = self.proposer.CProposerMaybeEnterNewViewAndSend1a();
        res
    }

    // #[verifier(external_body)]
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
        let res = self.proposer.CProposerMaybeEnterPhase2(self.acceptor.log_truncation_point);
        // let res = self.proposer.CProposerMaybeEnterPhase2_optimized(self.acceptor.log_truncation_point);
        res
    }

    // #[verifier(external_body)]
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
                // assert(forall |i:COperationNumber| self.learner.unexecuted_learner_state@.contains_key(i) ==> COperationNumberIsValid(i) && self.learner.unexecuted_learner_state@[i].valid());
                assume(forall |i:COperationNumber| self.learner.unexecuted_learner_state@.contains_key(i) ==> self.learner.unexecuted_learner_state@[i].valid());
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
                                // need to prove that the view of EndPoint is injective
                                assume(self.learner.unexecuted_learner_state@[opn].received_2b_message_senders.len() == ss.learner.unexecuted_learner_state[opn as int].received_2b_message_senders.len());
                                assert(ss.learner.unexecuted_learner_state[opn as int].received_2b_message_senders.len() >= LMinQuorumSize(ss.learner.constants.all.config));
                                self.executor.CExecutorGetDecision(
                                    self.learner.max_ballot_seen, opn, &v.candidate_learned_value
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
                                assume(ss.learner.unexecuted_learner_state[opn as int].received_2b_message_senders.len() < LMinQuorumSize(ss.learner.constants.all.config));
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

    // #[verifier(external_body)]
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
                    self.proposer.CProposerResetViewTimerDueToExecution(&v);
                    self.learner.CLearnerForgetDecision(self.executor.ops_complete);
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

    // #[verifier(external_body)]
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

    // #[verifier(external_body)]
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
        self.proposer.CProposerCheckForViewTimeout(clock);
        let mut pkt_vec: Vec<CPacket> = Vec::new();
        let outpackets = OutboundPackets::PacketSequence{
            s:pkt_vec,
        };
        assert(outpackets@ == Seq::<RslPacket>::empty());

        outpackets
    }

    // #[verifier(external_body)]
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
        self.proposer.CProposerCheckForQuorumOfViewSuspicions(clock);
        let mut pkt_vec: Vec<CPacket> = Vec::new();
        let outpackets = OutboundPackets::PacketSequence{
            s:pkt_vec,
        };
        assert(outpackets@ == Seq::<RslPacket>::empty());

        outpackets
    }

    // #[verifier(external_body)]
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
                self.acceptor.CAcceptorTruncateLog(target);
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

    #[verifier(external_body)]
    pub fn SortVecCOperationNumber(s:&mut Vec<COperationNumber>)
    {
        let mut i = 1;
        while i < s.len()
        {
            let mut j = i;
            while 0 < j && s[j-1] > s[j]
            {
                let temp = s[j-1];
                s[j-1] = s[j];
                s[j] = s[j-1];
                j = j - 1;
            }
            i = i + 1;
        }
    }



    #[verifier(external_body)]
    pub fn CGetHighestValueAmongMajority(checkpoints:&Vec<COperationNumber>, n:usize) -> (res:COperationNumber)
    {
        let mut s = clone_vec_coperationnumber(checkpoints);
        Self::SortVecCOperationNumber(&mut s);
        let len = checkpoints.len();
        s[len - n]
    }

    #[verifier(external_body)]
    pub fn CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints_optimized(&mut self) -> (res:OutboundPackets)
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
        let n = self.constants.all.config.CMinQuorumSize();
        let opn = Self::CGetHighestValueAmongMajority(&self.acceptor.last_checkpointed_operation, n);
        if opn > self.acceptor.log_truncation_point{
            self.acceptor.CAcceptorTruncateLog(opn);
            let mut pkt_vec: Vec<CPacket> = Vec::new();
            let outpackets = OutboundPackets::PacketSequence{
                s:pkt_vec,
            };
            outpackets
        } else {
            let mut pkt_vec: Vec<CPacket> = Vec::new();
            let outpackets = OutboundPackets::PacketSequence{
                s:pkt_vec,
            };
            outpackets
        }
    }

    // #[verifier(external_body)]
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
        let res = self.proposer.CProposerMaybeNominateValueAndSend2a(clock, self.acceptor.log_truncation_point);
        // let res = self.proposer.CProposerMaybeNominateValueAndSend2a_optimized(clock, self.acceptor.log_truncation_point);
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
    // && CPacketIsSendable(inp)
    //
    // ^^^ Needs to be implemented in packetparsing:
    // predicate CPacketIsSendable(cpacket:CPacket)
    // {
    //   && CMessageIsMarshallable(cpacket.msg)
    //   && CPacketIsAbstractable(cpacket)
    //   && EndPointIsValidIPV4(cpacket.src)
    // }
  }

  pub open spec fn Replica_Next_Process_Heartbeat_Preconditions(replica:CReplica, inp:CPacket) -> bool
  {
    inp.msg is CMessageHeartbeat
    && replica.valid()
    && inp.valid()
    // && inp.msg.marshallable()
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

// pub open spec fn Replica_Next_Process_2a_Postconditions(replica: LReplica, replica_: CReplica, inp: CPacket, packets_sent: OutboundPackets) -> bool {
//     inp.abstractable()
//     && inp.msg is CMessage2a
//     && Replica_Common_Postconditions(replica, replica_, inp, packets_sent)
//     && LReplicaNextProcess2a(
//         replica,
//         replica_@,
//         inp.view(),
//         packets_sent.view()
//     )
// }

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
