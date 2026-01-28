use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::implementation::common::generic_refinement::*;
use crate::implementation::RSL::appinterface::*;
use crate::implementation::RSL::cconfiguration::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::types_i::*;
use crate::protocol::RSL::broadcast::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::message::*;
use crate::protocol::RSL::types::*;
use crate::services::RSL::app_state_machine::*;
use std::collections::*;
use vstd::prelude::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

use super::cconfiguration::CConfiguration;

verus! {
    pub enum CBroadcast {
        CBroadcast{
            src: EndPoint,
            dsts: Vec<EndPoint>,
            msg:CMessage,
        },
        CBroadcastNop{},
    }

    impl CBroadcast{
        pub open spec fn abstractable(self) -> bool
        {
            match self {
                CBroadcast::CBroadcast{src, dsts, msg} =>
                    self->src.abstractable() && (forall |i:int| 0 <= i < self->dsts.len() ==> self->dsts[i].abstractable()) && self->msg.abstractable(),
                CBroadcast::CBroadcastNop{} => true
            }
        }

        pub open spec fn valid(self) -> bool
        {
            &&& self.abstractable()
            &&& match self {
                CBroadcast::CBroadcast{src, dsts, msg} =>
                    self->src.valid_public_key() && (forall |i:int| 0 <= i < self->dsts.len() ==> self->dsts[i].valid_public_key()) && self->msg.valid(),
                CBroadcast::CBroadcastNop{} => true
            }
        }



        pub open spec fn view(self) -> Seq<RslPacket>
            recommends self.abstractable()
        {
            match self {
                CBroadcast::CBroadcast{src, dsts, msg} => BuildLBroadcast(
                    self->src@,
                    self->dsts@.map(|i, e:EndPoint| e@),
                    self->msg@,
                ),
                CBroadcast::CBroadcastNop{} => Seq::<RslPacket>::empty(),
            }
        }

        // #[verifier(external_body)]
        pub fn BuildBroadcastToEveryone(config:&CConfiguration, my_index: u64, msg: CMessage) -> (res:Self)
        requires
            config.valid(),
            ReplicaIndexValid(my_index, *config),
            msg.abstractable(),
            msg.valid()
            // msg.marshallable()
        ensures
            res.abstractable(),
            res.valid(),
            // ({
            //     let packets = OutboundPackets::Broadcast { broadcast: res };
            //     packets.OutboundPacketsHasCorrectSrc(config.replica_ids@[my_index as int])
            // }),
            LBroadcastToEveryone(
                config@,
                my_index as int,
                msg@,
                // BuildLBroadcast(config.replica_ids@[my_index as int]@, config.replica_ids@.map(|i, x:EndPoint| x@), msg@)
                res@
            )
        {
            let mut i = 0;
            let mut dsts_clone: Vec<EndPoint> = Vec::new();
            while i < config.replica_ids.len()
                invariant
                    i <= config.replica_ids.len(),
                    i == dsts_clone.len(),
                    // forall |j: int| 0 <= j < i ==> dsts_clone[i as int]==config.replica_ids[i as int]
                    forall |j: int| 0 <= j < i ==> #[trigger] dsts_clone@[j]@ == config.replica_ids@[j]@
                decreases config.replica_ids.len() - i,
            {
                dsts_clone.push(config.replica_ids[i].clone_up_to_view());
                i+=1;
            }
            let res = CBroadcast::CBroadcast { src: config.replica_ids[my_index as usize].clone_up_to_view(), dsts: dsts_clone, msg: msg.clone_up_to_view() };


            if my_index < config.replica_ids.len() as u64 {
                assert(config.valid());
                match &res {
                    CBroadcast::CBroadcast { src: s, dsts: d, msg: m } => {

                        //Asserting all abstractable functions
                        assert(s.abstractable());
                        assert(forall |i:int| 0 <= i < d.len() ==> d[i].abstractable());
                        assert(msg.abstractable());//Proved that message is the abstractable (requirement)
                        assert(msg@ == m@);//Proved that both are the same
                        assume(m.abstractable());
                        assert(res.abstractable());

                        //Asserting all valid functions
                        assert(s.valid_public_key());
                        assert(forall |i:int| 0 <= i < d.len() ==> d[i].valid_public_key());
                        assume(m.valid());
                        assert(res.valid());

                        assert(s@ == config.replica_ids[my_index as int]@);
                        assert (forall |i: int|0 <= i < config.replica_ids@.len() ==> #[trigger] d@[i]@ == config.replica_ids@[i]@);
                        assert(d@.map(|i,x: EndPoint| x@) =~= config.replica_ids@.map(|i, x:EndPoint| x@));
                        // assert(msg.valid());
                        // assert(msg@ == config.replica_ids[my_index as int]@);

                        let ghost sent_packets = BuildLBroadcast(config.replica_ids@[my_index as int]@, config.replica_ids@.map(|i, x:EndPoint| x@), msg@);
                        //LBroadcast verification
                        assume(config.replica_ids@.len()==sent_packets.len());
                        assert(my_index < config.replica_ids.len());
                        assume(forall |i:int| 0 <= i < sent_packets.len() ==> sent_packets[i] =~= LPacket{
                            dst: config.replica_ids@[i]@,
                            src: config.replica_ids@[my_index as int]@,
                            msg: msg@
                        });
                    }
                    _ => {
                        assert(false);
                    }
                }
                // assert(res.valid());
            }
            else{
                // res = CBroadcast::CBroadcastNop{}
            }
            res
        }
    }

    // #[verifier(external_body)]
    pub proof fn lemma_BuildBroadcast_ensures(src:AbstractEndPoint, dsts:Seq<AbstractEndPoint>, m:RslMessage)
        ensures
            ({
                let b = BuildLBroadcast(src, dsts, m);
                &&& b.len() == dsts.len()
                &&& (forall |i:int| 0 <= i < dsts.len() ==> BuildLBroadcast(src, dsts, m)[i] == LPacket{dst:dsts[i], src:src, msg:m})
            })
        decreases dsts.len()
    {
        if dsts.len() == 0 {
            let b = BuildLBroadcast(src, dsts, m);
            assert(b.len() == 0);
            assert(forall |i:int| 0 <= i < dsts.len() ==> BuildLBroadcast(src, dsts, m)[i] == LPacket{dst:dsts[i], src:src, msg:m});
        } else {
            lemma_BuildBroadcast_ensures(src, dsts.drop_first(), m);

            let b = BuildLBroadcast(src, dsts, m);
            let b_rest = BuildLBroadcast(src, dsts.drop_first(), m);
            assert(b == seq![LPacket{dst: dsts[0], src: src, msg: m}] + b_rest);
        }
    }


    pub enum OutboundPackets {
        Broadcast{
            broadcast:CBroadcast,
        },
        OutboundPacket{
            p:Option<CPacket>,
        },
        PacketSequence{
            s:Vec<CPacket>,
        }
    }

    impl OutboundPackets{
        pub open spec fn abstractable(self) -> bool
        {
            match self {
                OutboundPackets::Broadcast{broadcast} => self->broadcast.abstractable(),
                OutboundPackets::OutboundPacket{p} =>
                    match self->p{
                        Some(p_val) => p_val.abstractable(),
                        None => true,
                    },
                OutboundPackets::PacketSequence{s} => (forall |i:int| 0 <= i < self->s.len() ==> self->s[i].abstractable()),
            }
        }

        pub open spec fn valid(self) -> bool
        {
            &&& self.abstractable()
            &&& match self {
                OutboundPackets::Broadcast{broadcast} => self->broadcast.valid(),
                OutboundPackets::OutboundPacket{p} =>
                    match self->p{
                        Some(p_val) => p_val.valid(),
                        None => true,
                    },
                OutboundPackets::PacketSequence{s} => (forall |i:int| 0 <= i < self->s.len() ==> self->s[i].valid()),
            }
        }

        pub open spec fn view(self) -> Seq<RslPacket>
            recommends self.abstractable()
        {
            match self {
                OutboundPackets::Broadcast{broadcast} => self->broadcast@,
                OutboundPackets::OutboundPacket{p} =>
                    match self->p{
                        Some(p_val) => seq![p_val@],
                        None => Seq::<RslPacket>::empty(),
                    },
                OutboundPackets::PacketSequence{s} => self->s@.map(|i, p:CPacket| p@),
            }
        }

        pub open spec fn OutboundPacketsHasCorrectSrc(self, me:EndPoint) -> bool
        {
            match self {
                OutboundPackets::Broadcast{broadcast} =>
                    match self->broadcast {
                        CBroadcast::CBroadcast{src, dsts, msg} => src == me,
                        CBroadcast::CBroadcastNop{} => true,
                    }
                OutboundPackets::OutboundPacket{p} =>
                    match self->p{
                        Some(p_val) => p_val.src == me,
                        None => true,
                    },
                OutboundPackets::PacketSequence{s} => (forall |i:int| 0 <= i < self->s.len() ==> self->s[i].src == me),
            }
        }
    }
}
