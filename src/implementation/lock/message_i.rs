#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::{modes::*, prelude::*, seq::*, *};

use super::netlock_i::{is_marshalable_data, net_packet_bound, net_packet_is_abstractable};
use crate::common::framework::environment_s::LPacket;
use crate::common::native::io_s::*;
use crate::implementation::common::marshalling::*;
use crate::protocol::lock::types::*;

// This mixes PacketParsing and Message

verus! {
    // Concrete Message, which has a view to LockMessage (the protocol message)
    // Also implements marshallable
    define_enum_and_derive_marshalable! {
        pub enum CMessage {
            #[tag = 0]
            CTransfer{#[o=o0] transfer_epoch:u64},
            #[tag = 1]
            CLocked{ #[o=o0] locked_epoch:u64},
            #[tag = 2]
            CInvalid,
        }
    [rlimit attr = verifier::rlimit(25)]
    }

    impl CMessage {
        pub open spec fn view(self) -> LockMessage {
            match self {
                CMessage::CTransfer{transfer_epoch} => LockMessage::Transfer { transfer_epoch: transfer_epoch as int},
                CMessage::CLocked{locked_epoch}     => LockMessage::Locked{locked_epoch: locked_epoch as int},
                CMessage::CInvalid                  => LockMessage::Invalid,
            }
        }

        pub open spec fn abstractable(self) -> bool { true }

        pub fn clone_up_to_view(&self) -> (c: Self)
        ensures
          c@ == self@
        {
            match self {
                CMessage::CTransfer{transfer_epoch} => {CMessage::CTransfer { transfer_epoch: transfer_epoch.clone()}},
                CMessage::CLocked{locked_epoch}     =>  {CMessage::CLocked{locked_epoch: locked_epoch.clone()}} ,
                CMessage::CInvalid                              => { CMessage::CInvalid },
            }
        }

        pub open spec fn marshallable(&self) -> bool
        {
            match self {
                CMessage::CTransfer{..} => true,
                CMessage::CLocked{..}   => true,
                CMessage::CInvalid{}    => false,
            }
        }

        pub fn is_marshallable(&self) -> (b: bool)
            ensures b == self.marshallable()
        {
            match self {
                CMessage::CTransfer{..} => true,
                CMessage::CLocked{..}   => true,
                CMessage::CInvalid{}    => false,
            }
        }
    }

    // Concrete Packet, with a view to protocol LockPacket
   pub type CLockPacket = LPacket<EndPoint, CMessage>;

   impl CLockPacket {
        pub open spec fn view(self) -> LockPacket
        {
            LockPacket{dst: self.dst@, src: self.src@, msg: self.msg@}
        }

        pub open spec fn abstractable(self) -> bool {
            &&& self.dst.abstractable()
            &&& self.src.abstractable()
            &&& self.msg.abstractable()
        }

        fn clone_up_to_view(&self) -> (o: Self) {
            CLockPacket {
                dst: self.dst.clone_up_to_view(),
                src: self.src.clone_up_to_view(),
                msg: self.msg.clone_up_to_view(),
            }
        }
   }

   pub open spec fn abstractify_net_packet_to_lock_packet(net: NetPacket) -> LockPacket
    recommends net_packet_is_abstractable(net)
    {
        LockPacket {
            dst: net.dst,
            src: net.src,
            msg: (lock_demarshal_data(net.msg))@
        }
    }

    pub open spec fn lock_demarshal_data(data: Seq<u8>) -> CMessage
    {
        let v = choose |v: CMessage| v.is_marshalable() && v.ghost_serialize() == data;
        v
    }

    pub open spec fn outbound_packet_is_valid(cpacket: &CLockPacket) -> bool
    {
        &&& cpacket.abstractable()
        &&& cpacket.msg.is_marshalable()
        &&& !(cpacket.msg is CInvalid)
    }


    pub open spec fn optional_clock_packet_is_valid(opt_packet: Option<CLockPacket>) -> bool {
        match opt_packet {
            Some(packet) => {
                outbound_packet_is_valid(&packet)
            },
            _ => true
        }
    }

}
