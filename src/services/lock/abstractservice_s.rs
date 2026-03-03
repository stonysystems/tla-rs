#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::{modes::*, prelude::*, seq::*, *};

use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::implementation::common::marshalling::*;

verus! {
    pub struct AbstractLockServiceState{
        pub hosts:Set<AbstractEndPoint>,
        pub history:Seq<AbstractEndPoint>
    }

    // Matches CMessage::CLocked{locked_epoch: epoch as u64}.ghost_serialize()
    // (1-byte tag=1 + 8-byte little-endian u64)
    pub open spec fn marshall_lock_message(epoch:int) -> Seq<u8>
    {
      if 0 <= epoch < 0x1_0000_0000_0000_0000
            { seq![1u8] + (epoch as u64).ghost_serialize()
            }
      else {
          seq![1u8]
      }
    }

    pub open spec fn service_init(s: AbstractLockServiceState, server_addresses: Set<AbstractEndPoint>) -> bool {
        &&& s.hosts =~= server_addresses
        &&& (exists |e: AbstractEndPoint| server_addresses.contains(e) && s.history =~= seq![e])
    }

    pub open spec fn service_next(s: AbstractLockServiceState, s_: AbstractLockServiceState) -> bool {
        &&& s_.hosts =~= s.hosts
        &&& (exists |new_lock_holder: AbstractEndPoint| #![auto] s.hosts.contains(new_lock_holder)
                        && s_.history =~= s.history + seq![new_lock_holder])
    }

    pub open spec fn service_correspondence(concrete_pkts: Set<LPacket<AbstractEndPoint, Seq<u8>>>, service_state: AbstractLockServiceState) -> bool {
        forall |p: LPacket<AbstractEndPoint, Seq<u8>>, epoch: int| #![auto] concrete_pkts.contains(p)
                && service_state.hosts.contains(p.src)
                && service_state.hosts.contains(p.dst)
                && 0 <= epoch < 0x1_0000_0000_0000_0000
                && p.msg =~= marshall_lock_message(epoch) ==> 1 <= epoch <= service_state.history.len()
                                                        && p.src == service_state.history[epoch-1]
    }
}
