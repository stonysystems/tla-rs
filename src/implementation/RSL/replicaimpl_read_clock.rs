use builtin::*;
use builtin_macros::*;
use crate::implementation::common::function::*;
use vstd::prelude::*;
use vstd::slice::*;
use crate::verus_extra::seq_lib_v::*;
use crate::common::native::io_s::*;
use crate::protocol::RSL::environment::*;
use crate::implementation::RSL::{replicaimpl_class::*, cmessage::*, cbroadcast::*, replicaimpl_delivery::*, netrsl_i::*, ReplicaImpl::*};
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

verus!{
    #[verifier::external_body]
    pub fn replica_next_read_clock_and_process_packet( r:&mut ReplicaImpl, netc:&mut NetClient, cpacket:CPacket) -> (ok:bool)
    {
        let clock = read_clock(netc);
        let outpackets = CReplica::CReplicaNextProcessHeartbeat(&mut r.replica, cpacket, clock);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }
}