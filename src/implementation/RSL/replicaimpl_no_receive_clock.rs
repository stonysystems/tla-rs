use crate::common::native::io_s::*;
use crate::implementation::RSL::{
    cbroadcast::*, cmessage::*, netrsl_i::*, replicaimpl_class::*, replicaimpl_delivery::*,
    replicaimpl_process_packet_no_clock::*, replicaimpl_read_clock::*, ReplicaImpl::*,
};
use crate::protocol::RSL::environment::*;
use crate::verus_extra::seq_lib_v::*;
use vstd::prelude::*;
use vstd::slice::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

verus! {
    pub fn replica_no_receive_read_clock_next_maybe_nominate_value_send_2a(r:&mut ReplicaImpl, netc:&mut NetClient) -> (ok:bool)
        requires old(r).valid(),
    {
        let clock = read_clock(netc);
        let outpackets = CReplica::CReplicaNextReadClockMaybeNominateValueAndSend2a(&mut r.replica, clock);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    pub fn replica_no_receive_read_clock_next_check_for_view_timeout(r:&mut ReplicaImpl, netc:&mut NetClient) -> (ok:bool)
        requires old(r).valid(),
    {
        let clock = read_clock(netc);
        let outpackets = CReplica::CReplicaNextReadClockCheckForViewTimeout(&mut r.replica, clock);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    pub fn replica_no_receive_read_clock_next_check_for_quorum_of_view_suspicious(r:&mut ReplicaImpl, netc:&mut NetClient) -> (ok:bool)
        requires old(r).valid(),
    {
        let clock = read_clock(netc);
        let outpackets = CReplica::CReplicaNextReadClockCheckForQuorumOfViewSuspicions(&mut r.replica, clock);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    pub fn replica_no_receive_read_clock_next_maybe_send_heartbeat(r:&mut ReplicaImpl, netc:&mut NetClient) -> (ok:bool)
        requires old(r).valid(),
    {
        let clock = read_clock(netc);
        let outpackets = CReplica::CReplicaNextReadClockMaybeSendHeartbeat(&mut r.replica, clock);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    pub fn replica_no_receive_read_clock_next(r:&mut ReplicaImpl, netc:&mut NetClient) -> (ok:bool)
        requires old(r).valid(),
    {
        if r.nextActionIndex == 3 {
            replica_no_receive_read_clock_next_maybe_nominate_value_send_2a(r, netc)
        } else if r.nextActionIndex == 7 {
            replica_no_receive_read_clock_next_check_for_view_timeout(r, netc)
        } else if r.nextActionIndex == 8 {
            replica_no_receive_read_clock_next_check_for_quorum_of_view_suspicious(r, netc)
        } else if r.nextActionIndex == 9 {
            replica_no_receive_read_clock_next_maybe_send_heartbeat(r, netc)
        } else {
            true
        }
    }
}
