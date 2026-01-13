use builtin::*;
use builtin_macros::*;
use crate::implementation::common::function::*;
use vstd::prelude::*;
use vstd::slice::*;
use crate::verus_extra::seq_lib_v::*;
use crate::common::native::io_s::*;
use crate::protocol::RSL::environment::*;
use crate::implementation::RSL::{
    replicaimpl_class::*, 
    cmessage::*, cbroadcast::*, 
    replicaimpl_delivery::*, 
    netrsl_i::*, 
    ReplicaImpl::*,
    replicaimpl_read_clock::*,
    replicaimpl_process_packet_no_clock::*,
};
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

verus!{
    #[verifier(external_body)]
    pub fn replica_no_receive_no_read_clock_next_maybe_enter_new_view_send_1a(r:&mut ReplicaImpl, netc:&mut NetClient) -> (ok:bool)
    {
        let outpackets = CReplica::CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(&mut r.replica);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    #[verifier(external_body)]
    pub fn replica_no_receive_no_read_clock_next_maybe_enter_phase2(r:&mut ReplicaImpl, netc:&mut NetClient) -> (ok:bool)
    {
        let outpackets = CReplica::CReplicaNextSpontaneousMaybeEnterPhase2(&mut r.replica);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    #[verifier(external_body)]
    pub fn replica_no_receive_no_read_clock_truncate_log_based_on_checkpoints(r:&mut ReplicaImpl, netc:&mut NetClient) -> (ok:bool)
    {
        let outpackets = CReplica::CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(&mut r.replica);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    #[verifier(external_body)]
    pub fn replica_no_receive_no_read_clock_maybe_make_decision(r:&mut ReplicaImpl, netc:&mut NetClient) -> (ok:bool)
    {
        let outpackets = CReplica::CReplicaNextSpontaneousMaybeMakeDecision(&mut r.replica);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    #[verifier(external_body)]
    pub fn replica_no_receive_no_read_clock_maybe_execute(r:&mut ReplicaImpl, netc:&mut NetClient) -> (ok:bool)
    {
        let outpackets = CReplica::CReplicaNextSpontaneousMaybeExecute(&mut r.replica);
        let ok = deliver_outbound_packets(r, netc, &outpackets);
        ok
    }

    #[verifier(external_body)]
    pub fn replica_no_receive_no_read_clock(r:&mut ReplicaImpl, netc:&mut NetClient) -> (ok:bool)
    {
        if r.nextActionIndex == 1 {
            replica_no_receive_no_read_clock_next_maybe_enter_new_view_send_1a(r, netc)
        } else if r.nextActionIndex == 2 {
            replica_no_receive_no_read_clock_next_maybe_enter_phase2(r, netc)
        } else if r.nextActionIndex == 4 {
            replica_no_receive_no_read_clock_truncate_log_based_on_checkpoints(r, netc)
        } else if r.nextActionIndex == 5 {
            replica_no_receive_no_read_clock_maybe_make_decision(r, netc)
        } else if r.nextActionIndex == 6 {
            replica_no_receive_no_read_clock_maybe_execute(r, netc)
        } else {
            true
        }
    }
}