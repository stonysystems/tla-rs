use super::host_s::EventResults;
use crate::common::native::io_s::*;
use crate::implementation::RSL::{
    cbroadcast::*, cmessage::*, netrsl_i::*, replicaimpl_class::*, replicaimpl_delivery::*,
    replicaimpl_no_receive_clock::*, replicaimpl_no_receive_no_clock::*,
    replicaimpl_process_packet_no_clock::*, replicaimpl_process_packet_x::*,
    replicaimpl_read_clock::*, ReplicaImpl::*,
};
use crate::protocol::RSL::environment::*;
use crate::verus_extra::seq_lib_v::*;
use vstd::prelude::*;
use vstd::slice::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

verus! {


    pub fn roll_action_index(a: u64) -> (a_prime: u64)
        requires
            0 <= a < 10,
        ensures
            (a_prime as int) == ((a as int + 1) % 10 as int),
    {
        if a >= 9 {
            0
        } else {
            a + 1
        }
    }


    pub fn ReplicaNextMainProcessPacketX(r:&mut ReplicaImpl, netc:&mut NetClient) -> (res: (bool, Ghost<EventResults>, Ghost<Seq<RslIo>>))
        requires
            old(r).valid(),
            old(r).nextActionIndex == 0,
    {
        let ghost event_results = EventResults{
            recvs: seq![],
            clocks: seq![],
            sends: seq![],
            ios: seq![],
        };

        let (ok, net_event_log, ios) = replica_next_process_packet_x(r, netc);
        if !ok {
            return (ok, Ghost(event_results), ios);
        }

        r.nextActionIndex = 1;

        (ok, Ghost(event_results), ios)
    }

    #[verifier(external_body)]
    pub fn ReplicaNextMainNoClock(r:&mut ReplicaImpl, netc:&mut NetClient) -> (res: (bool, Ghost<EventResults>, Ghost<Seq<RslIo>>))
    {

        let curActionIndex = r.nextActionIndex;
        let ghost mut net_event = Seq::<NetEvent>::empty();
        let ghost mut ios_his = Seq::<RslIo>::empty();

        let ghost event_results = EventResults{
            recvs: seq![],
            clocks: seq![],
            sends: seq![],
            ios: seq![],
        };

        let ok = replica_no_receive_no_read_clock(r, netc);
        if !ok {
            return (ok, Ghost(event_results), Ghost(ios_his));
        }

        let nextActionIndex_prime = r.nextActionIndex +1;
        r.nextActionIndex = nextActionIndex_prime;

        (ok, Ghost(event_results), Ghost(ios_his))
    }

    #[verifier(external_body)]
    pub fn ReplicaNextMainReadClock(r:&mut ReplicaImpl, netc:&mut NetClient) -> (res: (bool, Ghost<EventResults>, Ghost<Seq<RslIo>>))
    {
        let curActionIndex = r.nextActionIndex;
        let ghost mut net_event = Seq::<NetEvent>::empty();
        let ghost mut ios_his = Seq::<RslIo>::empty();
        let ghost event_results = EventResults{
            recvs: seq![],
            clocks: seq![],
            sends: seq![],
            ios: seq![],
        };

        let ok = replica_no_receive_read_clock_next(r, netc);
        if !ok {
            return (ok, Ghost(event_results), Ghost(ios_his));
        }

        let nextActionIndex_prime = roll_action_index(r.nextActionIndex);
        r.nextActionIndex = nextActionIndex_prime;

        (ok, Ghost(event_results), Ghost(ios_his))
    }

    #[verifier(external_body)]
    pub fn Replica_Next_main(r:&mut ReplicaImpl, netc:&mut NetClient) -> (res: (bool, Ghost<EventResults>, Ghost<Seq<RslIo>>))
    {
        if r.nextActionIndex == 0 {
            ReplicaNextMainProcessPacketX(r, netc)
          }
          else if r.nextActionIndex == 1 || r.nextActionIndex == 2 || r.nextActionIndex == 4 || r.nextActionIndex == 5 || r.nextActionIndex == 6 {
            ReplicaNextMainNoClock(r, netc)
          }
          else if r.nextActionIndex == 3 || (7 <= r.nextActionIndex && r.nextActionIndex <= 9) {
            ReplicaNextMainReadClock(r, netc)
          } else {
            let ghost event_results = EventResults{
                recvs: seq![],
                clocks: seq![],
                sends: seq![],
                ios: seq![],
            };
            let ghost net_event = Seq::<NetEvent>::empty();
            let ghost ios_his = Seq::<RslIo>::empty();
            (false, Ghost(event_results), Ghost(ios_his))
          }
    }
}
