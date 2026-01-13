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
    replicaimpl_process_packet_x::*,
    replicaimpl_no_receive_clock::*,
    replicaimpl_no_receive_no_clock::*,
};
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use super::host_s::EventResults;

verus!{

    // #[verifier(external_body)]
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
    // ensures 
    // // result: (bool, Seq<UdpEvent>, Seq<RslIo>)| {
    // // let (ok, net_event_log, ios) = result;
    //     r.valid(),
    //     r.netClient().is_some(),
    //     r.env().valid()
    //     r.valid && r.env().ok.ok(),
    //     r.env() == old(r.env())
    //     r.valid() 
    //     && (Q_LScheduler_Next(old(r.AbstractifyToLScheduler()), r.AbstractifyToLScheduler(), res.2)
    //     || HostNextIgnoreUnsendable(old(r.AbstractifyToLScheduler()), r.AbstractifyToLScheduler(), res.1)),
    //     RawIoConsistentWithSpecIO(net_event_log, ios)
    //     && OnlySentMarshallableData(net_event_log)
    //     && old(r.env().udp().history()) + net_event_log == r.env().udp().history()
    {
        // proof {
        //     let replica_old = old(r.AbstractifyToLReplica());
        //     let scheduler_old = old(r.AbstractifyToLScheduler());

        //     assert(scheduler_old.nextActionIndex() == 0);
        //     assert(scheduler_old.replica == replica_old);
        // }

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

        // assert(r.valid());

        // proof {
        //     let net_client_old = r.net_client().clone();
        //     let net_addr_old = r.net_client().local_end_point();
        //     assert(UdpClientIsValid(&net_client_old));
        // }

        // proof {
        //     let replica = r.AbstractifyToLReplica();
        // }
        r.nextActionIndex = 1;

        // proof {
        //     let scheduler = r.AbstractifyToLScheduler();

        //     assert(net_client_old == r.net_client());
        //     assert(UdpClientIsValid(r.net_client()));
        //     assert(net_addr_old == r.net_client().local_end_point());

        //     assert(r.valid());

        //     calc! {
        //         scheduler.next_action_index();
        //         == r.next_action_index();
        //         == 1;
        //         == (1 % LReplicaNumActions());
        //         == (scheduler_old.next_action_index() + 1) % LReplicaNumActions();
        //     }

        //     if Q_LReplica_Next_ProcessPacket(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios) {
        //         let replica = r.AbstractifyToLReplica();
        //         let scheduler = r.AbstractifyToLScheduler();
        //         lemma_EstablishQLSchedulerNext(replica_old, replica, ios, scheduler_old, scheduler);
        //         assert(Q_LScheduler_Next(old(r.AbstractifyToLScheduler()), r.AbstractifyToLScheduler(), ios));
        //     } else {
        //         assert(IosReflectIgnoringUnsendable(net_event_log));
        //         assert(old(r.AbstractifyToLReplica()) == r.AbstractifyToLReplica());
        //         assert(HostNextIgnoreUnsendable(old(r.AbstractifyToLScheduler()), r.AbstractifyToLScheduler(), net_event_log));
        //     }
        // }

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