use super::{
    acceptorimpl::CAcceptor,
    cconfiguration::CConfiguration,
    cconstants::{CConstants, CReplicaConstants},
    cparameters::CParameters,
    ElectionImpl::CElectionState,
    ExecutorImpl::CExecutor,
    ExecutorImpl::COutstandingOperation,
    ProposerImpl::CProposer,
    ReplicaImpl::CReplica,
};
use crate::common::native::io_s::NetEvent;
// use crate::implementation::common::generic_marshalling::G;
use crate::implementation::RSL::cmessage::CPacket;
use crate::implementation::RSL::learnerimpl::CLearner;
use crate::implementation::RSL::ProposerImpl::CIncompleteBatchTimer;
use crate::implementation::RSL::{cmessage::*, learnerimpl::*, ProposerImpl::*, ReplicaImpl::*};
use crate::protocol::RSL::environment::RslIo;
use crate::protocol::RSL::replica::LReplica;
use crate::protocol::RSL::replica::LScheduler;
use crate::{
    common::native::io_s::*,
    implementation::common::upper_bound_i::CUpperBound,
    implementation::RSL::types_i::*,
    protocol::RSL::executor,
};
use builtin::*;
use builtin_macros::*;
use std::collections::{HashMap, HashSet};
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

verus! {

    pub struct ReplicaImpl{
        pub replica: CReplica,
        pub nextActionIndex: u64,
        // pub netClient: Option<NetClient>,
        pub localAddr: EndPoint,
        // pub msg_grammar: G,
    }

    impl ReplicaImpl{

    // #[verifier(external_body)]
    //     fn new() -> Self{
    //         let rcs = CReplicaConstants{my_index: 0, 
    //             all: CConstants {
    //                 config: CConfiguration{replica_ids: vec![]}, 
    //                 params: CParameters{
    //                     max_log_length: 0,
    //                     baseline_view_timeout_period: 0,
    //                     heartbeat_period: 0,
    //                     max_integer_val: u64::MAX,
    //                     max_batch_size: 0,
    //                     max_batch_delay: 0
    //                 } 
    //             }
    //         };
    //         let election_state = CElectionState{
    //             constants: rcs,
    //             current_view: CBallot{
    //                 seqno : 0,
    //                 proposer_id : 0,},
    //             current_view_suspectors: HashSet::new(),
    //             epoch_end_time: 0,
    //             epoch_length: 0,
    //             requests_received_this_epoch: vec![],
    //             requests_received_prev_epochs: vec![],};
    //         let proposer_state = CProposer{
    //             constants: rcs,
    //             current_state: 0,
    //             request_queue: vec![],
    //             max_ballot_i_sent_1a: CBallot{
    //                 seqno : 0,
    //                 proposer_id : 0,},
    //             next_operation_number_to_propose: 0,
    //             received_1b_packets: HashSet::new(),
    //             highest_seqno_requested_by_client_this_view: HashMap::new(),
    //             incomplete_batch_timer: CIncompleteBatchTimer::CIncompleteBatchTimerOff{},
    //             election_state: election_state,
    //         };
    //         let acceptor_state =
    //         CAcceptor{
    //             constants: rcs,
    //             max_bal: CBallot{
    //                 seqno : 0,
    //                 proposer_id : 0,},
    //             votes: HashMap::new(),
    //             last_checkpointed_operation: vec![],
    //             log_truncation_point: 0,
    //         };
    //         let learner_state = CLearner{
    //             constants: rcs,
    //             max_ballot_seen: CBallot{
    //                 seqno : 0,
    //                 proposer_id : 0,},
    //             unexecuted_learner_state: HashMap::new(),};
    //         let executor_state = CExecutor{
    //             constants: rcs,
    //             app: 0,
    //             ops_complete: 0,
    //             max_bal_reflected: CBallot{
    //                 seqno : 0,
    //                 proposer_id : 0,},
    //             next_op_to_execute: COutstandingOperation::COutstandingOpUnknown{},
    //             reply_cache: HashMap::new()
    //         };

    //         Self{

    //             replica: CReplica {
    //                 constants: rcs,
    //                 nextHeartbeatTime: 0,
    //                 proposer: proposer_state,
    //                 acceptor: acceptor_state,
    //                 learner: learner_state,
    //                 executor: executor_state},
    //             netClient: None,
    //             nextActionIndex: 0,
    //             localAddr: AbstractEndPoint{id: Seq::empty()},
    //             msg_grammar: G::GUint64,
    //         }

    //     }

    // #[verifier(external_body)]
    pub open spec fn valid(&self) -> bool
        // recommends self.netClient.is_Some() ==> self.netClient.get_Some_0().valid()
        // ensures |ret: bool| ret ==> self.Repr() === set![self] + UdpClientRepr(self.netClient.get_Some_0())
    {
        &&& self.replica.abstractable()
        &&& self.replica.valid()
        &&& 0 <= self.nextActionIndex 
        &&& self.nextActionIndex < 10
        // &&& self.netClient.is_Some()
        // &&& self.netClient.get_Some_0().valid()
        // &&& self.netClient.get_Some_0().end_point@ === self.localAddr
        &&& self.localAddr@ === self.replica.constants.all.config.replica_ids[self.replica.constants.my_index as int]@
        // &&& self.Repr() === set![self] + UdpClientRepr(self.netClient.get_Some_0())
    }

    // #[verifier(external_body)]
    // pub fn env(&self) -> HostEnvironment
    //     requires
    //     self.netClient.is_Some(),
    //     self.netClient.get_Some_0().valid()
    // {
    //     self.netClient.get_Some_0().env()
    // }

    // #[verifier(external_body)]
    pub open spec fn view(&self) -> LReplica
        recommends self.replica.valid()
    {
        self.replica@
    }

    // #[verifier(external_body)]
    // pub open spec fn AbstractifyToLScheduler(&self) -> LScheduler
    //     recommends self.replica.valid()
    // {
    //     LScheduler{
    //         replica:self.replica@,
    //         nextActionIndex:self.nextActionIndex as int,
    //     }

    // }

    // #[verifier(external_body)]
    // pub fn ConstructNetClient(&self) -> (res:(bool,Option<NetClient>))
    //     requires
    //     self.netClient.get_Some_0().ok(),
    //     self.replica.constants.valid()
    //     ensures
    //     res.0 ==> res.1.is_Some()
    //     && res.1.get_Some_0().valid()
    //     && res.1.get_Some_0().end_point === self.replica.constants.all.config.replica_ids[self.replica.constants.my_index as int],
    //     // res.1.get_Some_0().env() === env_
    // {
    //     let constants = self.replica.constants.clone();
    //     let my_ep = constants.all.config.replica_ids[constants.my_index as usize];
    //     let ip_byte_array = my_ep;

    //     // assert(my_ep.valid_public_key());

    //     if !my_ep.valid_public_key() {
    //         return (false, None);
    //     }

    //     // let (ok_udp, udp_client) = NetCLient::Construct(ip_endpoint, env_);
    //     // if !ok_udp {
    //     //     return (false, None);
    //     // }

    //     // assert(udp_client.end_point() === my_ep);

    //     (true, Some(NetClient{end_point: my_ep,..self.netClient.get_Some_0()}))
    // }

    // pub open spec fn received_packet_properties(
    //     &self,
    //     cpacket: CPacket,
    //     net_event0: NetEvent,
    //     io0: RslIo,
    // ) -> bool
    // recommends
    //     self.replica.constants.all.config.valid(),
    // {
    //         cpacket.valid()
    //         // paxos_endpoint_is_valid(cpacket.src, replica.constants.all.config),
    //         // && io0.is_lio_op_receive()
    //         // && net_event0.abs
    //         // && io0 == abstractify_udp_event_to_rsl_io(net_event0)
    //         // && net_event0.is_lio_op_receive()
    //         // && abstractify_c_packet_to_rsl_packet(cpacket) == abstractify_net_packet_to_rsl_packet(net_event0.r)
    // }

    #[verifier::external_body]
    pub fn Replica_Init(constants:CReplicaConstants) -> (rc:Self)
        requires constants.valid(),
        ensures 
            rc.replica.constants == constants,
            rc.valid(),
    {
        let r = CReplica::CReplicaInit(constants.clone_up_to_view());
        ReplicaImpl{
            replica:r,
            nextActionIndex:0,
            localAddr:constants.all.config.replica_ids[constants.my_index as usize].clone_up_to_view(),
        }
    }

    }

}
