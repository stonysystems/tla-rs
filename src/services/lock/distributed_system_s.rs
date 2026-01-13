#![allow(unused_imports)]
use std::collections::HashMap;

use crate::common::framework::args_t::{abstractify_args, Args};
use crate::common::framework::environment_s::{
    LEnvStep, LEnvironment, LEnvironment_Init, LEnvironment_Next, LHostInfo, LPacket,
};
use crate::common::logic::*;
use crate::common::native::io_s::*;
use crate::implementation::common::cmd_line_parser_i::{parse_args, parse_end_points};
use crate::implementation::lock::host_i::HostState;
use crate::implementation::lock::host_s::EventResults;
use crate::implementation::lock::message_i::abstractify_net_packet_to_lock_packet;
use crate::implementation::lock::netlock_i::abstractify_raw_log_to_ios;
use crate::implementation::lock::node_i::{valid_config, ConcreteConfig};
use crate::protocol::lock::distributed_system_procotol_i::AbstractLSState;
use crate::protocol::lock::node::{AbstractConfig, AbstractNode};
use crate::protocol::lock::types::{LockEnvironment, LockIo, LockMessage, LockPacket};
use builtin::*;
use builtin_macros::*;
use vstd::hash_map::HashMapWithView;
use vstd::view::*;
use vstd::{modes::*, prelude::*, seq::*, set::*, *};

verus! {
    pub type ConcreteEnvironment = LEnvironment<AbstractEndPoint, Seq<u8>>;

    pub type ConcreteEnvStep = LEnvStep<AbstractEndPoint, Seq<u8>>;

    pub open spec fn l_env_step_is_abstractable(step: ConcreteEnvStep) -> bool {
        match step {
            LEnvStep::LEnvStepHostIos{actor, ios} => true,
            LEnvStep::LEnvStepDeliverPacket{p} => true,
            LEnvStep::LEnvStepAdvanceTime => true,
            LEnvStep::LEnvStepStutter => true,
        }
    }

    pub open spec fn abstractify_concrete_env_step(step: ConcreteEnvStep) -> LEnvStep<AbstractEndPoint, LockMessage>
        recommends l_env_step_is_abstractable(step)
    {
        match step {
            LEnvStep::LEnvStepHostIos{actor, ios} => LEnvStep::LEnvStepHostIos{actor, ios: abstractify_raw_log_to_ios(ios)},
            LEnvStep::LEnvStepDeliverPacket{p} => LEnvStep::LEnvStepDeliverPacket{p: abstractify_net_packet_to_lock_packet(p)},
            LEnvStep::LEnvStepAdvanceTime => LEnvStep::LEnvStepAdvanceTime{},
            LEnvStep::LEnvStepStutter => LEnvStep::LEnvStepStutter{},
        }
    }

    pub open spec fn concrete_env_is_abstractable(environment: ConcreteEnvironment) -> bool {
        &&& l_env_step_is_abstractable(environment.nextStep)
        &&& environment.sentPackets.finite()
    }

    pub open spec fn abstractify_concrete_env_sent_packets(sent: Set<NetPacket>) -> Set<LockPacket>
    {
        sent.map(|packet| abstractify_net_packet_to_lock_packet(packet))
    }

    pub open spec fn abstractify_concrete_environment(environment: ConcreteEnvironment) -> LockEnvironment
        recommends concrete_env_is_abstractable(environment)
    {
        LEnvironment{
            time: environment.time,
            sentPackets: abstractify_concrete_env_sent_packets(environment.sentPackets),
            hostInfo: map![],
            nextStep: abstractify_concrete_env_step(environment.nextStep),
        }
    }

    pub struct DSStateLock {
        pub config: ConcreteConfig,
        pub environment: ConcreteEnvironment,
        pub servers: Map<AbstractEndPoint, HostState>,
    }

    pub open spec fn valid_physical_environment(step:LEnvStep<AbstractEndPoint, Seq<u8>>) -> bool
    {
        match step {
            LEnvStep::LEnvStepHostIos{actor, ios} => {
                forall |io|#![trigger ios.contains(io), ValidPhysicalIo(io)] ios.contains(io) ==> ValidPhysicalIo(io)
            },
            _ => true,
        }
    }


    impl DSStateLock {
        pub open spec fn abstractable(self) -> bool {
            &&& valid_config(self.config)
            // TODO: maybe this trigger needs a change
            &&& forall |r: AbstractEndPoint| #![auto] abstractify_end_points(self.config).contains(r) ==> self.servers.contains_key(r)
            &&& self.environment.sentPackets.finite()
            &&& self.servers.dom().finite()
        }

        pub open spec fn view(self) -> AbstractLSState {
            AbstractLSState{
                environment: abstractify_concrete_environment(self.environment),
                servers: self.servers.map_values(|host_state: HostState| host_state@),
            }
        }

        pub open spec fn init_requires(s: Self, config: ConcreteConfig) -> bool {
            &&& abstractify_end_points(s.config) =~= abstractify_end_points(config)
            &&& s.servers.dom() =~= abstractify_end_points(s.config).to_set()
            &&& s.servers.dom().finite()
            &&& valid_config(s.config)
            &&& LEnvironment_Init(s.environment)
            &&& (forall |id: AbstractEndPoint| #![auto] s.servers.contains_key(id) ==> HostState::host_init(s.servers[id], abstractify_end_points(s.config), id))
        }

        pub open spec fn next_one_server_requires(s: Self, next_s: Self, id: AbstractEndPoint, ios: Seq<NetEvent>) -> bool {
            &&& s.servers.contains_key(id)
            &&& next_s.servers.contains_key(id)
            &&& HostState::next(s.servers[id]@, next_s.servers[id]@, ios)
            &&& next_s.servers =~= s.servers.insert(id, next_s.servers[id])
            &&& s.servers.dom().finite()
            &&& next_s.servers.dom().finite()
        }

        pub open spec fn next_requires(s: Self, next_s: Self) -> bool {
            &&& abstractify_end_points(s.config) =~= abstractify_end_points(next_s.config)
            &&& LEnvironment_Next(s.environment, next_s.environment)
            &&& valid_physical_environment(s.environment.nextStep)
            &&& {
                if s.environment.nextStep is LEnvStepHostIos && s.servers.contains_key(s.environment.nextStep->actor) {
                    Self::next_one_server_requires(s, next_s, s.environment.nextStep->actor, s.environment.nextStep->ios)
                } else {
                    s.servers =~= next_s.servers
                }
            }
        }
    }
}
