#![allow(unused_imports)]
use super::environment_s::*;
use super::host_s::*;
use crate::common::logic::*;
use crate::common::native::io_s::*;
use builtin::*;
use builtin_macros::*;
use vstd::{modes::*, prelude::*, seq::*, *};

verus! {
    // Initially I wanted to use traits as a way to implement abstract modules. However, traits are very limited in
    // Verus at the time of writing, and you can't add additional constraints on the structs that implement the trait,
    // defeating the idea of an abstract module. This code is now moved to the service folder.

    // pub struct DS_State<H_s:HostSpec> {
    //     pub config: H_s::ConcreteConfiguration,
    //     pub environment: LEnvironment<AbstractEndPoint, Seq<u8>>,
    //     pub servers: Map<AbstractEndPoint, H_s::HostState>,
    // }

    // pub trait DistributedSystem<H_s: HostSpec> {
    //     open spec fn support_ValidPhysicalEnvironmentStep(ios: Seq<LIoOp<AbstractEndPoint, Seq<u8>>>) -> bool {
    //         forall|i:LIoOp<AbstractEndPoint, Seq<u8>>| #![trigger ios.contains(i), ValidPhysicalIo(i)] ios.contains(i) ==> ValidPhysicalIo(i)
    //     }

    //     open spec fn ValidPhysicalEnvironmentStep(step: LEnvStep<AbstractEndPoint, Seq<u8>>) -> bool {
    //         match step {
    //             LEnvStep::LEnvStepHostIos { actor, ios } => Self::support_ValidPhysicalEnvironmentStep(ios),
    //             _ => false
    //         }
    //         // step matches LEnvStep::LEnvStepHostIos{actor: a, ios: _ios} ==> // why doesnt this wor
    //     }

    //    // BUG: this works but subbing in the predicate directly doesn't ????
    //    open spec fn support_DS_Init(s: DS_State<H_s>, config: H_s::ConcreteConfiguration) -> bool {
    //      forall |id: AbstractEndPoint| #![auto] s.servers.contains_key(id) ==> H_s::HostInit(s.servers[id], config, id)
    //    }

    //    open spec fn DS_Init(s: DS_State<H_s>, config: H_s::ConcreteConfiguration) -> bool {
    //      &&& s.config == config
    //      &&& H_s::ConcreteConfigToServers(s.config) == s.servers.dom()
    //      &&& H_s::ConcreteConfigInit(s.config)
    //      &&& LEnvironment_Init(s.environment)
    //      &&& Self::support_DS_Init(s, config)
    //    }

    //    open spec fn DS_NextOneServer(s:DS_State<H_s>, s_:DS_State<H_s>, id:AbstractEndPoint, ios:Seq<LIoOp<AbstractEndPoint,Seq<u8>>>) -> bool
    //    recommends s.servers.contains_key(id)
    //    {
    //     &&& s_.servers.contains_key(id)
    //     &&& H_s::HostNext(s.servers[id], s_.servers[id], ios)
    //     &&& s_.servers == s.servers.insert(id, s_.servers[id])
    //    }

    //    open spec fn DS_Next(s: DS_State<H_s>, s_: DS_State<H_s>) -> bool {
    //     let nextStepPredicate = match s.environment.nextStep {
    //         LEnvStep::LEnvStepHostIos { actor, ios } => Self::DS_NextOneServer(s, s_, actor, ios),
    //         _ => s_.servers == s.servers
    //     };

    //     &&& s_.config == s.config
    //     &&& LEnvironment_Next(s.environment, s_.environment)
    //     &&& Self::ValidPhysicalEnvironmentStep(s.environment.nextStep)
    //     &&& nextStepPredicate
    //    }

    // }
}
