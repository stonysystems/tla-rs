use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use crate::protocol::RSL::replica::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::message::*;
use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::parameters::*;

use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;

verus! {
    pub struct RslState {
        pub constants:LConstants,
        pub environment:LEnvironment<AbstractEndPoint, RslMessage>,
        pub replicas:Seq<LScheduler>,
        pub clients:Seq<AbstractEndPoint>,
    }

    pub open spec fn RslMapsComplete(ps:RslState) -> bool
    {
        ps.replicas.len() == ps.constants.config.replica_ids.len()
    }

    pub open spec fn RslConstantsUnchanged(ps:RslState, ps_:RslState) -> bool
    {
      &&& ps_.replicas.len() == ps.replicas.len()
      &&& ps_.clients == ps.clients
      &&& ps_.constants == ps.constants
    }

    pub open spec fn RslInit(con:LConstants, ps:RslState) -> bool 
    {
        &&& WellFormedLConfiguration(con.config)
        &&& WFLParameters(con.params)
        &&& ps.constants == con
        &&& LEnvironment_Init(ps.environment)
        &&& RslMapsComplete(ps)
        &&& (forall |i:int| 0 <= i < con.config.replica_ids.len() ==> LSchedulerInit(ps.replicas[i], LReplicaConstants{my_index:i, all:con}))
    }

    pub open spec fn RslNextCommon(ps:RslState, ps_:RslState) -> bool
    {
        &&& RslMapsComplete(ps)
        &&& RslConstantsUnchanged(ps, ps_)
        &&& LEnvironment_Next(ps.environment, ps_.environment)
    }

    pub open spec fn RslNextOneReplica(ps:RslState, ps_:RslState, idx:int, ios:Seq<RslIo>) -> bool
    {
        &&& RslNextCommon(ps, ps_)
        &&& 0 <= idx < ps.constants.config.replica_ids.len()
        &&& LSchedulerNext(ps.replicas[idx], ps_.replicas[idx], ios)
        &&& ps.environment.nextStep == LEnvStep::LEnvStepHostIos{actor:ps.constants.config.replica_ids[idx], ios:ios}
        &&& ps_.replicas == ps.replicas.update(idx, ps_.replicas[idx])
    }

    pub open spec fn RslNextEnvironment(ps:RslState, ps_:RslState) -> bool
    {
        &&& RslNextCommon(ps, ps_)
        &&& !(ps.environment.nextStep is LEnvStepHostIos)
        &&& ps_.replicas == ps.replicas
    }

    pub open spec fn RslNextOneExternal(ps:RslState, ps_:RslState, eid:AbstractEndPoint, ios:Seq<RslIo>) -> bool
    {
        &&& RslNextCommon(ps, ps_)
        &&& !ps.constants.config.replica_ids.contains(eid)
        &&& ps.environment.nextStep == LEnvStep::LEnvStepHostIos{actor:eid, ios:ios}
        &&& ps_.replicas == ps.replicas
    }

    pub open spec fn RslNext(ps:RslState, ps_:RslState) -> bool
    {
        ||| (exists |idx:int, ios:Seq<RslIo>| RslNextOneReplica(ps, ps_, idx, ios))
        ||| (exists |eid:AbstractEndPoint, ios:Seq<RslIo>| RslNextOneExternal(ps, ps_, eid, ios))
        ||| RslNextEnvironment(ps, ps_)
    }
}