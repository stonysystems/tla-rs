use crate::protocol::RSL::common_proof::assumptions::*;
use crate::protocol::RSL::common_proof::constants::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::replica::*;
use vstd::prelude::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};

use crate::common::collections::maps2::*;
use crate::common::framework::environment_s::LEnvStep;
use crate::common::framework::environment_s::*;
use crate::common::logic::heuristics_i::*;
use crate::common::logic::temporal_s::*;
use crate::common::native::io_s::*;

verus! {
    pub open spec fn PacketProcessedViaIos(
        ps:RslState,
        ps_:RslState,
        p:RslPacket,
        idx:int,
        ios:Seq<RslIo>
    ) -> bool
    {
        &&& ios.len() > 0
        &&& LIoOp::Receive{r:p} == ios[0]
        &&& 0 <= idx < ps.constants.config.replica_ids.len()
        &&& p.dst == ps.constants.config.replica_ids[idx]
        &&& ps.environment.nextStep == LEnvStep::LEnvStepHostIos{actor:p.dst, ios:ios}
        &&& RslNextOneReplica(ps, ps_, idx, ios)
        &&& LReplicaNextProcessPacket(ps.replicas[idx].replica, ps_.replicas[idx].replica, ios)
    }

    pub open spec fn PacketProcessedDuringAction(
        ps:RslState,
        p:RslPacket
    ) -> bool
    {
        ps.environment.nextStep is LEnvStepHostIos && ps.environment.nextStep->ios.contains(LIoOp::Receive{r:p})
    }

    pub open spec fn PacketSentDuringAction(
        ps:RslState,
        p:RslPacket
    ) -> bool
    {
        ps.environment.nextStep is LEnvStepHostIos && ps.environment.nextStep->ios.contains(LIoOp::Send{s:p})
    }

    pub proof fn lemma_ActionThatChangesReplicaIsThatReplicasAction(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        host_index:int
    ) -> (ios:Seq<RslIo>)
        requires IsValidBehaviorPrefix(b, c, i+1),
                 0 <= i,
                 0 <= host_index < b[i].replicas.len(),
                 0 <= host_index < b[i+1].replicas.len(),
                 b[i+1].replicas[host_index] != b[i].replicas[host_index],
        ensures b[i].environment.nextStep is LEnvStepHostIos,
                0 <= host_index < c.config.replica_ids.len(),
                b[i].environment.nextStep->actor == c.config.replica_ids[host_index],
                ios == b[i].environment.nextStep->ios,
                RslNext(b[i], b[i+1]),
                RslNextOneReplica(b[i], b[i+1], host_index, ios),
    {
        lemma_AssumptionsMakeValidTransition(b, c, i);
        lemma_ConstantsAllConsistent(b, c, i);
        assert(RslNext(b[i], b[i+1]));
        let ios = choose |ios:Seq<RslIo>| #![trigger  RslNextOneReplica(b[i], b[i+1], host_index, ios)] RslNextOneReplica(b[i], b[i+1], host_index, ios);
        ios
    }


    pub proof fn lemma_PacketProcessedImpliesPacketSent(
        ps:RslState,
        ps_:RslState,
        idx:int,
        ios:Seq<RslIo>,
        inp:RslPacket
    )
        requires RslNextOneReplica(ps, ps_, idx, ios),
                 ios.contains(LIoOp::Receive{r:inp})
        ensures  ps.environment.sentPackets.contains(inp)
    {
        let id = ps.constants.config.replica_ids[idx];
        let e = ps.environment;
        let e_ = ps_.environment;

        assert(IsValidLIoOp(LIoOp::Receive{r:inp}, id, ps.environment));
        assert(e.nextStep == LEnvStep::LEnvStepHostIos{actor:ps.constants.config.replica_ids[idx], ios:ios});

        let pkts = ExtractSentPacketsFromIos(ios);
        // assume(forall |p:RslPacket| pkts.contains(p) <==> ios.contains(LIoOp::Send{s:p}));
        assert(e.sentPackets.contains(inp));
    }


    pub proof fn lemma_PacketProcessedImpliesPacketSentAlt(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        idx:int,
        inp:RslPacket
    )
        requires IsValidBehaviorPrefix(b, c, i+1),
                 0 <= i,
                 0 <= idx < c.config.replica_ids.len(),
                 b[i].environment.nextStep is LEnvStepHostIos,
                 b[i].environment.nextStep->actor == c.config.replica_ids[idx],
                 b[i].environment.nextStep->ios.contains(LIoOp::Receive{r:inp}),
        ensures b[i].environment.sentPackets.contains(inp)
    {
        let ps = b[i];
        let ps_ = b[i+1];

        lemma_AssumptionsMakeValidTransition(b, c, i);
        lemma_ConstantsAllConsistent(b, c, i);

        let id = ps.constants.config.replica_ids[idx];
        let e = ps.environment;
        let e_ = ps_.environment;

        assert(IsValidLIoOp(LIoOp::Receive{r:inp}, id, ps.environment));
        assert(e.sentPackets.contains(inp));
    }
}
