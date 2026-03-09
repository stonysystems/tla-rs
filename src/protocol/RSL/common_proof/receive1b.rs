use crate::protocol::RSL::common_proof::actions::*;
use crate::protocol::RSL::common_proof::assumptions::*;
use crate::protocol::RSL::common_proof::constants::*;
use crate::protocol::RSL::common_proof::message2b::*;
use crate::protocol::RSL::common_proof::packet_sending::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::election::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::proposer::*;
use crate::protocol::RSL::replica::*;
use crate::protocol::RSL::types::*;
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

    #[verifier(external_body)]
    pub proof fn lemma_PacketInReceived1bWasSent(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        replica_idx:int,
        p:RslPacket
    )
        requires IsValidBehaviorPrefix(b, c, i),
                0 <= i,
                0 <= replica_idx < b[i].replicas.len(),
                b[i].replicas[replica_idx].replica.proposer.received_1b_packets.contains(p),
        ensures
                b[i].environment.sentPackets.contains(p),
                c.config.replica_ids.contains(p.src),
        decreases i
    {
        if i == 0
        {
          return;
        }

        lemma_ConstantsAllConsistent(b, c, i-1);
        lemma_ConstantsAllConsistent(b, c, i);
        lemma_AssumptionsMakeValidTransition(b, c, i-1);
        let s = b[i-1].replicas[replica_idx].replica.proposer;
        let s_ = b[i].replicas[replica_idx].replica.proposer;

        if s.received_1b_packets.contains(p)
        {
          lemma_PacketInReceived1bWasSent(b, c, i-1, replica_idx, p);
          assert(b[i-1].environment.sentPackets.contains(p));
          assert(b[i].environment.sentPackets.contains(p));
          return;
        }

        assert(s_.received_1b_packets.contains(p));
        let nextActionIndex = b[i].replicas[replica_idx].nextActionIndex;
        let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, replica_idx);
        assert(ios[0] is Receive);
        assert(ios[0]->r.msg is RslMessage1b);
        assert(p == ios[0]->r);
        assert(LProposerProcess1b(s, s_, ios[0]->r));
        assert(ios == b[i-1].environment.nextStep->ios);

        let e = b[i-1].environment;
        let e_ = b[i].environment;

        assert(e.nextStep is LEnvStepHostIos);
        assert(LEnvironment_PerformIos(e, e_, e.nextStep->actor, ios));
        assert(forall |io| ios.contains(io) ==> match_ios_recv(io, e.sentPackets));
        assert(ios.contains(ios[0]) && ios[0] is Receive);
        assert(match_ios_recv(ios[0], e.sentPackets));
        assert(e.sentPackets.contains(ios[0]->r));
        assert(b[i].environment.sentPackets.contains(p));
    }
}
