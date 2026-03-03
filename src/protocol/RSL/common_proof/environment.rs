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
    pub proof fn lemma_PacketStaysInSentPackets(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        j:int,
        p:RslPacket
    )
        requires IsValidBehaviorPrefix(b, c, j),
                 0 <= i <= j,
                 b[i].environment.sentPackets.contains(p)
        ensures  b[j].environment.sentPackets.contains(p)
        decreases j
    {
        if j == i
        {
        }
        else
        {
          lemma_PacketStaysInSentPackets(b, c, i, j-1, p);
          lemma_AssumptionsMakeValidTransition(b, c, j-1);
        }
    }

    pub proof fn lemma_sentPackets_finite(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
    )
        requires IsValidBehaviorPrefix(b, c, i),
                 0 <= i,
        ensures  b[i].environment.sentPackets.finite()
        decreases i
    {
        if i == 0 {
            // Base case: RslInit includes LEnvironment_Init which ensures sentPackets.finite()
        } else {
            lemma_sentPackets_finite(b, c, i - 1);
            lemma_AssumptionsMakeValidTransition(b, c, i - 1);
            lemma_environment_next_preserves_sentpackets_finite(
                b[i - 1].environment, b[i].environment);
        }
    }

    pub proof fn lemma_PacketSetStaysInSentPackets(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        j:int,
        packets:Set<RslPacket>
    )
        requires IsValidBehaviorPrefix(b, c, j),
                 0 <= i <= j,
                 packets <= b[i].environment.sentPackets
        ensures  packets <= b[j].environment.sentPackets
    {
        assert forall |p: RslPacket| packets.contains(p) implies b[j].environment.sentPackets.contains(p) by{
            lemma_PacketStaysInSentPackets(b, c, i, j, p);
        };
    }

}
