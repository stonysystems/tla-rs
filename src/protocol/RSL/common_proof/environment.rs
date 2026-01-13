use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::replica::*;
use crate::protocol::RSL::common_proof::assumptions::*;
use crate::protocol::RSL::common_proof::constants::*;

use crate::common::logic::temporal_s::*;
use crate::common::logic::heuristics_i::*;
use crate::common::framework::environment_s::*;
use crate::common::framework::environment_s::LEnvStep;
use crate::common::native::io_s::*;
use crate::common::collections::maps2::*;

verus!{
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