use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::election::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::common_proof::assumptions::*;
use crate::protocol::RSL::common_proof::constants::*;
use crate::protocol::RSL::common_proof::actions::*;
use crate::protocol::RSL::common_proof::packet_sending::*;

use crate::common::logic::temporal_s::*;
use crate::common::logic::heuristics_i::*;
use crate::common::framework::environment_s::*;
use crate::common::framework::environment_s::LEnvStep;
use crate::common::native::io_s::*;
use crate::common::collections::maps2::*;

verus!{
    pub proof fn lemma_max_balISent1aHasMeAsProposer(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        idx:int
    )
        requires IsValidBehaviorPrefix(b, c, i),
                0 <= i,
                0 <= idx < b[i].replicas.len(),
        ensures b[i].replicas[idx].replica.proposer.max_ballot_i_sent_1a.proposer_id == idx,
                b[i].replicas[idx].replica.proposer.max_ballot_i_sent_1a.seqno >= 0,
        decreases i
    {
        if i > 0
        {
          lemma_ConstantsAllConsistent(b, c, i-1);
          lemma_ConstantsAllConsistent(b, c, i);
          lemma_max_balISent1aHasMeAsProposer(b, c, i-1, idx);
      
          if b[i].replicas[idx].replica.proposer.max_ballot_i_sent_1a != b[i-1].replicas[idx].replica.proposer.max_ballot_i_sent_1a
          {
            let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
          }
        }
    }
    
    pub proof fn lemma_Received1bPacketsAreFrommax_balISent1a(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        idx: int
    )
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            0 <= idx < b[i].replicas.len(),
        ensures
            ({
                let s = b[i].replicas[idx].replica.proposer;
                &&&(forall |p: RslPacket| s.received_1b_packets.contains(p) ==> 
                    p.msg is RslMessage1b &&
                    p.msg->bal_1b == s.max_ballot_i_sent_1a &&
                    c.config.replica_ids.contains(p.src) &&
                    b[i].environment.sentPackets.contains(p))
                &&& (forall |p1: RslPacket, p2: RslPacket| s.received_1b_packets.contains(p1) && s.received_1b_packets.contains(p2)
                          ==> p1 == p2 || p1.src != p2.src)
            }),
        decreases i
    {
        if i > 0 {
            lemma_ConstantsAllConsistent(b, c, i - 1);
            lemma_AssumptionsMakeValidTransition(b, c, i - 1);
            lemma_Received1bPacketsAreFrommax_balISent1a(b, c, i - 1, idx);
    
            let s = b[i - 1].replicas[idx].replica.proposer;
            let s_prime = b[i].replicas[idx].replica.proposer;
    
            assert forall |p: RslPacket| s_prime.received_1b_packets.contains(p)
                implies p.msg is RslMessage1b
                    && p.msg->bal_1b == s.max_ballot_i_sent_1a
                    && b[i].environment.sentPackets.contains(p)
            by {
                if !s.received_1b_packets.contains(p) {
                    let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i - 1, idx);
                    lemma_PacketProcessedImpliesPacketSent(b[i - 1], b[i], idx, ios, p);
                }
            };
    
            assert forall |p1: RslPacket, p2: RslPacket|
                s_prime.received_1b_packets.contains(p1)
                && s_prime.received_1b_packets.contains(p2)
                implies p1 == p2 || p1.src != p2.src
            by {
                if !s.received_1b_packets.contains(p1) || !s.received_1b_packets.contains(p2) {
                    let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i - 1, idx);
                    // Possibly additional reasoning here
                }
            };
        }
    }
  
}