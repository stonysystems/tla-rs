use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use crate::protocol::RSL::distributed_system::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::environment::*;

use crate::protocol::RSL::common_proof::assumptions::*;

use crate::common::logic::temporal_s::*;
use crate::common::logic::heuristics_i::*;

verus!{
    pub open spec fn ConstantsAllConsistentInv(ps:RslState) -> bool
    {
        &&& ps.constants.config.replica_ids.len() == ps.replicas.len()
        &&& forall |idx:int| #![trigger ps.replicas[idx].replica.constants] 0 <= idx < ps.constants.config.replica_ids.len() ==>
            && ps.replicas[idx].replica.constants.my_index == idx
            && ps.replicas[idx].replica.constants.all == ps.constants
            && ps.replicas[idx].replica.proposer.constants == ps.replicas[idx].replica.constants
            && ps.replicas[idx].replica.proposer.election_state.constants == ps.replicas[idx].replica.constants
            && ps.replicas[idx].replica.acceptor.constants == ps.replicas[idx].replica.constants
            && ps.replicas[idx].replica.learner.constants == ps.replicas[idx].replica.constants
            && ps.replicas[idx].replica.executor.constants == ps.replicas[idx].replica.constants
    }

    pub proof fn lemma_AssumptionsMakeValidTransition(
        b:Behavior<RslState>,
        c:LConstants,
        i:int
        )
        requires IsValidBehaviorPrefix(b, c, i+1),
                 0 <= i
        ensures  RslNext(b[i], b[i+1])
    {
    }

    pub proof fn lemma_ReplicasSize(
        b:Behavior<RslState>,
        c:LConstants,
        i:int
    )
        requires IsValidBehaviorPrefix(b, c, i),
                 0 <= i
        ensures  c.config.replica_ids.len() == b[i].replicas.len()
        decreases i
    {
        if i > 0
        {
            lemma_ConstantsAllConsistent(b, c, i);
            lemma_AssumptionsMakeValidTransition(b, c, i-1);
            lemma_ReplicasSize(b, c, i-1);
        }
    }

    pub proof fn lemma_ReplicaInState(
        b:Behavior<RslState>,
        c:LConstants,
        replica_index:int,
        i:int
    )
        requires IsValidBehaviorPrefix(b, c, i),
                 0 <= i,
                 0 <= replica_index < c.config.replica_ids.len()
        ensures  0 <= replica_index < b[i].replicas.len()
    {
        lemma_ReplicasSize(b, c, i);
    }

    pub proof fn lemma_ValidPrefixHolds(
        b: Behavior<RslState>,
        c: LConstants,
        i: int
    )
        requires IsValidBehaviorPrefix(b, c, i),
                 0 <= i,
        ensures IsValidBehaviorPrefix(b, c, i)
    {
        assert(IsValidBehaviorPrefix(b, c, i));
    }
    
    // #[verifier(spinoff_prover)] 
    pub proof fn lemma_ConstantsAllConsistent(
        b:Behavior<RslState>,
        c:LConstants,
        i:int
    )
        requires IsValidBehaviorPrefix(b, c, i),
                 0 <= i,
        ensures b[i].constants == c,
                ConstantsAllConsistentInv(b[i])
        decreases i
    {
        TemporalAssist();
        // lemma_ValidPrefixHolds(b, c, i); 
        if i > 0
        {
          lemma_ConstantsAllConsistent(b, c, i-1);
          lemma_AssumptionsMakeValidTransition(b, c, i-1);
        }
        // assume(b[i].constants == c);
        // assume(ConstantsAllConsistentInv(b[i]));
    }


    pub proof fn lemma_ReplicaConstantsAllConsistent(
        b:Behavior<RslState>,
        c:LConstants,
        i:int,
        idx:int
    )
        requires IsValidBehaviorPrefix(b, c, i),
                 0 <= i,
                 0 <= idx < b[i].replicas.len() || 0 <= idx < c.config.replica_ids.len() || 0 <= idx < b[i].constants.config.replica_ids.len(),
        ensures b[i].constants == c,
                ConstantsAllConsistentInv(b[i])
    {
        lemma_ConstantsAllConsistent(b, c, i);
    }
}