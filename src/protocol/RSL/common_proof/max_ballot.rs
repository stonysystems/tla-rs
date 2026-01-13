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
    pub proof fn lemma_VotePrecedesMaxBal(
        b: Behavior<RslState>,
        c: LConstants,
        i: int,
        idx: int,
        opn: OperationNumber
    )
        requires
            IsValidBehaviorPrefix(b, c, i),
            0 <= i,
            0 <= idx < b[i].replicas.len(),
            b[i].replicas[idx].replica.acceptor.votes.contains_key(opn),
        ensures
            BalLeq(
                b[i].replicas[idx].replica.acceptor.votes[opn].max_value_bal,
                b[i].replicas[idx].replica.acceptor.max_bal
            ),
        decreases i,
    {
        if i == 0 {
            return;
        }
    
        lemma_ReplicaConstantsAllConsistent(b, c, i, idx);
        lemma_ReplicaConstantsAllConsistent(b, c, i - 1, idx);
        lemma_AssumptionsMakeValidTransition(b, c, i - 1);
    
        let s = b[i - 1].replicas[idx].replica.acceptor;
        let s_prime = b[i].replicas[idx].replica.acceptor;
    
        if s_prime == s {
            lemma_VotePrecedesMaxBal(b, c, i - 1, idx, opn);
            return;
        }
    
        let ios = lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i - 1, idx);
        if s.votes.contains_key(opn) {
            lemma_VotePrecedesMaxBal(b, c, i - 1, idx, opn);
        }
    }
}