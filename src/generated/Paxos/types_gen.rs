// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

use crate::common::collections::hashsets::clone_hashset_u64;
use crate::protocol::Paxos::paxos::*;
use crate::protocol::Paxos::types::*;
use std::collections::HashSet;
use vstd::prelude::*;
use vstd::set::*;

verus! {

pub struct CState {
    pub promised_bal: u64,
    pub accepted_bal: u64,
    pub accepted_val: u64,
    pub proposer_bal: u64,
    pub phase: CPhase,
    pub promises_rcvd: HashSet<u64>,
    pub highest_accepted_bal: u64,
    pub highest_accepted_val: u64,
    pub proposed_val: u64,
    pub accepts_rcvd: HashSet<u64>,
    pub decided_val: u64,
}

impl Clone for CState {
    fn clone(&self) -> (res: Self)
    ensures
        res@ == self@,
        res.valid() == self.valid(),
        res.promised_bal == self.promised_bal,
        res.accepted_bal == self.accepted_bal,
        res.accepted_val == self.accepted_val,
        res.proposer_bal == self.proposer_bal,
        res.phase == self.phase,
        res.highest_accepted_bal == self.highest_accepted_bal,
        res.highest_accepted_val == self.highest_accepted_val,
        res.proposed_val == self.proposed_val,
        res.decided_val == self.decided_val,
    {
        CState {
            promised_bal: self.promised_bal,
            accepted_bal: self.accepted_bal,
            accepted_val: self.accepted_val,
            proposer_bal: self.proposer_bal,
            phase: self.phase,
            promises_rcvd: clone_hashset_u64(&self.promises_rcvd),
            highest_accepted_bal: self.highest_accepted_bal,
            highest_accepted_val: self.highest_accepted_val,
            proposed_val: self.proposed_val,
            accepts_rcvd: clone_hashset_u64(&self.accepts_rcvd),
            decided_val: self.decided_val,
        }
    }
}

impl CState {
    pub open spec fn valid(&self) -> bool {
        &&& self.phase.valid()
    }
}

impl View for CState {
    type V = LState;

    open spec fn view(&self) -> LState {
        LState {
            promised_bal: self.promised_bal as int,
            accepted_bal: self.accepted_bal as int,
            accepted_val: self.accepted_val as int,
            proposer_bal: self.proposer_bal as int,
            phase: self.phase@,
            promises_rcvd: self.promises_rcvd@.map(|x: u64| x as int),
            highest_accepted_bal: self.highest_accepted_bal as int,
            highest_accepted_val: self.highest_accepted_val as int,
            proposed_val: self.proposed_val as int,
            accepts_rcvd: self.accepts_rcvd@.map(|x: u64| x as int),
            decided_val: self.decided_val as int,
        }
    }
}

pub struct CConstants {
    pub acceptors: HashSet<u64>,
    pub quorum_size: u64,
    pub node_id: u64,
}

impl Clone for CConstants {
    fn clone(&self) -> (res: Self)
    ensures
        res@ == self@,
        res.valid() == self.valid(),
        res.quorum_size == self.quorum_size,
        res.node_id == self.node_id,
    {
        CConstants {
            acceptors: clone_hashset_u64(&self.acceptors),
            quorum_size: self.quorum_size,
            node_id: self.node_id,
        }
    }
}

impl CConstants {
    pub open spec fn valid(&self) -> bool {
        true
    }
}

impl View for CConstants {
    type V = LConstants;

    open spec fn view(&self) -> LConstants {
        LConstants {
            acceptors: self.acceptors@.map(|x: u64| x as int),
            quorum_size: self.quorum_size as int,
            node_id: self.node_id as int,
        }
    }
}

#[derive(Clone, Copy)]
pub enum CPhase {
    Idle,
    Phase1,
    Phase2,
    Decided,
}

impl CPhase {
    pub open spec fn valid(&self) -> bool {
        match self {
            CPhase::Idle => true,
            CPhase::Phase1 => true,
            CPhase::Phase2 => true,
            CPhase::Decided => true,
        }
    }
}

impl View for CPhase {
    type V = LPhase;

    open spec fn view(&self) -> LPhase {
        match self {
            CPhase::Idle => LPhase::Idle,
            CPhase::Phase1 => LPhase::Phase1,
            CPhase::Phase2 => LPhase::Phase2,
            CPhase::Decided => LPhase::Decided,
        }
    }
}

} // verus!
