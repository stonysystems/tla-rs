// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

use crate::protocol::EPaxos::epaxos::*;
use crate::protocol::EPaxos::types::*;
use vstd::prelude::*;

verus! {

#[derive(Clone)]
pub struct CState {
    pub ballot: u64,
    pub phase: CInstancePhase,
    pub cmd: u64,
    pub seq: u64,
    pub dep_count: u64,
    pub preaccept_count: u64,
    pub accept_count: u64,
    pub is_leader: bool,
    pub committed_count: u64,
    pub executed_count: u64,
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
            ballot: self.ballot as int,
            phase: self.phase@,
            cmd: self.cmd as int,
            seq: self.seq as int,
            dep_count: self.dep_count as int,
            preaccept_count: self.preaccept_count as int,
            accept_count: self.accept_count as int,
            is_leader: self.is_leader,
            committed_count: self.committed_count as int,
            executed_count: self.executed_count as int,
        }
    }
}

#[derive(Clone)]
pub struct CConstants {
    pub num_replicas: u64,
    pub fast_quorum_size: u64,
    pub quorum_size: u64,
    pub my_id: u64,
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
            num_replicas: self.num_replicas as int,
            fast_quorum_size: self.fast_quorum_size as int,
            quorum_size: self.quorum_size as int,
            my_id: self.my_id as int,
        }
    }
}

#[derive(Clone)]
pub enum CInstancePhase {
    Empty,
    PreAccepted,
    Accepted,
    Committed,
    Executed,
}

impl CInstancePhase {
    pub open spec fn valid(&self) -> bool {
        match self {
            CInstancePhase::Empty => true,
            CInstancePhase::PreAccepted => true,
            CInstancePhase::Accepted => true,
            CInstancePhase::Committed => true,
            CInstancePhase::Executed => true,
        }
    }
}

impl View for CInstancePhase {
    type V = LInstancePhase;

    open spec fn view(&self) -> LInstancePhase {
        match self {
            CInstancePhase::Empty => LInstancePhase::Empty,
            CInstancePhase::PreAccepted => LInstancePhase::PreAccepted,
            CInstancePhase::Accepted => LInstancePhase::Accepted,
            CInstancePhase::Committed => LInstancePhase::Committed,
            CInstancePhase::Executed => LInstancePhase::Executed,
        }
    }
}

} // verus!
