// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

use crate::protocol::PBFT::pbft::*;
use crate::protocol::PBFT::types::*;
use vstd::prelude::*;

verus! {

#[derive(Clone)]
pub struct CState {
    pub view: u64,
    pub phase: CPhase,
    pub prepare_count: u64,
    pub commit_count: u64,
    pub seq_num: u64,
    pub is_primary: bool,
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
            view: self.view as int,
            phase: self.phase@,
            prepare_count: self.prepare_count as int,
            commit_count: self.commit_count as int,
            seq_num: self.seq_num as int,
            is_primary: self.is_primary,
        }
    }
}

#[derive(Clone)]
pub struct CConstants {
    pub f: u64,
    pub n: u64,
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
            f: self.f as int,
            n: self.n as int,
        }
    }
}

#[derive(Clone)]
pub enum CPhase {
    PrePrepare,
    Prepare,
    Commit,
    Replied,
}

impl CPhase {
    pub open spec fn valid(&self) -> bool {
        match self {
            CPhase::PrePrepare => true,
            CPhase::Prepare => true,
            CPhase::Commit => true,
            CPhase::Replied => true,
        }
    }
}

impl View for CPhase {
    type V = LPhase;

    open spec fn view(&self) -> LPhase {
        match self {
            CPhase::PrePrepare => LPhase::PrePrepare,
            CPhase::Prepare => LPhase::Prepare,
            CPhase::Commit => LPhase::Commit,
            CPhase::Replied => LPhase::Replied,
        }
    }
}

} // verus!
