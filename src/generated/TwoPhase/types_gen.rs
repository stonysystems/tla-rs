// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

use crate::common::collections::hashsets::clone_hashset_u64;
use crate::protocol::TwoPhase::twophase::*;
use crate::protocol::TwoPhase::types::*;
use std::collections::HashSet;
use vstd::prelude::*;
use vstd::set::*;

verus! {

pub struct CState {
    pub tm_state: CTMState,
    pub tm_prepared: HashSet<u64>,
    pub rm_prepared: HashSet<u64>,
    pub rm_committed: HashSet<u64>,
    pub rm_aborted: HashSet<u64>,
}

impl Clone for CState {
    fn clone(&self) -> (res: Self)
    ensures
        res@ == self@,
        res.valid() == self.valid(),
        res.tm_state == self.tm_state,
    {
        CState {
            tm_state: self.tm_state,
            tm_prepared: clone_hashset_u64(&self.tm_prepared),
            rm_prepared: clone_hashset_u64(&self.rm_prepared),
            rm_committed: clone_hashset_u64(&self.rm_committed),
            rm_aborted: clone_hashset_u64(&self.rm_aborted),
        }
    }
}

impl CState {
    pub open spec fn valid(&self) -> bool {
        &&& self.tm_state.valid()
    }
}

impl View for CState {
    type V = LState;

    open spec fn view(&self) -> LState {
        LState {
            tm_state: self.tm_state@,
            tm_prepared: self.tm_prepared@.map(|x: u64| x as int),
            rm_prepared: self.rm_prepared@.map(|x: u64| x as int),
            rm_committed: self.rm_committed@.map(|x: u64| x as int),
            rm_aborted: self.rm_aborted@.map(|x: u64| x as int),
        }
    }
}

pub struct CConstants {
    pub rm: HashSet<u64>,
}

impl Clone for CConstants {
    fn clone(&self) -> (res: Self)
    ensures
        res@ == self@,
        res.valid() == self.valid(),
    {
        CConstants {
            rm: clone_hashset_u64(&self.rm),
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
            rm: self.rm@.map(|x: u64| x as int),
        }
    }
}

#[derive(Clone)]
pub enum CTPCMessage {
    Prepare,
    PreparedVote {
        rm: u64,
    },
    Commit,
    Abort,
}

impl CTPCMessage {
    pub open spec fn valid(&self) -> bool {
        match self {
            CTPCMessage::Prepare => true,
            CTPCMessage::PreparedVote { rm } => true,
            CTPCMessage::Commit => true,
            CTPCMessage::Abort => true,
        }
    }
}

impl View for CTPCMessage {
    type V = LTPCMessage;

    open spec fn view(&self) -> LTPCMessage {
        match self {
            CTPCMessage::Prepare => LTPCMessage::Prepare,
            CTPCMessage::PreparedVote { rm } => LTPCMessage::PreparedVote { rm: *rm as int },
            CTPCMessage::Commit => LTPCMessage::Commit,
            CTPCMessage::Abort => LTPCMessage::Abort,
        }
    }
}

#[derive(Clone, Copy)]
pub enum CTMState {
    Init,
    Committed,
    Aborted,
}

impl CTMState {
    pub open spec fn valid(&self) -> bool {
        match self {
            CTMState::Init => true,
            CTMState::Committed => true,
            CTMState::Aborted => true,
        }
    }
}

impl View for CTMState {
    type V = LTMState;

    open spec fn view(&self) -> LTMState {
        match self {
            CTMState::Init => LTMState::Init,
            CTMState::Committed => LTMState::Committed,
            CTMState::Aborted => LTMState::Aborted,
        }
    }
}

#[derive(Clone, Copy)]
pub enum CRMState {
    Working,
    Prepared,
    Committed,
    Aborted,
}

impl CRMState {
    pub open spec fn valid(&self) -> bool {
        match self {
            CRMState::Working => true,
            CRMState::Prepared => true,
            CRMState::Committed => true,
            CRMState::Aborted => true,
        }
    }
}

impl View for CRMState {
    type V = LRMState;

    open spec fn view(&self) -> LRMState {
        match self {
            CRMState::Working => LRMState::Working,
            CRMState::Prepared => LRMState::Prepared,
            CRMState::Committed => LRMState::Committed,
            CRMState::Aborted => LRMState::Aborted,
        }
    }
}

} // verus!
