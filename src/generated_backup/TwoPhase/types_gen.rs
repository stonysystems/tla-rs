// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

use crate::protocol::TwoPhase::twophase::*;
use crate::protocol::TwoPhase::types::*;
use std::collections::HashSet;
use vstd::prelude::*;
use vstd::set::*;

verus! {

pub struct CState {
    pub rm_state: HashSet<u64>,
    pub tm_state: CTMState,
    pub tm_prepared: HashSet<u64>,
}

impl Clone for CState {
    #[verifier(external_body)]
    fn clone(&self) -> (res: Self)
    ensures
        res@ == self@,
        res.valid() == self.valid(),
    { unimplemented!() }
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
            rm_state: self.rm_state@.map(|x: u64| x as int),
            tm_state: self.tm_state@,
            tm_prepared: self.tm_prepared@.map(|x: u64| x as int),
        }
    }
}

pub struct CConstants {
    pub rm: HashSet<u64>,
}

impl Clone for CConstants {
    #[verifier(external_body)]
    fn clone(&self) -> (res: Self)
    ensures
        res@ == self@,
        res.valid() == self.valid(),
    { unimplemented!() }
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

} // verus!
