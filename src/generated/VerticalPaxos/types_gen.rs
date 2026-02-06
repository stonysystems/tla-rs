// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

use crate::protocol::VerticalPaxos::types::*;
use crate::protocol::VerticalPaxos::vpaxos::*;
use vstd::prelude::*;

verus! {

#[derive(Clone)]
pub struct CState {
    pub config_num: u64,
    pub max_bal: u64,
    pub max_v_bal: u64,
    pub max_val: u64,
    pub has_voted: bool,
    pub is_active: bool,
}

impl CState {
    pub open spec fn valid(&self) -> bool {
        true
    }
}

impl View for CState {
    type V = LState;

    open spec fn view(&self) -> LState {
        LState {
            config_num: self.config_num as int,
            max_bal: self.max_bal as int,
            max_v_bal: self.max_v_bal as int,
            max_val: self.max_val as int,
            has_voted: self.has_voted,
            is_active: self.is_active,
        }
    }
}

#[derive(Clone)]
pub struct CConstants {
    pub quorum_size: u64,
    pub num_nodes: u64,
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
            quorum_size: self.quorum_size as int,
            num_nodes: self.num_nodes as int,
        }
    }
}

} // verus!
