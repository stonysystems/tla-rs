// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

use crate::common::collections::hashsets::clone_hashset;
use crate::protocol::LeaderElection::types::*;
use std::collections::HashSet;
use vstd::prelude::*;
use vstd::set::*;

verus! {

pub struct CState {
    pub electing: HashSet<u64>,
    pub has_leader: bool,
    pub leader: u64,
    pub alive: HashSet<u64>,
    pub has_highest: bool,
    pub highest_heard: u64,
}

impl Clone for CState {
    #[verifier(external_body)]
    fn clone(&self) -> Self {
        CState {
            electing: self.electing.clone(),
            has_leader: self.has_leader,
            leader: self.leader,
            alive: self.alive.clone(),
            has_highest: self.has_highest,
            highest_heard: self.highest_heard,
        }
    }
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
            electing: self.electing@.map(|x: u64| x as int),
            has_leader: self.has_leader,
            leader: self.leader as int,
            alive: self.alive@.map(|x: u64| x as int),
            has_highest: self.has_highest,
            highest_heard: self.highest_heard as int,
        }
    }
}

pub struct CConstants {
    pub nodes: HashSet<u64>,
    pub num_nodes: u64,
}

impl Clone for CConstants {
    #[verifier(external_body)]
    fn clone(&self) -> Self {
        CConstants {
            nodes: self.nodes.clone(),
            num_nodes: self.num_nodes,
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
            nodes: self.nodes@.map(|x: u64| x as int),
            num_nodes: self.num_nodes as int,
        }
    }
}

#[derive(Clone)]
pub enum CNodeState {
    Normal,
    Election,
    Leader,
}

impl CNodeState {
    pub open spec fn valid(&self) -> bool {
        match self {
            CNodeState::Normal => true,
            CNodeState::Election => true,
            CNodeState::Leader => true,
        }
    }
}

impl View for CNodeState {
    type V = LNodeState;

    open spec fn view(&self) -> LNodeState {
        match self {
            CNodeState::Normal => LNodeState::Normal,
            CNodeState::Election => LNodeState::Election,
            CNodeState::Leader => LNodeState::Leader,
        }
    }
}

} // verus!
