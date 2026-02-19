// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

use crate::protocol::LeaderElection::election::*;
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
    pub waiting_answer: bool,
    pub waiting_node: u64,
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
            waiting_answer: self.waiting_answer,
            waiting_node: self.waiting_node as int,
        }
    }
}

pub struct CConstants {
    pub nodes: HashSet<u64>,
    pub num_nodes: u64,
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

#[derive(Clone)]
pub enum CElectionMessage {
    Election {
        sender: u64,
    },
    Answer {
        responder: u64,
    },
    Coordinator {
        leader: u64,
    },
}

impl CElectionMessage {
    pub open spec fn valid(&self) -> bool {
        match self {
            CElectionMessage::Election { sender } => true,
            CElectionMessage::Answer { responder } => true,
            CElectionMessage::Coordinator { leader } => true,
        }
    }
}

impl View for CElectionMessage {
    type V = LElectionMessage;

    open spec fn view(&self) -> LElectionMessage {
        match self {
            CElectionMessage::Election { sender } => LElectionMessage::Election { sender: *sender as int },
            CElectionMessage::Answer { responder } => LElectionMessage::Answer { responder: *responder as int },
            CElectionMessage::Coordinator { leader } => LElectionMessage::Coordinator { leader: *leader as int },
        }
    }
}

} // verus!
