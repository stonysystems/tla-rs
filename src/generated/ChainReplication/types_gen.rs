// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

use crate::common::collections::hashsets::clone_hashset_u64;
use crate::protocol::ChainReplication::chain::*;
use crate::protocol::ChainReplication::types::*;
use std::collections::HashSet;
use std::sync::Arc;
use vstd::prelude::*;
use vstd::set::*;

verus! {

pub struct CState {
    pub role: CNodeRole,
    pub history: Arc<Vec<u64>>,
    pub pending_sent: Arc<HashSet<u64>>,
    pub committed_count: u64,
    pub obj_value: u64,
    pub has_predecessor: bool,
    pub predecessor: u64,
    pub has_successor: bool,
    pub successor: u64,
    pub alive: bool,
}

impl Clone for CState {
    #[verifier(external_body)]
    fn clone(&self) -> (res: Self)
    ensures
        res@ == self@,
        res.valid() == self.valid(),
        res.role == self.role,
        res.committed_count == self.committed_count,
        res.obj_value == self.obj_value,
        res.has_predecessor == self.has_predecessor,
        res.predecessor == self.predecessor,
        res.has_successor == self.has_successor,
        res.successor == self.successor,
        res.alive == self.alive,
    {
        CState {
            role: self.role,
            history: self.history.clone(),
            pending_sent: self.pending_sent.clone(),
            committed_count: self.committed_count,
            obj_value: self.obj_value,
            has_predecessor: self.has_predecessor,
            predecessor: self.predecessor,
            has_successor: self.has_successor,
            successor: self.successor,
            alive: self.alive,
        }
    }
}

impl CState {
    pub open spec fn valid(&self) -> bool {
        &&& self.role.valid()
    }
}

impl View for CState {
    type V = LState;

    open spec fn view(&self) -> LState {
        LState {
            role: self.role@,
            history: self.history@.map(|i: int, x: u64| x as int),
            pending_sent: self.pending_sent@.map(|x: u64| x as int),
            committed_count: self.committed_count as int,
            obj_value: self.obj_value as int,
            has_predecessor: self.has_predecessor,
            predecessor: self.predecessor as int,
            has_successor: self.has_successor,
            successor: self.successor as int,
            alive: self.alive,
        }
    }
}

#[derive(Clone)]
pub struct CConstants {
    pub node_id: u64,
    pub chain_len: u64,
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
            node_id: self.node_id as int,
            chain_len: self.chain_len as int,
        }
    }
}

#[derive(Clone, Copy)]
pub enum CNodeRole {
    Head,
    Middle,
    Tail,
}

impl CNodeRole {
    pub open spec fn valid(&self) -> bool {
        match self {
            CNodeRole::Head => true,
            CNodeRole::Middle => true,
            CNodeRole::Tail => true,
        }
    }
}

impl View for CNodeRole {
    type V = LNodeRole;

    open spec fn view(&self) -> LNodeRole {
        match self {
            CNodeRole::Head => LNodeRole::Head,
            CNodeRole::Middle => LNodeRole::Middle,
            CNodeRole::Tail => LNodeRole::Tail,
        }
    }
}

#[derive(Clone)]
pub enum CCRMessage {
    Forward {
        value: u64,
    },
    Ack {
        value: u64,
    },
}

impl CCRMessage {
    pub open spec fn valid(&self) -> bool {
        match self {
            CCRMessage::Forward { value } => true,
            CCRMessage::Ack { value } => true,
        }
    }
}

impl View for CCRMessage {
    type V = LCRMessage;

    open spec fn view(&self) -> LCRMessage {
        match self {
            CCRMessage::Forward { value } => LCRMessage::Forward { value: *value as int },
            CCRMessage::Ack { value } => LCRMessage::Ack { value: *value as int },
        }
    }
}

} // verus!
