// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

use crate::common::collections::hashsets::clone_hashset;
use crate::protocol::Paxos::types::*;
use std::collections::HashSet;
use vstd::prelude::*;
use vstd::set::*;

verus! {

pub struct CState {
    pub max_bal: HashSet<u64>,
    pub max_v_bal: HashSet<u64>,
    pub max_val: HashSet<u64>,
    pub msg_count: u64,
}

impl Clone for CState {
    #[verifier(external_body)]
    fn clone(&self) -> Self {
        CState {
            max_bal: self.max_bal.clone(),
            max_v_bal: self.max_v_bal.clone(),
            max_val: self.max_val.clone(),
            msg_count: self.msg_count,
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
            max_bal: self.max_bal@.map(|x: u64| x as int),
            max_v_bal: self.max_v_bal@.map(|x: u64| x as int),
            max_val: self.max_val@.map(|x: u64| x as int),
            msg_count: self.msg_count as int,
        }
    }
}

pub struct CConstants {
    pub acceptors: HashSet<u64>,
    pub quorum_size: u64,
}

impl Clone for CConstants {
    #[verifier(external_body)]
    fn clone(&self) -> Self {
        CConstants {
            acceptors: self.acceptors.clone(),
            quorum_size: self.quorum_size,
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
        }
    }
}

#[derive(Clone)]
pub enum CMsgType {
    Phase1a,
    Phase1b,
    Phase2a,
    Phase2b,
}

impl CMsgType {
    pub open spec fn valid(&self) -> bool {
        match self {
            CMsgType::Phase1a => true,
            CMsgType::Phase1b => true,
            CMsgType::Phase2a => true,
            CMsgType::Phase2b => true,
        }
    }
}

impl View for CMsgType {
    type V = LMsgType;

    open spec fn view(&self) -> LMsgType {
        match self {
            CMsgType::Phase1a => LMsgType::Phase1a,
            CMsgType::Phase1b => LMsgType::Phase1b,
            CMsgType::Phase2a => LMsgType::Phase2a,
            CMsgType::Phase2b => LMsgType::Phase2b,
        }
    }
}

} // verus!
