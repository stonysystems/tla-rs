// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

use crate::common::collections::hashsets::clone_hashset_u64;
use crate::protocol::VerticalPaxos::types::*;
use crate::protocol::VerticalPaxos::vpaxos::*;
use std::collections::HashSet;
use std::sync::Arc;
use vstd::prelude::*;
use vstd::set::*;

verus! {

pub struct CState {
    pub config_num: u64,
    pub max_bal: u64,
    pub max_v_bal: u64,
    pub max_val: u64,
    pub has_voted: bool,
    pub is_active: bool,
    pub promises_rcvd: Arc<HashSet<u64>>,
    pub accepts_rcvd: Arc<HashSet<u64>>,
    pub committed: bool,
    pub committed_val: u64,
    pub witness_val: u64,
    pub has_witness: bool,
}

impl Clone for CState {
    #[verifier(external_body)]
    fn clone(&self) -> (res: Self)
    ensures
        res@ == self@,
        res.valid() == self.valid(),
        res.config_num == self.config_num,
        res.max_bal == self.max_bal,
        res.max_v_bal == self.max_v_bal,
        res.max_val == self.max_val,
        res.has_voted == self.has_voted,
        res.is_active == self.is_active,
        res.committed == self.committed,
        res.committed_val == self.committed_val,
        res.witness_val == self.witness_val,
        res.has_witness == self.has_witness,
    {
        CState {
            config_num: self.config_num,
            max_bal: self.max_bal,
            max_v_bal: self.max_v_bal,
            max_val: self.max_val,
            has_voted: self.has_voted,
            is_active: self.is_active,
            promises_rcvd: self.promises_rcvd.clone(),
            accepts_rcvd: self.accepts_rcvd.clone(),
            committed: self.committed,
            committed_val: self.committed_val,
            witness_val: self.witness_val,
            has_witness: self.has_witness,
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
            config_num: self.config_num as int,
            max_bal: self.max_bal as int,
            max_v_bal: self.max_v_bal as int,
            max_val: self.max_val as int,
            has_voted: self.has_voted,
            is_active: self.is_active,
            promises_rcvd: self.promises_rcvd@.map(|x: u64| x as int),
            accepts_rcvd: self.accepts_rcvd@.map(|x: u64| x as int),
            committed: self.committed,
            committed_val: self.committed_val as int,
            witness_val: self.witness_val as int,
            has_witness: self.has_witness,
        }
    }
}

#[derive(Clone, Copy)]
pub struct CConstants {
    pub quorum_size: u64,
    pub num_nodes: u64,
    pub node_id: u64,
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
            node_id: self.node_id as int,
        }
    }
}

#[derive(Clone, Copy)]
pub enum CVPMessage {
    Prepare {
        bal: u64,
    },
    Promise {
        bal: u64,
        v_bal: u64,
        val: u64,
    },
    Accept {
        bal: u64,
        val: u64,
    },
}

impl CVPMessage {
    pub open spec fn valid(&self) -> bool {
        match self {
            CVPMessage::Prepare { bal } => true,
            CVPMessage::Promise { bal, v_bal, val } => true,
            CVPMessage::Accept { bal, val } => true,
        }
    }
}

impl View for CVPMessage {
    type V = LVPMessage;

    open spec fn view(&self) -> LVPMessage {
        match self {
            CVPMessage::Prepare { bal } => LVPMessage::Prepare { bal: *bal as int },
            CVPMessage::Promise { bal, v_bal, val } => LVPMessage::Promise { bal: *bal as int, v_bal: *v_bal as int, val: *val as int },
            CVPMessage::Accept { bal, val } => LVPMessage::Accept { bal: *bal as int, val: *val as int },
        }
    }
}

} // verus!

