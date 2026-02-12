// Auto-generated concrete types by verus-transpiler
// DO NOT EDIT MANUALLY

use crate::protocol::VerticalPaxos::types::*;
use crate::protocol::VerticalPaxos::vpaxos::*;
use std::collections::HashSet;
use vstd::prelude::*;
use vstd::set::*;

verus! {

#[derive(Clone)]
pub struct CState {
    pub config_num: u64,
    pub max_bal: u64,
    pub max_v_bal: u64,
    pub max_val: u64,
    pub has_voted: bool,
    pub is_active: bool,
    pub promises_rcvd: HashSet<u64>,
    pub accepts_rcvd: HashSet<u64>,
    pub committed: bool,
    pub committed_val: u64,
    pub witness_val: u64,
    pub has_witness: bool,
    pub msgs_prepare: bool,
    pub msgs_prepare_bal: u64,
    pub msgs_promise: bool,
    pub msgs_promise_bal: u64,
    pub msgs_promise_v_bal: u64,
    pub msgs_promise_val: u64,
    pub msgs_accept: bool,
    pub msgs_accept_bal: u64,
    pub msgs_accept_val: u64,
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
            msgs_prepare: self.msgs_prepare,
            msgs_prepare_bal: self.msgs_prepare_bal as int,
            msgs_promise: self.msgs_promise,
            msgs_promise_bal: self.msgs_promise_bal as int,
            msgs_promise_v_bal: self.msgs_promise_v_bal as int,
            msgs_promise_val: self.msgs_promise_val as int,
            msgs_accept: self.msgs_accept,
            msgs_accept_bal: self.msgs_accept_bal as int,
            msgs_accept_val: self.msgs_accept_val as int,
        }
    }
}

#[derive(Clone)]
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

} // verus!
