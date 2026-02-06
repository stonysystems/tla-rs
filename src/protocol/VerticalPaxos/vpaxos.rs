/// Simplified Vertical Paxos (Reconfigurable Paxos) protocol.
///
/// Models Paxos with reconfiguration from a single node's perspective:
/// 1. Prepare: Proposer sends Phase1a with ballot b
/// 2. Promise: Acceptor promises not to accept lower ballots
/// 3. Accept: Proposer sends Phase2a with ballot and value
/// 4. Accepted: Acceptor accepts the value
/// 5. Reconfigure: Move to a new configuration (higher config number)
/// 6. Sync: Transfer state to new configuration members
/// 7. Activate: New config member becomes active
use vstd::prelude::*;
use crate::protocol::VerticalPaxos::types::*;

verus! {

/// Initial state: config 0, no ballots seen, not voted, active
pub open spec fn LInit(s: LState, c: LConstants) -> bool {
    &&& s.config_num == 0
    &&& s.max_bal == 0
    &&& s.max_v_bal == 0
    &&& s.max_val == 0
    &&& s.has_voted == false
    &&& s.is_active == true
    &&& c.quorum_size >= 1
    &&& c.num_nodes >= c.quorum_size
}

/// Phase 1a: Proposer sends prepare with ballot b.
/// The node promises not to accept any ballot less than b.
pub open spec fn LPrepare(s: LState, s_: LState, c: LConstants, b: int) -> bool {
    &&& s.is_active == true
    &&& b > s.max_bal
    &&& s_.max_bal == b
    &&& s_.max_v_bal == s.max_v_bal
    &&& s_.max_val == s.max_val
    &&& s_.has_voted == s.has_voted
    &&& s_.config_num == s.config_num
    &&& s_.is_active == s.is_active
}

/// Phase 2a/2b: Accept a value v at ballot b.
/// Only accepts if b equals the current max_bal (promised ballot).
pub open spec fn LAccept(s: LState, s_: LState, c: LConstants, b: int, v: int) -> bool {
    &&& s.is_active == true
    &&& b == s.max_bal
    &&& b > s.max_v_bal
    &&& s_.max_bal == s.max_bal
    &&& s_.max_v_bal == b
    &&& s_.max_val == v
    &&& s_.has_voted == true
    &&& s_.config_num == s.config_num
    &&& s_.is_active == s.is_active
}

/// Reconfigure: Move to a new configuration.
/// Increments the config number and resets ballot tracking,
/// but preserves the accepted value (for state transfer).
pub open spec fn LReconfigure(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.is_active == true
    &&& s_.config_num == s.config_num + 1
    &&& s_.max_bal == 0
    &&& s_.max_v_bal == 0
    &&& s_.max_val == s.max_val
    &&& s_.has_voted == false
    &&& s_.is_active == true
}

/// Sync: Transfer accepted state to a new configuration member.
/// The accepting node copies the value from the old config.
/// Models the "state transfer" step of Vertical Paxos.
pub open spec fn LSync(s: LState, s_: LState, c: LConstants, new_config: int, val: int) -> bool {
    &&& s.is_active == false
    &&& new_config > s.config_num
    &&& s_.config_num == new_config
    &&& s_.max_bal == 0
    &&& s_.max_v_bal == 0
    &&& s_.max_val == val
    &&& s_.has_voted == false
    &&& s_.is_active == true
}

/// Deactivate: Node leaves the active set for reconfiguration.
/// This models a node being removed from the current configuration.
pub open spec fn LDeactivate(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.is_active == true
    &&& s_.config_num == s.config_num
    &&& s_.max_bal == s.max_bal
    &&& s_.max_v_bal == s.max_v_bal
    &&& s_.max_val == s.max_val
    &&& s_.has_voted == s.has_voted
    &&& s_.is_active == false
}

/// Next-state relation: disjunction of all transitions.
pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
    ||| exists |b: int| LPrepare(s, s_, c, b)
    ||| exists |b: int, v: int| LAccept(s, s_, c, b, v)
    ||| LReconfigure(s, s_, c)
    ||| exists |new_config: int, val: int| LSync(s, s_, c, new_config, val)
    ||| LDeactivate(s, s_, c)
}

} // verus!
