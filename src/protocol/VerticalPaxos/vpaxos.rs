/// Simplified Vertical Paxos (Reconfigurable Paxos) protocol.
///
/// Models Paxos with reconfiguration from a single node's perspective:
/// 1. Prepare: Proposer sends Phase1a with ballot b
/// 2. Promise: Acceptor promises not to accept lower ballots
/// 3. Accept: Proposer sends Phase2a with ballot and value
/// 4. Accepted: Acceptor accepts the value
/// 5. Reconfigure: Move to a new configuration (higher config number)
/// 6. WitnessSync: Witness transfers state from old config to new
/// 7. Deactivate: Node leaves active set for reconfiguration
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
    &&& s.promises_rcvd == Set::<int>::empty()
    &&& s.accepts_rcvd == Set::<int>::empty()
    &&& s.committed == false
    &&& s.committed_val == 0
    &&& s.witness_val == 0
    &&& s.has_witness == false
    &&& s.msgs_prepare == false
    &&& s.msgs_prepare_bal == 0
    &&& s.msgs_promise == false
    &&& s.msgs_promise_bal == 0
    &&& s.msgs_promise_v_bal == 0
    &&& s.msgs_promise_val == 0
    &&& s.msgs_accept == false
    &&& s.msgs_accept_bal == 0
    &&& s.msgs_accept_val == 0
    &&& c.quorum_size >= 1
    &&& c.num_nodes >= c.quorum_size
}

/// Phase 1a: Proposer sends prepare with ballot b.
/// The node promises not to accept any ballot less than b.
pub open spec fn LPrepare(s: LState, s_: LState, c: LConstants, b: int) -> bool {
    &&& s.is_active == true
    &&& b > s.max_bal
    // Update max_bal
    &&& s_.max_bal == b
    // Send prepare message
    &&& s_.msgs_prepare == true
    &&& s_.msgs_prepare_bal == b
    // Frame
    &&& s_.max_v_bal == s.max_v_bal
    &&& s_.max_val == s.max_val
    &&& s_.has_voted == s.has_voted
    &&& s_.config_num == s.config_num
    &&& s_.is_active == s.is_active
    &&& s_.promises_rcvd == s.promises_rcvd
    &&& s_.accepts_rcvd == s.accepts_rcvd
    &&& s_.committed == s.committed
    &&& s_.committed_val == s.committed_val
    &&& s_.witness_val == s.witness_val
    &&& s_.has_witness == s.has_witness
    &&& s_.msgs_promise == s.msgs_promise
    &&& s_.msgs_promise_bal == s.msgs_promise_bal
    &&& s_.msgs_promise_v_bal == s.msgs_promise_v_bal
    &&& s_.msgs_promise_val == s.msgs_promise_val
    &&& s_.msgs_accept == s.msgs_accept
    &&& s_.msgs_accept_bal == s.msgs_accept_bal
    &&& s_.msgs_accept_val == s.msgs_accept_val
}

/// Phase 1b: Acceptor receives prepare and sends promise.
pub open spec fn LSendPromise(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.is_active == true
    &&& s.msgs_prepare == true
    &&& s.msgs_prepare_bal > s.max_bal
    // Update max_bal
    &&& s_.max_bal == s.msgs_prepare_bal
    // Send promise with current accepted state
    &&& s_.msgs_promise == true
    &&& s_.msgs_promise_bal == s.msgs_prepare_bal
    &&& s_.msgs_promise_v_bal == s.max_v_bal
    &&& s_.msgs_promise_val == s.max_val
    // Frame
    &&& s_.max_v_bal == s.max_v_bal
    &&& s_.max_val == s.max_val
    &&& s_.has_voted == s.has_voted
    &&& s_.config_num == s.config_num
    &&& s_.is_active == s.is_active
    &&& s_.promises_rcvd == s.promises_rcvd
    &&& s_.accepts_rcvd == s.accepts_rcvd
    &&& s_.committed == s.committed
    &&& s_.committed_val == s.committed_val
    &&& s_.witness_val == s.witness_val
    &&& s_.has_witness == s.has_witness
    &&& s_.msgs_prepare == s.msgs_prepare
    &&& s_.msgs_prepare_bal == s.msgs_prepare_bal
    &&& s_.msgs_accept == s.msgs_accept
    &&& s_.msgs_accept_bal == s.msgs_accept_bal
    &&& s_.msgs_accept_val == s.msgs_accept_val
}

/// Proposer receives a promise and tracks it.
pub open spec fn LReceivePromise(s: LState, s_: LState, c: LConstants, sender: int) -> bool {
    &&& s.is_active == true
    &&& s.msgs_promise == true
    &&& s.msgs_promise_bal == s.max_bal
    &&& !s.promises_rcvd.contains(sender)
    // Add sender to promises received
    &&& s_.promises_rcvd == s.promises_rcvd.insert(sender)
    // Track highest accepted value from promises
    &&& s_.max_v_bal == (if s.msgs_promise_v_bal > s.max_v_bal { s.msgs_promise_v_bal } else { s.max_v_bal })
    &&& s_.max_val == (if s.msgs_promise_v_bal > s.max_v_bal { s.msgs_promise_val } else { s.max_val })
    // Frame
    &&& s_.max_bal == s.max_bal
    &&& s_.has_voted == s.has_voted
    &&& s_.config_num == s.config_num
    &&& s_.is_active == s.is_active
    &&& s_.accepts_rcvd == s.accepts_rcvd
    &&& s_.committed == s.committed
    &&& s_.committed_val == s.committed_val
    &&& s_.witness_val == s.witness_val
    &&& s_.has_witness == s.has_witness
    &&& s_.msgs_prepare == s.msgs_prepare
    &&& s_.msgs_prepare_bal == s.msgs_prepare_bal
    &&& s_.msgs_promise == s.msgs_promise
    &&& s_.msgs_promise_bal == s.msgs_promise_bal
    &&& s_.msgs_promise_v_bal == s.msgs_promise_v_bal
    &&& s_.msgs_promise_val == s.msgs_promise_val
    &&& s_.msgs_accept == s.msgs_accept
    &&& s_.msgs_accept_bal == s.msgs_accept_bal
    &&& s_.msgs_accept_val == s.msgs_accept_val
}

/// Phase 2a/2b: Accept a value v at ballot b.
/// Only accepts if b equals the current max_bal (promised ballot).
pub open spec fn LAccept(s: LState, s_: LState, c: LConstants, b: int, v: int) -> bool {
    &&& s.is_active == true
    &&& b == s.max_bal
    &&& b > s.max_v_bal
    // Accept the value
    &&& s_.max_v_bal == b
    &&& s_.max_val == v
    &&& s_.has_voted == true
    // Send accept message
    &&& s_.msgs_accept == true
    &&& s_.msgs_accept_bal == b
    &&& s_.msgs_accept_val == v
    // Frame
    &&& s_.max_bal == s.max_bal
    &&& s_.config_num == s.config_num
    &&& s_.is_active == s.is_active
    &&& s_.promises_rcvd == s.promises_rcvd
    &&& s_.accepts_rcvd == s.accepts_rcvd
    &&& s_.committed == s.committed
    &&& s_.committed_val == s.committed_val
    &&& s_.witness_val == s.witness_val
    &&& s_.has_witness == s.has_witness
    &&& s_.msgs_prepare == s.msgs_prepare
    &&& s_.msgs_prepare_bal == s.msgs_prepare_bal
    &&& s_.msgs_promise == s.msgs_promise
    &&& s_.msgs_promise_bal == s.msgs_promise_bal
    &&& s_.msgs_promise_v_bal == s.msgs_promise_v_bal
    &&& s_.msgs_promise_val == s.msgs_promise_val
}

/// Receive an accepted message and track the accepting node.
pub open spec fn LReceiveAccepted(s: LState, s_: LState, c: LConstants, sender: int) -> bool {
    &&& s.is_active == true
    &&& s.msgs_accept == true
    &&& s.msgs_accept_bal == s.max_bal
    &&& !s.accepts_rcvd.contains(sender)
    // Add sender to accepts received
    &&& s_.accepts_rcvd == s.accepts_rcvd.insert(sender)
    // Frame
    &&& s_.max_bal == s.max_bal
    &&& s_.max_v_bal == s.max_v_bal
    &&& s_.max_val == s.max_val
    &&& s_.has_voted == s.has_voted
    &&& s_.config_num == s.config_num
    &&& s_.is_active == s.is_active
    &&& s_.promises_rcvd == s.promises_rcvd
    &&& s_.committed == s.committed
    &&& s_.committed_val == s.committed_val
    &&& s_.witness_val == s.witness_val
    &&& s_.has_witness == s.has_witness
    &&& s_.msgs_prepare == s.msgs_prepare
    &&& s_.msgs_prepare_bal == s.msgs_prepare_bal
    &&& s_.msgs_promise == s.msgs_promise
    &&& s_.msgs_promise_bal == s.msgs_promise_bal
    &&& s_.msgs_promise_v_bal == s.msgs_promise_v_bal
    &&& s_.msgs_promise_val == s.msgs_promise_val
    &&& s_.msgs_accept == s.msgs_accept
    &&& s_.msgs_accept_bal == s.msgs_accept_bal
    &&& s_.msgs_accept_val == s.msgs_accept_val
}

/// Commit: value is committed when accepted by a quorum.
/// Uses accepts_rcvd.len() for quorum check.
pub open spec fn LCommit(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.is_active == true
    &&& s.committed == false
    &&& s.accepts_rcvd.len() >= c.quorum_size
    // Mark as committed
    &&& s_.committed == true
    &&& s_.committed_val == s.max_val
    // Frame
    &&& s_.max_bal == s.max_bal
    &&& s_.max_v_bal == s.max_v_bal
    &&& s_.max_val == s.max_val
    &&& s_.has_voted == s.has_voted
    &&& s_.config_num == s.config_num
    &&& s_.is_active == s.is_active
    &&& s_.promises_rcvd == s.promises_rcvd
    &&& s_.accepts_rcvd == s.accepts_rcvd
    &&& s_.witness_val == s.witness_val
    &&& s_.has_witness == s.has_witness
    &&& s_.msgs_prepare == s.msgs_prepare
    &&& s_.msgs_prepare_bal == s.msgs_prepare_bal
    &&& s_.msgs_promise == s.msgs_promise
    &&& s_.msgs_promise_bal == s.msgs_promise_bal
    &&& s_.msgs_promise_v_bal == s.msgs_promise_v_bal
    &&& s_.msgs_promise_val == s.msgs_promise_val
    &&& s_.msgs_accept == s.msgs_accept
    &&& s_.msgs_accept_bal == s.msgs_accept_bal
    &&& s_.msgs_accept_val == s.msgs_accept_val
}

/// Reconfigure: Move to a new configuration.
/// Increments the config number and resets ballot tracking.
pub open spec fn LReconfigure(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.is_active == true
    &&& s_.config_num == s.config_num + 1
    &&& s_.max_bal == 0
    &&& s_.max_v_bal == 0
    &&& s_.max_val == s.max_val
    &&& s_.has_voted == false
    &&& s_.is_active == true
    // Reset quorum tracking
    &&& s_.promises_rcvd == Set::<int>::empty()
    &&& s_.accepts_rcvd == Set::<int>::empty()
    // Clear messages
    &&& s_.msgs_prepare == false
    &&& s_.msgs_prepare_bal == 0
    &&& s_.msgs_promise == false
    &&& s_.msgs_promise_bal == 0
    &&& s_.msgs_promise_v_bal == 0
    &&& s_.msgs_promise_val == 0
    &&& s_.msgs_accept == false
    &&& s_.msgs_accept_bal == 0
    &&& s_.msgs_accept_val == 0
    // Frame
    &&& s_.committed == s.committed
    &&& s_.committed_val == s.committed_val
    &&& s_.witness_val == s.witness_val
    &&& s_.has_witness == s.has_witness
}

/// WitnessSync: Witness transfers accepted state from old config to new.
pub open spec fn LWitnessSync(s: LState, s_: LState, c: LConstants, witness_val: int) -> bool {
    &&& s.is_active == true
    // Receive witness value
    &&& s_.has_witness == true
    &&& s_.witness_val == witness_val
    // If no local vote, adopt the witness value
    &&& s_.max_val == (if !s.has_voted { witness_val } else { s.max_val })
    // Frame
    &&& s_.max_bal == s.max_bal
    &&& s_.max_v_bal == s.max_v_bal
    &&& s_.has_voted == s.has_voted
    &&& s_.config_num == s.config_num
    &&& s_.is_active == s.is_active
    &&& s_.promises_rcvd == s.promises_rcvd
    &&& s_.accepts_rcvd == s.accepts_rcvd
    &&& s_.committed == s.committed
    &&& s_.committed_val == s.committed_val
    &&& s_.msgs_prepare == s.msgs_prepare
    &&& s_.msgs_prepare_bal == s.msgs_prepare_bal
    &&& s_.msgs_promise == s.msgs_promise
    &&& s_.msgs_promise_bal == s.msgs_promise_bal
    &&& s_.msgs_promise_v_bal == s.msgs_promise_v_bal
    &&& s_.msgs_promise_val == s.msgs_promise_val
    &&& s_.msgs_accept == s.msgs_accept
    &&& s_.msgs_accept_bal == s.msgs_accept_bal
    &&& s_.msgs_accept_val == s.msgs_accept_val
}

/// Sync: Transfer accepted state to a new configuration member.
pub open spec fn LSync(s: LState, s_: LState, c: LConstants, new_config: int, val: int) -> bool {
    &&& s.is_active == false
    &&& new_config > s.config_num
    &&& s_.config_num == new_config
    &&& s_.max_bal == 0
    &&& s_.max_v_bal == 0
    &&& s_.max_val == val
    &&& s_.has_voted == false
    &&& s_.is_active == true
    // Reset quorum tracking
    &&& s_.promises_rcvd == Set::<int>::empty()
    &&& s_.accepts_rcvd == Set::<int>::empty()
    &&& s_.committed == false
    &&& s_.committed_val == 0
    &&& s_.witness_val == 0
    &&& s_.has_witness == false
    // Clear messages
    &&& s_.msgs_prepare == false
    &&& s_.msgs_prepare_bal == 0
    &&& s_.msgs_promise == false
    &&& s_.msgs_promise_bal == 0
    &&& s_.msgs_promise_v_bal == 0
    &&& s_.msgs_promise_val == 0
    &&& s_.msgs_accept == false
    &&& s_.msgs_accept_bal == 0
    &&& s_.msgs_accept_val == 0
}

/// Deactivate: Node leaves the active set for reconfiguration.
pub open spec fn LDeactivate(s: LState, s_: LState, c: LConstants) -> bool {
    &&& s.is_active == true
    &&& s_.is_active == false
    // Frame
    &&& s_.config_num == s.config_num
    &&& s_.max_bal == s.max_bal
    &&& s_.max_v_bal == s.max_v_bal
    &&& s_.max_val == s.max_val
    &&& s_.has_voted == s.has_voted
    &&& s_.promises_rcvd == s.promises_rcvd
    &&& s_.accepts_rcvd == s.accepts_rcvd
    &&& s_.committed == s.committed
    &&& s_.committed_val == s.committed_val
    &&& s_.witness_val == s.witness_val
    &&& s_.has_witness == s.has_witness
    &&& s_.msgs_prepare == s.msgs_prepare
    &&& s_.msgs_prepare_bal == s.msgs_prepare_bal
    &&& s_.msgs_promise == s.msgs_promise
    &&& s_.msgs_promise_bal == s.msgs_promise_bal
    &&& s_.msgs_promise_v_bal == s.msgs_promise_v_bal
    &&& s_.msgs_promise_val == s.msgs_promise_val
    &&& s_.msgs_accept == s.msgs_accept
    &&& s_.msgs_accept_bal == s.msgs_accept_bal
    &&& s_.msgs_accept_val == s.msgs_accept_val
}

/// Next-state relation: disjunction of all transitions.
pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
    ||| exists |b: int| LPrepare(s, s_, c, b)
    ||| LSendPromise(s, s_, c)
    ||| exists |sender: int| LReceivePromise(s, s_, c, sender)
    ||| exists |b: int, v: int| LAccept(s, s_, c, b, v)
    ||| exists |sender: int| LReceiveAccepted(s, s_, c, sender)
    ||| LCommit(s, s_, c)
    ||| LReconfigure(s, s_, c)
    ||| exists |witness_val: int| LWitnessSync(s, s_, c, witness_val)
    ||| exists |new_config: int, val: int| LSync(s, s_, c, new_config, val)
    ||| LDeactivate(s, s_, c)
}

} // verus!
