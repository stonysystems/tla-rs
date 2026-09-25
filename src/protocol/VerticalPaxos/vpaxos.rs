use crate::protocol::VerticalPaxos::types::*;
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

verus! {

/// Initial state: config 0, no ballots seen, not voted, active
// @automan predicate(s: out, c: in)
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
    &&& c.quorum_size >= 1
    &&& c.num_nodes >= c.quorum_size
}

/// Phase 1a: Proposer sends prepare with ballot b.
/// The node promises not to accept any ballot less than b.
// @automan predicate(s: in, s_: out, c: in, b: in, sent_packets: out)
pub open spec fn LPrepare(s: LState, s_: LState, c: LConstants, b: int, sent_packets: Seq<LVPMessage>) -> bool {
    &&& s.is_active == true
    &&& b > s.max_bal
    // Update max_bal
    &&& s_.max_bal == b
    // Send prepare message
    &&& sent_packets == seq![LVPMessage::Prepare { bal: b }]
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
}

/// Phase 1b: Acceptor receives prepare and sends promise.
// @automan predicate(s: in, s_: out, c: in, prepare_bal: in, sent_packets: out)
pub open spec fn LSendPromise(s: LState, s_: LState, c: LConstants, prepare_bal: int, sent_packets: Seq<LVPMessage>) -> bool {
    &&& s.is_active == true
    &&& prepare_bal > s.max_bal
    // Update max_bal
    &&& s_.max_bal == prepare_bal
    // Send promise with current accepted state
    &&& sent_packets == seq![LVPMessage::Promise { bal: prepare_bal, v_bal: s.max_v_bal, val: s.max_val }]
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
}

/// Proposer receives a promise and tracks it.
// @automan predicate(s: in, s_: out, c: in, sender: in, promise_bal: in, promise_v_bal: in, promise_val: in, sent_packets: out)
pub open spec fn LReceivePromise(s: LState, s_: LState, c: LConstants, sender: int, promise_bal: int, promise_v_bal: int, promise_val: int, sent_packets: Seq<LVPMessage>) -> bool {
    &&& s.is_active == true
    &&& promise_bal == s.max_bal
    &&& !s.promises_rcvd.contains(sender)
    // Add sender to promises received
    &&& s_.promises_rcvd == s.promises_rcvd.insert(sender)
    // Track highest accepted value from promises
    &&& s_.max_v_bal == (if promise_v_bal > s.max_v_bal { promise_v_bal } else { s.max_v_bal })
    &&& s_.max_val == (if promise_v_bal > s.max_v_bal { promise_val } else { s.max_val })
    // No messages sent
    &&& sent_packets == Seq::<LVPMessage>::empty()
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
}

/// Phase 2a/2b: Accept a value v at ballot b.
/// Only accepts if b equals the current max_bal (promised ballot).
// @automan predicate(s: in, s_: out, c: in, b: in, v: in, sent_packets: out)
pub open spec fn LAccept(s: LState, s_: LState, c: LConstants, b: int, v: int, sent_packets: Seq<LVPMessage>) -> bool {
    &&& s.is_active == true
    &&& b == s.max_bal
    &&& b > s.max_v_bal
    // Accept the value
    &&& s_.max_v_bal == b
    &&& s_.max_val == v
    &&& s_.has_voted == true
    // Send accept message
    &&& sent_packets == seq![LVPMessage::Accept { bal: b, val: v }]
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
}

/// Receive an accepted message and track the accepting node.
// @automan predicate(s: in, s_: out, c: in, sender: in, accept_bal: in, sent_packets: out)
pub open spec fn LReceiveAccepted(s: LState, s_: LState, c: LConstants, sender: int, accept_bal: int, sent_packets: Seq<LVPMessage>) -> bool {
    &&& s.is_active == true
    &&& accept_bal == s.max_bal
    &&& !s.accepts_rcvd.contains(sender)
    // Add sender to accepts received
    &&& s_.accepts_rcvd == s.accepts_rcvd.insert(sender)
    // No messages sent
    &&& sent_packets == Seq::<LVPMessage>::empty()
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
}

/// Commit: value is committed when accepted by a quorum.
/// Uses accepts_rcvd.len() for quorum check.
// @automan predicate(s: in, s_: out, c: in, sent_packets: out)
pub open spec fn LCommit(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LVPMessage>) -> bool {
    &&& s.is_active == true
    &&& s.committed == false
    &&& s.accepts_rcvd.len() >= c.quorum_size
    // Mark as committed
    &&& s_.committed == true
    &&& s_.committed_val == s.max_val
    // No messages sent
    &&& sent_packets == Seq::<LVPMessage>::empty()
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
}

/// Reconfigure: Move to a new configuration.
/// Increments the config number and resets ballot tracking.
// @automan predicate(s: in, s_: out, c: in, sent_packets: out)
pub open spec fn LReconfigure(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LVPMessage>) -> bool {
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
    // No messages sent
    &&& sent_packets == Seq::<LVPMessage>::empty()
    // Frame
    &&& s_.committed == s.committed
    &&& s_.committed_val == s.committed_val
    &&& s_.witness_val == s.witness_val
    &&& s_.has_witness == s.has_witness
}

/// WitnessSync: Witness transfers accepted state from old config to new.
// @automan predicate(s: in, s_: out, c: in, witness_val: in, sent_packets: out)
pub open spec fn LWitnessSync(s: LState, s_: LState, c: LConstants, witness_val: int, sent_packets: Seq<LVPMessage>) -> bool {
    &&& s.is_active == true
    // Receive witness value
    &&& s_.has_witness == true
    &&& s_.witness_val == witness_val
    // If no local vote, adopt the witness value
    &&& s_.max_val == (if !s.has_voted { witness_val } else { s.max_val })
    // No messages sent
    &&& sent_packets == Seq::<LVPMessage>::empty()
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
}

/// Sync: Transfer accepted state to a new configuration member.
// @automan predicate(s: in, s_: out, c: in, new_config: in, val: in, sent_packets: out)
pub open spec fn LSync(s: LState, s_: LState, c: LConstants, new_config: int, val: int, sent_packets: Seq<LVPMessage>) -> bool {
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
    // No messages sent
    &&& sent_packets == Seq::<LVPMessage>::empty()
}

/// Deactivate: Node leaves the active set for reconfiguration.
// @automan predicate(s: in, s_: out, c: in, sent_packets: out)
pub open spec fn LDeactivate(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LVPMessage>) -> bool {
    &&& s.is_active == true
    &&& s_.is_active == false
    // No messages sent
    &&& sent_packets == Seq::<LVPMessage>::empty()
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
}

/// Next-state relation: disjunction of all transitions.
pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
    ||| exists |b: int, sent_packets: Seq<LVPMessage>| LPrepare(s, s_, c, b, sent_packets)
    ||| exists |prepare_bal: int, sent_packets: Seq<LVPMessage>| LSendPromise(s, s_, c, prepare_bal, sent_packets)
    ||| exists |sender: int, promise_bal: int, promise_v_bal: int, promise_val: int, sent_packets: Seq<LVPMessage>| LReceivePromise(s, s_, c, sender, promise_bal, promise_v_bal, promise_val, sent_packets)
    ||| exists |b: int, v: int, sent_packets: Seq<LVPMessage>| LAccept(s, s_, c, b, v, sent_packets)
    ||| exists |sender: int, accept_bal: int, sent_packets: Seq<LVPMessage>| LReceiveAccepted(s, s_, c, sender, accept_bal, sent_packets)
    ||| exists |sent_packets: Seq<LVPMessage>| LCommit(s, s_, c, sent_packets)
    ||| exists |sent_packets: Seq<LVPMessage>| LReconfigure(s, s_, c, sent_packets)
    ||| exists |witness_val: int, sent_packets: Seq<LVPMessage>| LWitnessSync(s, s_, c, witness_val, sent_packets)
    ||| exists |new_config: int, val: int, sent_packets: Seq<LVPMessage>| LSync(s, s_, c, new_config, val, sent_packets)
    ||| exists |sent_packets: Seq<LVPMessage>| LDeactivate(s, s_, c, sent_packets)
}

} // verus!
