use crate::protocol::ChainReplication::types::*;
use vstd::prelude::*;

verus! {
    /// Initialize chain replication node state
    /// Node starts with empty history, no pending updates, no committed ops
    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        &&& s.history == Seq::<int>::empty()
        &&& s.pending_sent == Set::<int>::empty()
        &&& s.committed_count == 0int
        &&& s.obj_value == 0int
        &&& (c.node_id == 0 ==> s.role is Head)
        &&& (c.node_id == c.chain_len - 1 ==> s.role is Tail)
        &&& (c.node_id > 0 && c.node_id < c.chain_len - 1 ==> s.role is Middle)
        &&& s.has_predecessor == (c.node_id > 0)
        &&& s.predecessor == (if c.node_id > 0 { c.node_id - 1 } else { 0int })
        &&& s.has_successor == (c.node_id < c.chain_len - 1)
        &&& s.successor == (if c.node_id < c.chain_len - 1 { c.node_id + 1 } else { 0int })
        &&& s.alive == true
    }

    /// Head receives a client write request and applies it locally
    /// The value is appended to the head's history and marked as pending
    pub open spec fn LHeadReceiveWrite(
        s: LState, s_: LState, c: LConstants, value: int,
        sent_packets: Seq<LCRMessage>,
    ) -> bool {
        &&& s.role is Head
        &&& s.alive == true
        &&& !s.pending_sent.contains(value)
        &&& s_.role == s.role
        &&& s_.history == s.history.push(value)
        &&& s_.pending_sent == s.pending_sent.insert(value)
        &&& s_.committed_count == s.committed_count
        &&& s_.obj_value == s.obj_value
        // Frame
        &&& s_.has_predecessor == s.has_predecessor
        &&& s_.predecessor == s.predecessor
        &&& s_.has_successor == s.has_successor
        &&& s_.successor == s.successor
        &&& s_.alive == s.alive
        // No messages sent
        &&& sent_packets == Seq::<LCRMessage>::empty()
    }

    /// Head or middle node forwards a pending value to its successor
    /// Sends a Forward message
    pub open spec fn LForwardToSuccessor(
        s: LState, s_: LState, c: LConstants, value: int,
        sent_packets: Seq<LCRMessage>,
    ) -> bool {
        &&& (s.role is Head || s.role is Middle)
        &&& s.alive == true
        &&& s.pending_sent.contains(value)
        &&& s.has_successor == true
        // Frame
        &&& s_.role == s.role
        &&& s_.history == s.history
        &&& s_.pending_sent == s.pending_sent
        &&& s_.committed_count == s.committed_count
        &&& s_.obj_value == s.obj_value
        &&& s_.has_predecessor == s.has_predecessor
        &&& s_.predecessor == s.predecessor
        &&& s_.has_successor == s.has_successor
        &&& s_.successor == s.successor
        &&& s_.alive == s.alive
        // Send forward message
        &&& sent_packets == seq![LCRMessage::Forward { value }]
    }

    /// A middle or tail node receives an update from its predecessor
    /// The value is appended to this node's history
    pub open spec fn LReceiveUpdate(
        s: LState, s_: LState, c: LConstants, value: int,
        sent_packets: Seq<LCRMessage>,
    ) -> bool {
        &&& (s.role is Middle || s.role is Tail)
        &&& s.alive == true
        &&& !s.history.contains(value)
        &&& s_.role == s.role
        &&& s_.history == s.history.push(value)
        // Middle nodes add to pending_sent; tail does not
        &&& if s.role is Middle {
            s_.pending_sent == s.pending_sent.insert(value)
        } else {
            s_.pending_sent == s.pending_sent
        }
        &&& s_.committed_count == s.committed_count
        &&& s_.obj_value == s.obj_value
        // Frame
        &&& s_.has_predecessor == s.has_predecessor
        &&& s_.predecessor == s.predecessor
        &&& s_.has_successor == s.has_successor
        &&& s_.successor == s.successor
        &&& s_.alive == s.alive
        // No messages sent
        &&& sent_packets == Seq::<LCRMessage>::empty()
    }

    /// The tail commits a value: updates committed count and object value
    pub open spec fn LTailCommit(
        s: LState, s_: LState, c: LConstants, value: int,
        sent_packets: Seq<LCRMessage>,
    ) -> bool {
        &&& s.role is Tail
        &&& s.alive == true
        &&& s.history.contains(value)
        &&& s_.role == s.role
        &&& s_.history == s.history
        &&& s_.pending_sent == s.pending_sent
        &&& s_.committed_count == s.committed_count + 1
        &&& s_.obj_value == value
        // Frame
        &&& s_.has_predecessor == s.has_predecessor
        &&& s_.predecessor == s.predecessor
        &&& s_.has_successor == s.has_successor
        &&& s_.successor == s.successor
        &&& s_.alive == s.alive
        // Send ack back up the chain
        &&& sent_packets == seq![LCRMessage::Ack { value }]
    }

    /// A node receives an acknowledgment from its successor
    /// Removes the value from the pending_sent set
    pub open spec fn LReceiveAck(
        s: LState, s_: LState, c: LConstants, value: int,
        sent_packets: Seq<LCRMessage>,
    ) -> bool {
        &&& (s.role is Head || s.role is Middle)
        &&& s.alive == true
        &&& s.pending_sent.contains(value)
        &&& s_.role == s.role
        &&& s_.history == s.history
        &&& s_.pending_sent == s.pending_sent.remove(value)
        &&& s_.committed_count == s.committed_count
        &&& s_.obj_value == s.obj_value
        // Frame
        &&& s_.has_predecessor == s.has_predecessor
        &&& s_.predecessor == s.predecessor
        &&& s_.has_successor == s.has_successor
        &&& s_.successor == s.successor
        &&& s_.alive == s.alive
        // No messages sent
        &&& sent_packets == Seq::<LCRMessage>::empty()
    }

    /// Client reads the current committed value (tail only, no state change)
    pub open spec fn LClientRead(
        s: LState, s_: LState, c: LConstants,
        sent_packets: Seq<LCRMessage>,
    ) -> bool {
        &&& s.role is Tail
        &&& s.alive == true
        &&& s_.role == s.role
        &&& s_.history == s.history
        &&& s_.pending_sent == s.pending_sent
        &&& s_.committed_count == s.committed_count
        &&& s_.obj_value == s.obj_value
        &&& s_.has_predecessor == s.has_predecessor
        &&& s_.predecessor == s.predecessor
        &&& s_.has_successor == s.has_successor
        &&& s_.successor == s.successor
        &&& s_.alive == s.alive
        // No messages sent
        &&& sent_packets == Seq::<LCRMessage>::empty()
    }

    /// A node fails (crashes)
    pub open spec fn LNodeFail(
        s: LState, s_: LState, c: LConstants,
        sent_packets: Seq<LCRMessage>,
    ) -> bool {
        &&& s.alive == true
        // Node becomes dead
        &&& s_.alive == false
        // Frame: state preserved but node inactive
        &&& s_.role == s.role
        &&& s_.history == s.history
        &&& s_.pending_sent == s.pending_sent
        &&& s_.committed_count == s.committed_count
        &&& s_.obj_value == s.obj_value
        &&& s_.has_predecessor == s.has_predecessor
        &&& s_.predecessor == s.predecessor
        &&& s_.has_successor == s.has_successor
        &&& s_.successor == s.successor
        // No messages sent
        &&& sent_packets == Seq::<LCRMessage>::empty()
    }

    /// Reconfigure the chain after a node failure
    /// Adjusts predecessor/successor links to skip the failed node
    pub open spec fn LReconfigure(
        s: LState, s_: LState, c: LConstants,
        new_has_predecessor: bool, new_predecessor: int,
        new_has_successor: bool, new_successor: int,
        sent_packets: Seq<LCRMessage>,
    ) -> bool {
        &&& s.alive == true
        // Update chain links
        &&& s_.has_predecessor == new_has_predecessor
        &&& s_.predecessor == new_predecessor
        &&& s_.has_successor == new_has_successor
        &&& s_.successor == new_successor
        // Role stays the same during reconfiguration
        &&& s_.role == s.role
        // Frame
        &&& s_.history == s.history
        &&& s_.pending_sent == s.pending_sent
        &&& s_.committed_count == s.committed_count
        &&& s_.obj_value == s.obj_value
        &&& s_.alive == s.alive
        // No messages sent
        &&& sent_packets == Seq::<LCRMessage>::empty()
    }

    /// Next-state relation: disjunction of all possible transitions
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        ||| exists |value: int, sent_packets: Seq<LCRMessage>| LHeadReceiveWrite(s, s_, c, value, sent_packets)
        ||| exists |value: int, sent_packets: Seq<LCRMessage>| LForwardToSuccessor(s, s_, c, value, sent_packets)
        ||| exists |value: int, sent_packets: Seq<LCRMessage>| LReceiveUpdate(s, s_, c, value, sent_packets)
        ||| exists |value: int, sent_packets: Seq<LCRMessage>| LTailCommit(s, s_, c, value, sent_packets)
        ||| exists |value: int, sent_packets: Seq<LCRMessage>| LReceiveAck(s, s_, c, value, sent_packets)
        ||| exists |sent_packets: Seq<LCRMessage>| LClientRead(s, s_, c, sent_packets)
        ||| exists |sent_packets: Seq<LCRMessage>| LNodeFail(s, s_, c, sent_packets)
        ||| exists |new_has_predecessor: bool, new_predecessor: int, new_has_successor: bool, new_successor: int, sent_packets: Seq<LCRMessage>| LReconfigure(s, s_, c, new_has_predecessor, new_predecessor, new_has_successor, new_successor, sent_packets)
    }
}
