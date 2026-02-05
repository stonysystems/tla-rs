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
    }

    /// Head receives a client write request and applies it locally
    /// The value is appended to the head's history and marked as pending
    /// (forwarded to successor but not yet acked)
    pub open spec fn LHeadReceiveWrite(
        s: LState, s_: LState, c: LConstants, value: int,
    ) -> bool {
        &&& s.role is Head
        &&& !s.pending_sent.contains(value)
        &&& s_.role == s.role
        &&& s_.history == s.history.push(value)
        &&& s_.pending_sent == s.pending_sent.insert(value)
        &&& s_.committed_count == s.committed_count
        &&& s_.obj_value == s.obj_value
    }

    /// A middle or tail node receives an update from its predecessor
    /// The value is appended to this node's history.
    /// Middle nodes also add it to pending_sent (forward to successor).
    pub open spec fn LReceiveUpdate(
        s: LState, s_: LState, c: LConstants, value: int,
    ) -> bool {
        &&& (s.role is Middle || s.role is Tail)
        &&& !s.history.contains(value)
        &&& s_.role == s.role
        &&& s_.history == s.history.push(value)
        &&& if s.role is Middle {
            s_.pending_sent == s.pending_sent.insert(value)
        } else {
            s_.pending_sent == s.pending_sent
        }
        &&& s_.committed_count == s.committed_count
        &&& s_.obj_value == s.obj_value
    }

    /// The tail commits a value: updates committed count and object value
    /// This represents the value being fully replicated through the chain
    pub open spec fn LTailCommit(
        s: LState, s_: LState, c: LConstants, value: int,
    ) -> bool {
        &&& s.role is Tail
        &&& s.history.contains(value)
        &&& s_.role == s.role
        &&& s_.history == s.history
        &&& s_.pending_sent == s.pending_sent
        &&& s_.committed_count == s.committed_count + 1
        &&& s_.obj_value == value
    }

    /// A node receives an acknowledgment from its successor
    /// Removes the value from the pending_sent set
    pub open spec fn LReceiveAck(
        s: LState, s_: LState, c: LConstants, value: int,
    ) -> bool {
        &&& (s.role is Head || s.role is Middle)
        &&& s.pending_sent.contains(value)
        &&& s_.role == s.role
        &&& s_.history == s.history
        &&& s_.pending_sent == s.pending_sent.remove(value)
        &&& s_.committed_count == s.committed_count
        &&& s_.obj_value == s.obj_value
    }

    /// Client reads the current committed value (tail only, no state change)
    /// Models a read returning the current object state
    pub open spec fn LClientRead(
        s: LState, s_: LState, c: LConstants,
    ) -> bool {
        &&& s.role is Tail
        &&& s_ == s
    }

    /// Next-state relation: disjunction of all possible transitions
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        ||| exists |value: int| LHeadReceiveWrite(s, s_, c, value)
        ||| exists |value: int| LReceiveUpdate(s, s_, c, value)
        ||| exists |value: int| LTailCommit(s, s_, c, value)
        ||| exists |value: int| LReceiveAck(s, s_, c, value)
        ||| LClientRead(s, s_, c)
    }
}
