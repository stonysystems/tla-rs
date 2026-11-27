use crate::protocol::CRAQ::types::*;
use vstd::prelude::*;

verus! {
    /// Initialize CRAQ node state.
    /// Node starts with empty version history, no dirty versions, and clean_version = 0.
    // @automan predicate(s: out, c: in)
    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        &&& s.history == Seq::<int>::empty()
        &&& s.pending_sent == Set::<int>::empty()
        &&& s.clean_version == 0int
        &&& s.latest_version == 0int
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

    /// Head receives a client write request and creates a new dirty version locally.
    // @automan predicate(s: in, s_: out, c: in, value: in, sent_packets: out)
    pub open spec fn LHeadReceiveWrite(
        s: LState, s_: LState, c: LConstants, value: int,
        sent_packets: Seq<LCraqMessage>,
    ) -> bool {
        let new_version = s.latest_version + 1;
        &&& s.role is Head
        &&& s.alive == true
        &&& !s.pending_sent.contains(new_version)
        &&& s_.role == s.role
        &&& s_.history == s.history.push(value)
        &&& s_.pending_sent == s.pending_sent.insert(new_version)
        &&& s_.clean_version == s.clean_version
        &&& s_.latest_version == new_version
        &&& s_.obj_value == s.obj_value
        // Frame
        &&& s_.has_predecessor == s.has_predecessor
        &&& s_.predecessor == s.predecessor
        &&& s_.has_successor == s.has_successor
        &&& s_.successor == s.successor
        &&& s_.alive == s.alive
        // No messages sent yet
        &&& sent_packets == Seq::<LCraqMessage>::empty()
    }

    /// Head or middle node forwards a dirty version to its successor.
    // @automan predicate(s: in, s_: out, c: in, version: in, sent_packets: out)
    pub open spec fn LForwardToSuccessor(
        s: LState, s_: LState, c: LConstants, version: int,
        sent_packets: Seq<LCraqMessage>,
    ) -> bool {
        &&& (s.role is Head || s.role is Middle)
        &&& s.alive == true
        &&& 1 <= version <= s.latest_version
        &&& s.history.len() == s.latest_version
        &&& s.pending_sent.contains(version)
        &&& s.has_successor == true
        // Frame
        &&& s_.role == s.role
        &&& s_.history == s.history
        &&& s_.pending_sent == s.pending_sent
        &&& s_.clean_version == s.clean_version
        &&& s_.latest_version == s.latest_version
        &&& s_.obj_value == s.obj_value
        &&& s_.has_predecessor == s.has_predecessor
        &&& s_.predecessor == s.predecessor
        &&& s_.has_successor == s.has_successor
        &&& s_.successor == s.successor
        &&& s_.alive == s.alive
        // Send forward message with version and value
        &&& sent_packets == seq![LCraqMessage::Forward { version, value: s.history[version - 1] }]
    }

    /// A middle or tail node receives a new version from its predecessor.
    /// Middle nodes mark the new version as dirty; tail stores it for commit.
    // @automan predicate(s: in, s_: out, c: in, version: in, value: in, sent_packets: out)
    pub open spec fn LReceiveUpdate(
        s: LState, s_: LState, c: LConstants, version: int, value: int,
        sent_packets: Seq<LCraqMessage>,
    ) -> bool {
        &&& (s.role is Middle || s.role is Tail)
        &&& s.alive == true
        &&& version == s.latest_version + 1
        &&& s_.role == s.role
        &&& s_.history == s.history.push(value)
        &&& s_.latest_version == version
        &&& if s.role is Middle {
            s_.pending_sent == s.pending_sent.insert(version)
        } else {
            s_.pending_sent == s.pending_sent
        }
        &&& s_.clean_version == s.clean_version
        &&& s_.obj_value == s.obj_value
        // Frame
        &&& s_.has_predecessor == s.has_predecessor
        &&& s_.predecessor == s.predecessor
        &&& s_.has_successor == s.has_successor
        &&& s_.successor == s.successor
        &&& s_.alive == s.alive
        // No messages sent
        &&& sent_packets == Seq::<LCraqMessage>::empty()
    }

    /// The tail commits a version: marks it clean, updates obj_value, and sends Ack up the chain.
    // @automan predicate(s: in, s_: out, c: in, version: in, sent_packets: out)
    pub open spec fn LTailCommit(
        s: LState, s_: LState, c: LConstants, version: int,
        sent_packets: Seq<LCraqMessage>,
    ) -> bool {
        &&& s.role is Tail
        &&& s.alive == true
        &&& version == s.clean_version + 1
        &&& version <= s.latest_version
        &&& s.history.len() == s.latest_version
        &&& s_.role == s.role
        &&& s_.history == s.history
        &&& s_.pending_sent == s.pending_sent
        &&& s_.clean_version == version
        &&& s_.latest_version == s.latest_version
        &&& s_.obj_value == s.history[version - 1]
        // Frame
        &&& s_.has_predecessor == s.has_predecessor
        &&& s_.predecessor == s.predecessor
        &&& s_.has_successor == s.has_successor
        &&& s_.successor == s.successor
        &&& s_.alive == s.alive
        // Send ack back up the chain if there is a predecessor
        &&& if s.has_predecessor {
            sent_packets == seq![LCraqMessage::Ack { version, value: s.history[version - 1] }]
        } else {
            sent_packets == Seq::<LCraqMessage>::empty()
        }
    }

    /// Head or middle receives an acknowledgment from its successor:
    /// marks the version clean, removes it from dirty/pending_sent, and forwards Ack to predecessor.
    // @automan predicate(s: in, s_: out, c: in, version: in, value: in, sent_packets: out)
    pub open spec fn LReceiveAck(
        s: LState, s_: LState, c: LConstants, version: int, value: int,
        sent_packets: Seq<LCraqMessage>,
    ) -> bool {
        &&& (s.role is Head || s.role is Middle)
        &&& s.alive == true
        &&& 1 <= version <= s.latest_version
        &&& s.history.len() == s.latest_version
        &&& s.pending_sent.contains(version)
        &&& s_.role == s.role
        &&& s_.history == s.history
        &&& s_.pending_sent == s.pending_sent.remove(version)
        &&& s_.clean_version == (if version > s.clean_version { version } else { s.clean_version })
        &&& s_.latest_version == s.latest_version
        &&& s_.obj_value == (if version > s.clean_version { s.history[version - 1] } else { s.obj_value })
        // Frame
        &&& s_.has_predecessor == s.has_predecessor
        &&& s_.predecessor == s.predecessor
        &&& s_.has_successor == s.has_successor
        &&& s_.successor == s.successor
        &&& s_.alive == s.alive
        // Propagate Ack up the chain if this node has a predecessor
        &&& if s.has_predecessor {
            sent_packets == seq![LCraqMessage::Ack { version, value }]
        } else {
            sent_packets == Seq::<LCraqMessage>::empty()
        }
    }

    /// CRAQ clean read: ANY alive node (Head, Middle, or Tail) serves a read locally
    /// when its latest version is clean (no uncommitted/dirty writes pending).
    // @automan predicate(s: in, s_: out, c: in, read_value: out, sent_packets: out)
    pub open spec fn LClientReadClean(
        s: LState, s_: LState, c: LConstants, read_value: int,
        sent_packets: Seq<LCraqMessage>,
    ) -> bool {
        &&& s.alive == true
        &&& s.clean_version == s.latest_version
        &&& s.pending_sent == Set::<int>::empty()
        &&& read_value == s.obj_value
        // Frame (no state change)
        &&& s_ == s
        // Served locally: no messages sent
        &&& sent_packets == Seq::<LCraqMessage>::empty()
    }

    /// CRAQ dirty read: if a non-Tail node has dirty (unacknowledged) versions,
    /// it cannot serve the read locally and must send a lightweight VersionQuery to the Tail.
    // @automan predicate(s: in, s_: out, c: in, sent_packets: out)
    pub open spec fn LClientReadDirty(
        s: LState, s_: LState, c: LConstants,
        sent_packets: Seq<LCraqMessage>,
    ) -> bool {
        &&& (s.role is Head || s.role is Middle)
        &&& s.alive == true
        &&& s.clean_version < s.latest_version
        // Frame (no state change)
        &&& s_ == s
        // Send VersionQuery to the Tail
        &&& sent_packets == seq![LCraqMessage::VersionQuery { requester: c.node_id }]
    }

    /// Client read from any alive node: either served locally if clean,
    /// or triggers a VersionQuery to the Tail if dirty.
    pub open spec fn LClientRead(
        s: LState, s_: LState, c: LConstants,
        sent_packets: Seq<LCraqMessage>,
    ) -> bool {
        ||| exists|read_value: int| LClientReadClean(s, s_, c, read_value, sent_packets)
        ||| LClientReadDirty(s, s_, c, sent_packets)
    }

    /// Tail handles a VersionQuery from another node and replies with its latest committed version.
    // @automan predicate(s: in, s_: out, c: in, requester: in, sent_packets: out)
    pub open spec fn LTailHandleVersionQuery(
        s: LState, s_: LState, c: LConstants, requester: int,
        sent_packets: Seq<LCraqMessage>,
    ) -> bool {
        &&& s.role is Tail
        &&& s.alive == true
        // Frame (no state change)
        &&& s_ == s
        // Reply with tail's committed (clean) version
        &&& sent_packets == seq![LCraqMessage::VersionReply { requester, version: s.clean_version }]
    }

    /// A non-Tail node receives a VersionReply from the Tail and serves the read
    /// using the value at the committed version returned by the Tail.
    // @automan predicate(s: in, s_: out, c: in, version: in, read_value: out, sent_packets: out)
    pub open spec fn LReceiveVersionReply(
        s: LState, s_: LState, c: LConstants, version: int, read_value: int,
        sent_packets: Seq<LCraqMessage>,
    ) -> bool {
        &&& (s.role is Head || s.role is Middle)
        &&& s.alive == true
        &&& 0 <= version <= s.latest_version
        &&& s.history.len() == s.latest_version
        &&& read_value == (if version == 0 { 0int } else { s.history[version - 1] })
        // Frame (no state change)
        &&& s_ == s
        // No further messages sent
        &&& sent_packets == Seq::<LCraqMessage>::empty()
    }

    /// A node fails (crashes).
    // @automan predicate(s: in, s_: out, c: in, sent_packets: out)
    pub open spec fn LNodeFail(
        s: LState, s_: LState, c: LConstants,
        sent_packets: Seq<LCraqMessage>,
    ) -> bool {
        &&& s.alive == true
        &&& s_.alive == false
        // Frame: state preserved but node inactive
        &&& s_.role == s.role
        &&& s_.history == s.history
        &&& s_.pending_sent == s.pending_sent
        &&& s_.clean_version == s.clean_version
        &&& s_.latest_version == s.latest_version
        &&& s_.obj_value == s.obj_value
        &&& s_.has_predecessor == s.has_predecessor
        &&& s_.predecessor == s.predecessor
        &&& s_.has_successor == s.has_successor
        &&& s_.successor == s.successor
        &&& sent_packets == Seq::<LCraqMessage>::empty()
    }

    /// Reconfigure the chain after a node failure.
    /// Adjusts predecessor/successor links to skip the failed node.
    // @automan predicate(s: in, s_: out, c: in, new_has_predecessor: in, new_predecessor: in, new_has_successor: in, new_successor: in, sent_packets: out)
    pub open spec fn LReconfigure(
        s: LState, s_: LState, c: LConstants,
        new_has_predecessor: bool, new_predecessor: int,
        new_has_successor: bool, new_successor: int,
        sent_packets: Seq<LCraqMessage>,
    ) -> bool {
        &&& s.alive == true
        // Update chain links
        &&& s_.has_predecessor == new_has_predecessor
        &&& s_.predecessor == new_predecessor
        &&& s_.has_successor == new_has_successor
        &&& s_.successor == new_successor
        // Frame
        &&& s_.role == s.role
        &&& s_.history == s.history
        &&& s_.pending_sent == s.pending_sent
        &&& s_.clean_version == s.clean_version
        &&& s_.latest_version == s.latest_version
        &&& s_.obj_value == s.obj_value
        &&& s_.alive == s.alive
        &&& sent_packets == Seq::<LCraqMessage>::empty()
    }

    /// Next-state relation: disjunction of all possible CRAQ transitions.
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        ||| exists|value: int, sent_packets: Seq<LCraqMessage>| LHeadReceiveWrite(s, s_, c, value, sent_packets)
        ||| exists|version: int, sent_packets: Seq<LCraqMessage>| LForwardToSuccessor(s, s_, c, version, sent_packets)
        ||| exists|version: int, value: int, sent_packets: Seq<LCraqMessage>| LReceiveUpdate(s, s_, c, version, value, sent_packets)
        ||| exists|version: int, sent_packets: Seq<LCraqMessage>| LTailCommit(s, s_, c, version, sent_packets)
        ||| exists|version: int, value: int, sent_packets: Seq<LCraqMessage>| LReceiveAck(s, s_, c, version, sent_packets)
        ||| exists|sent_packets: Seq<LCraqMessage>| LClientRead(s, s_, c, sent_packets)
        ||| exists|requester: int, sent_packets: Seq<LCraqMessage>| LTailHandleVersionQuery(s, s_, c, requester, sent_packets)
        ||| exists|version: int, read_value: int, sent_packets: Seq<LCraqMessage>| LReceiveVersionReply(s, s_, c, version, read_value, sent_packets)
        ||| exists|sent_packets: Seq<LCraqMessage>| LNodeFail(s, s_, c, sent_packets)
        ||| exists|new_has_predecessor: bool, new_predecessor: int, new_has_successor: bool, new_successor: int, sent_packets: Seq<LCraqMessage>|
            LReconfigure(s, s_, c, new_has_predecessor, new_predecessor, new_has_successor, new_successor, sent_packets)
    }
}
