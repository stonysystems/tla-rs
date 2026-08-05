//! Expected translator output for `clean.tla` (module `TwoPhaseClean`).
//!
//! This is the **golden**: the single-process Verus spec the Phase 52
//! translator must emit. Frozen after human review and byte-compared by V3.
//!
//! Reading it beside `clean.tla`:
//!
//! - `tm_state` and `tm_prepared` are ordinary per-node fields. 2PC has two
//!   roles, and the rewrite made the coordinator a *designated node* rather
//!   than global state; every node carries the fields and only `c.tm` acts on
//!   them, which is why `LTMCommit` opens with `c.node_id == c.tm`.
//! - `LTMCommit` compares `s.tm_prepared` against the whole node set rather
//!   than counting. 2PC needs unanimity, not a majority, so P4's counting rule
//!   does not apply here — the contrast with Paxos's `LIsMajority` is the point.
//! - `LRMRcvCommitMsg` takes no parameters beyond the state: a `Commit`
//!   message carries no payload and the handler does not use the sender.
//!
//! No counterpart is emitted for `Consistent` or `TypeOK`: both quantify over
//! all nodes, and a global property does not project onto one.

use vstd::prelude::*;

verus! {
    pub enum LRmState {
        Working,
        Prepared,
        Committed,
        Aborted,
    }

    pub enum LTmState {
        Init,
        Committed,
        Aborted,
    }

    /// Wire messages. Routing lives on the packet, not in the payload.
    pub enum LMessage {
        Prepared,
        Commit,
        Abort,
    }

    /// A message addressed to a peer.
    pub struct LPacket {
        pub dst: int,
        pub msg: LMessage,
    }

    /// This node's state.
    pub struct LState {
        pub rm_state: LRmState,
        pub tm_state: LTmState,
        pub tm_prepared: Set<int>,
    }

    /// Protocol constants, including this node's own identity.
    pub struct LConstants {
        pub r_m: Set<int>,
        pub t_m: int,
        pub node_id: int,
    }

    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        &&& s.rm_state is Working
        &&& s.tm_state is Init
        &&& s.tm_prepared == Set::<int>::empty()
    }

    pub open spec fn LTMRcvPrepared(
        s: LState,
        s_: LState,
        c: LConstants,
        src: int,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& c.node_id == c.t_m
        &&& s.tm_state is Init
        &&& s_.tm_prepared == s.tm_prepared.union(set![src])
        &&& sent_packets == Set::<LPacket>::empty()
        &&& s_.rm_state == s.rm_state
        &&& s_.tm_state == s.tm_state
    }

    pub open spec fn LTMCommit(
        s: LState,
        s_: LState,
        c: LConstants,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& c.node_id == c.t_m
        &&& s.tm_state is Init
        &&& s.tm_prepared == c.r_m
        &&& s_.tm_state is Committed
        &&& sent_packets == c.r_m.map(|d: int| LPacket { dst: d, msg: LMessage::Commit })
        &&& s_.rm_state == s.rm_state
        &&& s_.tm_prepared == s.tm_prepared
    }

    pub open spec fn LTMAbort(
        s: LState,
        s_: LState,
        c: LConstants,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& c.node_id == c.t_m
        &&& s.tm_state is Init
        &&& s_.tm_state is Aborted
        &&& sent_packets == c.r_m.map(|d: int| LPacket { dst: d, msg: LMessage::Abort })
        &&& s_.rm_state == s.rm_state
        &&& s_.tm_prepared == s.tm_prepared
    }

    pub open spec fn LRMPrepare(
        s: LState,
        s_: LState,
        c: LConstants,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& s.rm_state is Working
        &&& s_.rm_state is Prepared
        &&& sent_packets == set![LPacket { dst: c.t_m, msg: LMessage::Prepared }]
        &&& s_.tm_state == s.tm_state
        &&& s_.tm_prepared == s.tm_prepared
    }

    pub open spec fn LRMChooseToAbort(
        s: LState,
        s_: LState,
        c: LConstants,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& s.rm_state is Working
        &&& s_.rm_state is Aborted
        &&& sent_packets == Set::<LPacket>::empty()
        &&& s_.tm_state == s.tm_state
        &&& s_.tm_prepared == s.tm_prepared
    }

    pub open spec fn LRMRcvCommitMsg(
        s: LState,
        s_: LState,
        c: LConstants,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& s_.rm_state is Committed
        &&& sent_packets == Set::<LPacket>::empty()
        &&& s_.tm_state == s.tm_state
        &&& s_.tm_prepared == s.tm_prepared
    }

    pub open spec fn LRMRcvAbortMsg(
        s: LState,
        s_: LState,
        c: LConstants,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& s_.rm_state is Aborted
        &&& sent_packets == Set::<LPacket>::empty()
        &&& s_.tm_state == s.tm_state
        &&& s_.tm_prepared == s.tm_prepared
    }

    /// Dispatch on the received message. Delivery and the tag are the
    /// framework's; each handler states only its own conditions.
    pub open spec fn LHandleMessage(
        s: LState,
        s_: LState,
        c: LConstants,
        src: int,
        msg: LMessage,
        sent_packets: Set<LPacket>,
    ) -> bool {
        match msg {
            LMessage::Prepared =>
                LTMRcvPrepared(s, s_, c, src, sent_packets),
            LMessage::Commit =>
                LRMRcvCommitMsg(s, s_, c, sent_packets),
            LMessage::Abort =>
                LRMRcvAbortMsg(s, s_, c, sent_packets),
        }
    }

    pub open spec fn LNext(
        s: LState,
        s_: LState,
        c: LConstants,
        sent_packets: Set<LPacket>,
    ) -> bool {
        ||| LTMCommit(s, s_, c, sent_packets)
        ||| LTMAbort(s, s_, c, sent_packets)
        ||| LRMPrepare(s, s_, c, sent_packets)
        ||| LRMChooseToAbort(s, s_, c, sent_packets)
        ||| (exists|src: int, msg: LMessage|
                LHandleMessage(s, s_, c, src, msg, sent_packets))
    }
}
