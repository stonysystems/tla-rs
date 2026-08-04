//! Expected translator output for `clean.tla` (module `LamportMutexClean`).
//!
//! This is the **golden**: the single-process Verus spec the Phase 52
//! translator must emit. Frozen after human review and byte-compared by V3.
//!
//! What the projection did:
//!
//! - **P1 state projection.** `clock`, `ack`, `crit` were `[Proc -> T]` and
//!   become this node's `int`, `Set<int>`, `bool`. `req`, `sendSeq` and
//!   `recvSeq` were `[Proc -> [Proc -> Nat]]`: the **outer** index is the node
//!   and is projected away, the **inner** index is the peer and survives as a
//!   `Map<int, int>`. Getting only the outer one is the whole point — this is
//!   the node's own table *about* its peers.
//! - **P2 de-index.** `req[p][q]` becomes `s.req[q]`, and `req[p][p]` becomes
//!   `s.req[c.node_id]`: the inner index can itself be the acting node, and
//!   then it is written as this node's identity rather than dropped.
//! - **P3 network.** `network` is gone. A send became `sent_packets`; a receive
//!   became a handler whose parameters are the message's fields, with the
//!   sender supplied by the framework from the packet.
//! - **P4 quorum.** `ack[p] = Proc` stays a comparison against the constant
//!   node set — this protocol needs unanimity, not a counted majority, so
//!   there is no counting rule to apply here.
//! - **P5 frame conditions.** Every action states what it leaves unchanged.
//!
//! Naming is uniform: a projected definition is `L` + the source's own name
//! (`beats` → `Lbeats`, `AdvanceAll` → `LAdvanceAll`), a constant keeps the
//! source's name (`Proc` → `c.proc`), and a receive's parameter is named after
//! the message field it carries. Helpers over node state survive as their own
//! functions rather than being inlined, which is what lets a reviewer match this
//! file against `clean.tla` concept by concept.
//!
//! `sent_packets` is a **`Set`**, not a `Seq`. The clean subset designates the
//! network as a set (C4), and a broadcast is written there as a set
//! comprehension over the peers; a sequence would require a delivery order that
//! the source spec does not give and a translator cannot invent. The executable
//! layer, which is out of Phase 52's scope, is where an ordered view belongs.
//!
//! No counterpart is emitted for `MutualExclusion` or `ClockConstraint`: both
//! quantify over all nodes, and a global property does not project onto one.

use vstd::prelude::*;

verus! {
    /// Wire messages. Sequence numbers carry the per-peer ordering that the
    /// original spec got from its FIFO channels; see the case's rewrite.md.
    pub enum LMessage {
        Req { clock: int, seq: int },
        Ack { seq: int },
        Rel { seq: int },
    }

    /// A message addressed to a peer.
    pub struct LPacket {
        pub dst: int,
        pub msg: LMessage,
    }

    /// This node's state.
    pub struct LState {
        /// Local logical clock.
        pub clock: int,
        /// Request clock received from each peer, 0 when none outstanding.
        /// The entry for this node itself holds its own outstanding request.
        pub req: Map<int, int>,
        /// Peers that have acknowledged this node's request.
        pub ack: Set<int>,
        /// Whether this node is in its critical section.
        pub crit: bool,
        /// Next sequence number this node will use toward each peer.
        pub send_seq: Map<int, int>,
        /// Next sequence number this node will accept from each peer.
        pub recv_seq: Map<int, int>,
    }

    /// Protocol constants, including this node's own identity.
    pub struct LConstants {
        pub proc: Set<int>,
        pub node_id: int,
    }

    /// `beats(p, q)` with `p` projected to this node.
    pub open spec fn Lbeats(s: LState, c: LConstants, q: int) -> bool {
        ||| s.req[q] == 0
        ||| s.req[c.node_id] < s.req[q]
        ||| (s.req[c.node_id] == s.req[q] && c.node_id < q)
    }

    /// Every peer's counter advances on a broadcast; this node's own does not.
    /// One peer's counter advances on a point-to-point send.
    pub open spec fn LAdvanceOne(s: LState, c: LConstants, d: int) -> Map<int, int> {
        s.send_seq.insert(d, s.send_seq[d] + 1)
    }

    pub open spec fn LAdvanceAll(s: LState, c: LConstants) -> Map<int, int> {
        Map::new(
            c.proc,
            |d: int| if d == c.node_id { s.send_seq[d] } else { s.send_seq[d] + 1 },
        )
    }

    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        &&& s.clock == 1
        &&& s.req == Map::new(c.proc, |q: int| 0int)
        &&& s.ack == Set::<int>::empty()
        &&& s.crit == false
        &&& s.send_seq == Map::new(c.proc, |q: int| 0int)
        &&& s.recv_seq == Map::new(c.proc, |q: int| 0int)
    }

    /// Request access to the critical section, broadcasting to every peer.
    pub open spec fn LRequest(
        s: LState,
        s_: LState,
        c: LConstants,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& s.req[c.node_id] == 0
        &&& s_.req == s.req.insert(c.node_id, s.clock)
        &&& sent_packets == c.proc.remove(c.node_id).map(
                |d: int| LPacket {
                    dst: d,
                    msg: LMessage::Req { clock: s.clock, seq: s.send_seq[d] },
                },
            )
        &&& s_.send_seq == LAdvanceAll(s, c)
        &&& s_.ack == set![c.node_id]
        &&& s_.clock == s.clock
        &&& s_.crit == s.crit
        &&& s_.recv_seq == s.recv_seq
    }

    /// Receive a request and acknowledge it.
    pub open spec fn LReceiveRequest(
        s: LState,
        s_: LState,
        c: LConstants,
        src: int,
        clock: int,
        seq: int,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& seq == s.recv_seq[src]
        &&& s_.req == s.req.insert(src, clock)
        &&& s_.clock == if clock > s.clock { clock + 1 } else { s.clock + 1 }
        &&& sent_packets == set![
                LPacket { dst: src, msg: LMessage::Ack { seq: s.send_seq[src] } },
            ]
        &&& s_.send_seq == LAdvanceOne(s, c, src)
        &&& s_.recv_seq == s.recv_seq.insert(src, s.recv_seq[src] + 1)
        &&& s_.ack == s.ack
        &&& s_.crit == s.crit
    }

    /// Receive an acknowledgement.
    pub open spec fn LReceiveAck(
        s: LState,
        s_: LState,
        c: LConstants,
        src: int,
        seq: int,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& seq == s.recv_seq[src]
        &&& s_.ack == s.ack.insert(src)
        &&& s_.recv_seq == s.recv_seq.insert(src, s.recv_seq[src] + 1)
        &&& sent_packets == Set::<LPacket>::empty()
        &&& s_.clock == s.clock
        &&& s_.req == s.req
        &&& s_.crit == s.crit
        &&& s_.send_seq == s.send_seq
    }

    /// Enter the critical section: everyone has acknowledged, and this node's
    /// request outranks every peer's.
    pub open spec fn LEnter(
        s: LState,
        s_: LState,
        c: LConstants,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& s.ack == c.proc
        &&& forall|q: int| c.proc.contains(q) && q != c.node_id ==> Lbeats(s, c, q)
        &&& s_.crit == true
        &&& sent_packets == Set::<LPacket>::empty()
        &&& s_.clock == s.clock
        &&& s_.req == s.req
        &&& s_.ack == s.ack
        &&& s_.send_seq == s.send_seq
        &&& s_.recv_seq == s.recv_seq
    }

    /// Leave the critical section and notify every peer.
    pub open spec fn LExit(
        s: LState,
        s_: LState,
        c: LConstants,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& s.crit
        &&& s_.crit == false
        &&& sent_packets == c.proc.remove(c.node_id).map(
                |d: int| LPacket { dst: d, msg: LMessage::Rel { seq: s.send_seq[d] } },
            )
        &&& s_.send_seq == LAdvanceAll(s, c)
        &&& s_.req == s.req.insert(c.node_id, 0)
        &&& s_.ack == Set::<int>::empty()
        &&& s_.clock == s.clock
        &&& s_.recv_seq == s.recv_seq
    }

    /// Receive a release notification.
    pub open spec fn LReceiveRelease(
        s: LState,
        s_: LState,
        c: LConstants,
        src: int,
        seq: int,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& seq == s.recv_seq[src]
        &&& s_.req == s.req.insert(src, 0)
        &&& s_.recv_seq == s.recv_seq.insert(src, s.recv_seq[src] + 1)
        &&& sent_packets == Set::<LPacket>::empty()
        &&& s_.clock == s.clock
        &&& s_.ack == s.ack
        &&& s_.crit == s.crit
        &&& s_.send_seq == s.send_seq
    }

    /// Dispatch on the received message.
    pub open spec fn LHandleMessage(
        s: LState,
        s_: LState,
        c: LConstants,
        src: int,
        msg: LMessage,
        sent_packets: Set<LPacket>,
    ) -> bool {
        match msg {
            LMessage::Req { clock, seq } =>
                LReceiveRequest(s, s_, c, src, clock, seq, sent_packets),
            LMessage::Ack { seq } => LReceiveAck(s, s_, c, src, seq, sent_packets),
            LMessage::Rel { seq } => LReceiveRelease(s, s_, c, src, seq, sent_packets),
        }
    }

    pub open spec fn LNext(
        s: LState,
        s_: LState,
        c: LConstants,
        sent_packets: Set<LPacket>,
    ) -> bool {
        ||| LRequest(s, s_, c, sent_packets)
        ||| LEnter(s, s_, c, sent_packets)
        ||| LExit(s, s_, c, sent_packets)
        ||| (exists|src: int, msg: LMessage|
                LHandleMessage(s, s_, c, src, msg, sent_packets))
    }
}
