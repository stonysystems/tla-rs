//! Expected translator output for `clean.tla` (module `SimpleClean`).
//!
//! This is the **golden**: the single-process Verus spec the Phase 52
//! translator must emit. It is frozen after human review and byte-compared by
//! the V3 regression test. It is written in the conventions the hand-written
//! tla-rs specs already use (`src/protocol/*/`): an `LMessage` enum for the
//! wire, receive handlers taking the message's fields as scalar parameters,
//! and sends flowing out through `sent_packets`.
//!
//! What the projection did to `clean.tla`:
//!
//! - **P1 state projection.** `x`, `y`, `pc` were `[Proc -> T]`; they become
//!   this node's `int`, `int`, `LPc`. The node dimension is gone.
//! - **P2 de-index.** `x[self]` becomes `s.x`, `x'[self]` becomes `s_.x`, and
//!   `\E self \in Proc : Action(self)` becomes `LNext(s, s_, c)` about one
//!   node. The node's own identity survives as `c.node_id`, which the spec
//!   still needs because it addresses its left neighbour.
//! - **P3 network.** `network` is gone. `network' = network \cup {m}` became an
//!   entry in `sent_packets`; `\E m \in network : Recv(self, m)` became a
//!   handler whose parameters are the message's fields, since delivery is the
//!   framework's job.
//! - **P5 frame conditions.** Every action states what it leaves unchanged.
//!
//! Two things in `clean.tla` deliberately have **no counterpart** here, and a
//! translator that emitted something for them would be wrong:
//!
//! - `Terminating` — a stuttering step guarded by "every process is Done". One
//!   node cannot observe that, so the guard is not projectable. Termination
//!   handling belongs to the runtime, exactly as `LNext` in the hand-written
//!   specs omits it.
//! - `PCorrect` — `(\A i : pc[i] = "Done") => (\E i : y[i] = 1)` quantifies
//!   over all nodes. A global property does not project onto a single node; it
//!   is a statement about the composed system and belongs to the refinement
//!   layer, not to this spec.

use vstd::prelude::*;

verus! {
    /// Control state of this process.
    pub enum LPc {
        A,
        B,
        W,
        Done,
    }

    /// Wire messages. `dst` lives on the packet, not the message, matching the
    /// hand-written specs' split between payload and routing.
    pub enum LMessage {
        Read { src: int },
        Val { src: int, val: int },
    }

    /// A message addressed to a peer.
    pub struct LPacket {
        pub dst: int,
        pub msg: LMessage,
    }

    /// This node's state.
    pub struct LState {
        pub x: int,
        pub y: int,
        pub pc: LPc,
    }

    /// Protocol constants, including this node's own identity.
    pub struct LConstants {
        pub n: int,
        pub node_id: int,
    }

    /// The left neighbour in the ring: `(self - 1) % N` from the source spec.
    pub open spec fn LLeft(c: LConstants) -> int {
        (c.node_id - 1) % c.n
    }

    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        &&& s.x == 0
        &&& s.y == 0
        &&& s.pc is A
    }

    /// Step a: set my own value.
    pub open spec fn La(
        s: LState,
        s_: LState,
        c: LConstants,
        sent_packets: Seq<LPacket>,
    ) -> bool {
        &&& s.pc is A
        &&& s_.x == 1
        &&& s_.pc is B
        &&& s_.y == s.y
        &&& sent_packets == Seq::<LPacket>::empty()
    }

    /// Step b, first half: ask the left neighbour for its value.
    pub open spec fn Lb(
        s: LState,
        s_: LState,
        c: LConstants,
        sent_packets: Seq<LPacket>,
    ) -> bool {
        &&& s.pc is B
        &&& s_.pc is W
        &&& s_.x == s.x
        &&& s_.y == s.y
        &&& sent_packets == seq![
            LPacket { dst: LLeft(c), msg: LMessage::Read { src: c.node_id } },
        ]
    }

    /// Answer a read request. Enabled in any control state: the source spec's
    /// read observes this node's value wherever this node happens to be.
    pub open spec fn LReply(
        s: LState,
        s_: LState,
        c: LConstants,
        src: int,
        sent_packets: Seq<LPacket>,
    ) -> bool {
        &&& s_.x == s.x
        &&& s_.y == s.y
        &&& s_.pc == s.pc
        &&& sent_packets == seq![
            LPacket { dst: src, msg: LMessage::Val { src: c.node_id, val: s.x } },
        ]
    }

    /// Step b, second half: record the answer.
    pub open spec fn LRecv(
        s: LState,
        s_: LState,
        c: LConstants,
        val: int,
        sent_packets: Seq<LPacket>,
    ) -> bool {
        &&& s.pc is W
        &&& s_.y == val
        &&& s_.pc is Done
        &&& s_.x == s.x
        &&& sent_packets == Seq::<LPacket>::empty()
    }

    /// Dispatch on the received message, as the hand-written specs do.
    pub open spec fn LHandleMessage(
        s: LState,
        s_: LState,
        c: LConstants,
        msg: LMessage,
        sent_packets: Seq<LPacket>,
    ) -> bool {
        match msg {
            LMessage::Read { src } => LReply(s, s_, c, src, sent_packets),
            LMessage::Val { src: _, val } => LRecv(s, s_, c, val, sent_packets),
        }
    }

    pub open spec fn LNext(
        s: LState,
        s_: LState,
        c: LConstants,
        sent_packets: Seq<LPacket>,
    ) -> bool {
        ||| La(s, s_, c, sent_packets)
        ||| Lb(s, s_, c, sent_packets)
        ||| (exists |msg: LMessage| LHandleMessage(s, s_, c, msg, sent_packets))
    }
}
