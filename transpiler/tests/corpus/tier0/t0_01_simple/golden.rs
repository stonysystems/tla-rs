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
//! `sent_packets` is a **`Set`**, not a `Seq`: the clean subset designates the
//! network as a set (C4), and a broadcast is a set comprehension over the
//! peers, so a sequence would need a delivery order the source spec does not
//! give. The rule is uniform across goldens; see
//! `t0_05_lamport_mutex/golden.rs`, where a real broadcast makes it matter.
//!
//! Two things in `clean.tla` deliberately have **no counterpart** here, and a
//! translator that emitted something for them would be wrong:
//!
//! - `Terminating` — a stuttering step. It *was* guarded by "every process is
//!   Done", which no single node can observe; Phase 52 taught the linter to
//!   reject a `Next` disjunct with no node parameter that reads node state, and
//!   this is the case it caught. `clean.tla` now guards it on `pc[self]`, so it
//!   is projectable — but it still has no counterpart here, because stuttering
//!   is what the runtime does when a node has nothing to do, exactly as `LNext`
//!   in the hand-written specs omits it.
//! - `PCorrect` — `(\A i : pc[i] = "Done") => (\E i : y[i] = 1)` quantifies
//!   over all nodes. A global property does not project onto a single node; it
//!   is a statement about the composed system and belongs to the refinement
//!   layer, not to this spec.

//!
//! Reading it beside `clean.tla`:
//!
//! - `LPc` is the projection of `pc`'s type, a set of string literals in the
//!   source. Comparing an enum-typed field to a literal is a variant test, so
//!   `pc[self] = "a"` becomes `s.pc is A`.
//! - `LLeft` is the source's `Left(i) == (i - 1) % N` with the node parameter
//!   projected away; the node's own identity survives as `c.node_id`.
//! - `LReply` takes `src` because it answers the requester; `LRecv` does not,
//!   because it never mentions the sender. A handler is given only what it
//!   uses -- the framework always knows the rest.
//! - `La` and `Lb` keep the source's names. Every projected definition is `L`
//!   plus the name it had in the spec, so the two files can be read together.

use vstd::prelude::*;

verus! {
    pub enum LPc {
        A,
        B,
        W,
        Done,
    }

    /// Wire messages. Routing lives on the packet, not in the payload.
    pub enum LMessage {
        Read,
        Val { val: int },
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

    pub open spec fn LLeft(c: LConstants) -> int {
        (c.node_id - 1) % c.n
    }

    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        &&& s.x == 0
        &&& s.y == 0
        &&& s.pc is A
    }

    pub open spec fn La(
        s: LState,
        s_: LState,
        c: LConstants,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& s.pc is A
        &&& s_.x == 1
        &&& s_.pc is B
        &&& s_.y == s.y
        &&& sent_packets == Set::<LPacket>::empty()
    }

    pub open spec fn Lb(
        s: LState,
        s_: LState,
        c: LConstants,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& s.pc is B
        &&& sent_packets == set![LPacket { dst: LLeft(c), msg: LMessage::Read }]
        &&& s_.pc is W
        &&& s_.x == s.x
        &&& s_.y == s.y
    }

    pub open spec fn LReply(
        s: LState,
        s_: LState,
        c: LConstants,
        src: int,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& sent_packets == set![LPacket { dst: src, msg: LMessage::Val { val: s.x } }]
        &&& s_.x == s.x
        &&& s_.y == s.y
        &&& s_.pc == s.pc
    }

    pub open spec fn LRecv(
        s: LState,
        s_: LState,
        c: LConstants,
        val: int,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& s.pc is W
        &&& s_.y == val
        &&& s_.pc is Done
        &&& sent_packets == Set::<LPacket>::empty()
        &&& s_.x == s.x
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
            LMessage::Read =>
                LReply(s, s_, c, src, sent_packets),
            LMessage::Val { val } =>
                LRecv(s, s_, c, val, sent_packets),
        }
    }

    pub open spec fn LNext(
        s: LState,
        s_: LState,
        c: LConstants,
        sent_packets: Set<LPacket>,
    ) -> bool {
        ||| La(s, s_, c, sent_packets)
        ||| Lb(s, s_, c, sent_packets)
        ||| (exists|src: int, msg: LMessage|
                LHandleMessage(s, s_, c, src, msg, sent_packets))
    }
}
