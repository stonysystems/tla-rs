//! Expected translator output for `clean.tla` (module `PaxosClean`).
//!
//! This is the **golden**: the single-process Verus spec the Phase 52
//! translator must emit. Frozen after human review and byte-compared by V3.
//!
//! Reading it beside `clean.tla`:
//!
//! - `LIsMajority` is the quorum-to-counting rewrite (P4). The source's
//!   `Cardinality(s) * 2 > Cardinality(Acceptor)` becomes `s_arg.len() * 2 >
//!   c.acceptor.len()`; the parameter is renamed because the source calls it
//!   `s`, which is the projected spec's own state parameter.
//! - `LPhase1a` and `LPhase2a` take the parameters the source's actions take
//!   beyond the node, and `LNext` quantifies them exactly as the source does
//!   with `\E b \in Ballot`.
//! - `LPhase1bReply` shows a conditional update: the source assigns
//!   `promiseBal'` in both branches of an `IF`, which becomes one conjunct
//!   whose value is the conditional.
//! - `LMessage::M1a` and friends carry an `M` prefix because the source's tags
//!   are `"1a"`, `"1b"`, `"2a"`, `"2b"`, and `LMessage::1a` is not a Rust
//!   identifier.
//! - The dispatch ends in `_ => false`: nothing in this slice reacts to a `2b`
//!   message, and a message no action handles cannot be acted on.
//!
//! No counterpart is emitted for `Consistency` or `TypeOK`: both quantify over
//! all nodes, and a global property does not project onto one.

use vstd::prelude::*;

verus! {
    /// Wire messages. Routing lives on the packet, not in the payload.
    pub enum LMessage {
        M1a { bal: int, mbal: int, mval: int },
        M1b { bal: int, mbal: int, mval: int },
        M2a { bal: int, mbal: int, mval: int },
        M2b { bal: int, mbal: int, mval: int },
    }

    /// A message addressed to a peer.
    pub struct LPacket {
        pub dst: int,
        pub msg: LMessage,
    }

    /// This node's state.
    pub struct LState {
        pub max_bal: int,
        pub max_v_bal: int,
        pub max_val: int,
        pub leader_bal: int,
        pub promises: Set<int>,
        pub promise_bal: int,
        pub promise_val: int,
        pub proposed: bool,
    }

    /// Protocol constants, including this node's own identity.
    pub struct LConstants {
        pub value: Set<int>,
        pub acceptor: Set<int>,
        pub max_ballot: int,
        pub node_id: int,
    }

    pub open spec fn LIsMajority(c: LConstants, s_arg: Set<int>) -> bool {
        (s_arg.len() as int) * 2 > (c.acceptor.len() as int)
    }

    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        &&& s.max_bal == -1
        &&& s.max_v_bal == -1
        &&& s.max_val == -1
        &&& s.leader_bal == -1
        &&& s.promises == Set::<int>::empty()
        &&& s.promise_bal == -1
        &&& s.promise_val == -1
        &&& s.proposed == false
    }

    pub open spec fn LPhase1a(
        s: LState,
        s_: LState,
        c: LConstants,
        b: int,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& b > s.leader_bal
        &&& s_.leader_bal == b
        &&& s_.promises == Set::<int>::empty()
        &&& s_.promise_bal == -1
        &&& s_.promise_val == -1
        &&& s_.proposed == false
        &&& sent_packets == c.value.map(|d: int| LPacket { dst: d, msg: LMessage::M1a { bal: b, mbal: -1, mval: -1 } })
        &&& s_.max_bal == s.max_bal
        &&& s_.max_v_bal == s.max_v_bal
        &&& s_.max_val == s.max_val
    }

    pub open spec fn LPhase1b(
        s: LState,
        s_: LState,
        c: LConstants,
        src: int,
        bal: int,
        mbal: int,
        mval: int,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& bal > s.max_bal
        &&& s_.max_bal == bal
        &&& sent_packets == set![LPacket { dst: src, msg: LMessage::M1b { bal: bal, mbal: s.max_v_bal, mval: s.max_val } }]
        &&& s_.max_v_bal == s.max_v_bal
        &&& s_.max_val == s.max_val
        &&& s_.leader_bal == s.leader_bal
        &&& s_.promises == s.promises
        &&& s_.promise_bal == s.promise_bal
        &&& s_.promise_val == s.promise_val
        &&& s_.proposed == s.proposed
    }

    pub open spec fn LPhase1bReply(
        s: LState,
        s_: LState,
        c: LConstants,
        src: int,
        bal: int,
        mbal: int,
        mval: int,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& bal == s.leader_bal
        &&& s_.promises == s.promises.union(set![src])
        &&& s_.promise_bal == if mbal > s.promise_bal { mbal } else { s.promise_bal }
        &&& s_.promise_val == if mbal > s.promise_bal { mval } else { s.promise_val }
        &&& sent_packets == Set::<LPacket>::empty()
        &&& s_.max_bal == s.max_bal
        &&& s_.max_v_bal == s.max_v_bal
        &&& s_.max_val == s.max_val
        &&& s_.leader_bal == s.leader_bal
        &&& s_.proposed == s.proposed
    }

    pub open spec fn LPhase2a(
        s: LState,
        s_: LState,
        c: LConstants,
        v: int,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& s.leader_bal != -1
        &&& !(s.proposed)
        &&& LIsMajority(c, s.promises)
        &&& if s.promise_bal == -1 { true } else { v == s.promise_val }
        &&& s_.proposed == true
        &&& sent_packets == c.value.map(|d: int| LPacket { dst: d, msg: LMessage::M2a { bal: s.leader_bal, mbal: -1, mval: v } })
        &&& s_.max_bal == s.max_bal
        &&& s_.max_v_bal == s.max_v_bal
        &&& s_.max_val == s.max_val
        &&& s_.leader_bal == s.leader_bal
        &&& s_.promises == s.promises
        &&& s_.promise_bal == s.promise_bal
        &&& s_.promise_val == s.promise_val
    }

    pub open spec fn LPhase2b(
        s: LState,
        s_: LState,
        c: LConstants,
        src: int,
        bal: int,
        mbal: int,
        mval: int,
        sent_packets: Set<LPacket>,
    ) -> bool {
        &&& bal >= s.max_bal
        &&& s_.max_bal == bal
        &&& s_.max_v_bal == bal
        &&& s_.max_val == mval
        &&& sent_packets == set![LPacket { dst: src, msg: LMessage::M2b { bal: bal, mbal: -1, mval: mval } }]
        &&& s_.leader_bal == s.leader_bal
        &&& s_.promises == s.promises
        &&& s_.promise_bal == s.promise_bal
        &&& s_.promise_val == s.promise_val
        &&& s_.proposed == s.proposed
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
            LMessage::M1a { bal, mbal, mval } =>
                LPhase1b(s, s_, c, src, bal, mbal, mval, sent_packets),
            LMessage::M1b { bal, mbal, mval } =>
                LPhase1bReply(s, s_, c, src, bal, mbal, mval, sent_packets),
            LMessage::M2a { bal, mbal, mval } =>
                LPhase2b(s, s_, c, src, bal, mbal, mval, sent_packets),
            _ => false,
        }
    }

    pub open spec fn LNext(
        s: LState,
        s_: LState,
        c: LConstants,
        sent_packets: Set<LPacket>,
    ) -> bool {
        ||| (exists|b: int|
                0 <= b && b <= c.max_ballot && LPhase1a(s, s_, c, b, sent_packets))
        ||| (exists|v: int|
                c.value.contains(v) && LPhase2a(s, s_, c, v, sent_packets))
        ||| (exists|src: int, msg: LMessage|
                LHandleMessage(s, s_, c, src, msg, sent_packets))
    }
}
