use vstd::prelude::*;

verus! {

pub struct Instance {
    pub owner: int,
    pub slot: nat,
}

pub enum Payload { Unknown, Nop, Command { value: int } }
pub enum Phase { Initial, PreAccepted, Accepted, Committed }

pub struct Attributes {
    pub payload: Payload,
    pub deps: Set<Instance>,
}

pub struct Record {
    pub promise: int,
    pub accepted_ballot: int,
    pub phase: Phase,
    pub attrs: Attributes,
    pub original: Payload,
    pub initial_deps: Set<Instance>,
}

pub enum Stage { Initial, Recovering, Validating, Waiting, Accepting, Done }

pub struct Invalidation {
    pub instance: Instance,
    pub committed: bool,
}

pub struct Attempt {
    pub ballot: int,
    pub stage: Stage,
    pub candidate: Attributes,
    pub quorum: Set<int>,
    pub invalidating: Set<Invalidation>,
}

pub struct Node {
    // Durable protocol state and model-level application execution history.
    pub log: Map<Instance, Record>,
    pub next_slot: nat,
    pub executed: Seq<Instance>,
    // Volatile coordinator state; reboot clears this map.
    pub attempts: Map<Instance, Attempt>,
}

pub enum Kind {
    PreAccept, PreAcceptOk, Accept, AcceptOk, Commit,
    Recover, RecoverOk, Validate, ValidateOk, Waiting,
}

/// Uniform message envelope. Unused fields have canonical empty defaults.
/// Every response carries both instance and ballot; src/dst are model routing.
pub struct Packet {
    pub kind: Kind,
    pub src: int,
    pub dst: int,
    pub instance: Instance,
    pub ballot: int,
    pub attrs: Attributes,
    pub snapshot: Record,
    pub invalidating: Set<Invalidation>,
}

pub struct Constants {
    pub n: int,
    pub f: int,
    pub e: int,
    pub conflict: spec_fn(int, int) -> bool,
}

pub struct State {
    pub nodes: Seq<Node>,
    /// Sent packets are retained, permitting arbitrary delay and duplication.
    pub network: Set<Packet>,
    /// Deterministic observation of client submissions; not a protocol guard.
    pub submitted: Map<Instance, Attributes>,
}

pub open spec fn valid_constants(c: Constants) -> bool {
    &&& c.n >= 3
    &&& 0 <= c.e <= c.f
    &&& c.n >= 2 * c.f + 1
    &&& c.n >= 2 * c.e + c.f + 1
    &&& forall |a: int, b: int| #[trigger] (c.conflict)(a, b) == (c.conflict)(b, a)
}

pub open spec fn members(c: Constants) -> Set<int> { Set::range(0, c.n) }
pub open spec fn member(c: Constants, node: int) -> bool { 0 <= node < c.n }
pub open spec fn empty_attrs() -> Attributes {
    Attributes { payload: Payload::Unknown, deps: Set::empty() }
}
pub open spec fn nop_attrs() -> Attributes {
    Attributes { payload: Payload::Nop, deps: Set::empty() }
}
pub open spec fn empty_record() -> Record {
    Record { promise: 0, accepted_ballot: 0, phase: Phase::Initial,
        attrs: empty_attrs(), original: Payload::Unknown, initial_deps: Set::empty() }
}
pub open spec fn record(n: Node, id: Instance) -> Record {
    if n.log.dom().contains(id) { n.log[id] } else { empty_record() }
}
pub open spec fn empty_node() -> Node {
    Node { log: Map::empty(), next_slot: 0, executed: Seq::empty(), attempts: Map::empty() }
}
pub open spec fn conflicts(c: Constants, a: Payload, b: Payload) -> bool {
    match (a, b) {
        (Payload::Unknown, _) | (_, Payload::Unknown) => false,
        (Payload::Nop, _) | (_, Payload::Nop) => true,
        (Payload::Command { value: x }, Payload::Command { value: y }) => (c.conflict)(x, y),
    }
}
pub open spec fn stable(r: Record) -> bool { r.phase is Accepted || r.phase is Committed }
pub open spec fn id_less(a: Instance, b: Instance) -> bool {
    a.owner < b.owner || (a.owner == b.owner && a.slot < b.slot)
}
pub open spec fn owns_ballot(c: Constants, node: int, id: Instance, b: int) -> bool {
    if b == 0 { node == id.owner } else { b > 0 && b % c.n == node }
}
pub open spec fn majority(c: Constants, q: Set<int>) -> bool {
    q.subset_of(members(c)) && q.len() >= c.n - c.f
}
pub open spec fn fast_quorum(c: Constants, q: Set<int>) -> bool {
    q.subset_of(members(c)) && q.len() >= c.n - c.e
}

} // verus!
