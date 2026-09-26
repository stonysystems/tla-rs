use super::types::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub open spec fn init(s: State, c: Constants) -> bool {
    &&& valid_constants(c)
    &&& s.nodes == Seq::new(c.n as nat, |i: int| empty_node())
    &&& s.network == Set::<Packet>::empty()
    &&& s.submitted == Map::<Instance, Attributes>::empty()
}

pub open spec fn packet(kind: Kind, src: int, dst: int, id: Instance,
    ballot: int, attrs: Attributes) -> Packet {
    Packet { kind, src, dst, instance: id, ballot, attrs,
        snapshot: empty_record(), invalidating: Set::empty() }
}

pub open spec fn broadcast(c: Constants, p: Packet) -> Set<Packet> {
    members(c).map(|dst: int| Packet { dst, ..p })
}

pub open spec fn known_conflicts(c: Constants, n: Node, id: Instance, payload: Payload) -> Set<Instance> {
    n.log.dom().filter(|other: Instance|
        other != id && conflicts(c, n.log[other].attrs.payload, payload))
}

pub open spec fn replace_node(s: State, node: int, n: Node, output: Set<Packet>) -> State {
    State { nodes: s.nodes.update(node, n), network: s.network.union(output), ..s }
}

pub open spec fn route(s: State, c: Constants, p: Packet) -> bool {
    &&& s.nodes.len() == c.n
    &&& s.network.contains(p)
    &&& member(c, p.src)
    &&& member(c, p.dst)
    &&& member(c, p.instance.owner)
    &&& p.ballot >= 0
}

/// A batch represents delivered replies, not a read of remote replica state.
/// Snapshots may be arbitrarily old; each reply must have actually been sent.
pub open spec fn replies(s: State, c: Constants, node: int, id: Instance,
    ballot: int, kind: Kind, batch: Map<int, Packet>) -> bool {
    &&& batch.dom().subset_of(members(c))
    &&& forall |sender: int| #[trigger] batch.dom().contains(sender) ==> {
        let p = batch[sender];
        &&& s.network.contains(p)
        &&& p.src == sender
        &&& p.dst == node
        &&& p.instance == id
        &&& p.ballot == ballot
        &&& p.kind == kind
    }
}

pub open spec fn active(s: State, node: int, id: Instance, b: int, stage: Stage) -> bool {
    &&& s.nodes[node].attempts.dom().contains(id)
    &&& s.nodes[node].attempts[id].ballot == b
    &&& s.nodes[node].attempts[id].stage == stage
    &&& record(s.nodes[node], id).promise == b
}

pub open spec fn attempt(b: int, stage: Stage, attrs: Attributes) -> Attempt {
    Attempt { ballot: b, stage, candidate: attrs, quorum: Set::empty(), invalidating: Set::empty() }
}

/// Self-delivery of submission is atomic, as in the reference protocol.
pub open spec fn submit(s: State, s_: State, c: Constants, node: int, value: int) -> bool {
    let n = s.nodes[node];
    let id = Instance { owner: node, slot: n.next_slot };
    let attrs = Attributes { payload: Payload::Command { value },
        deps: known_conflicts(c, n, id, Payload::Command { value }) };
    let r = Record { phase: Phase::PreAccepted, attrs, original: attrs.payload,
        initial_deps: attrs.deps, ..empty_record() };
    let updated = Node { log: n.log.insert(id, r), next_slot: n.next_slot + 1,
        attempts: n.attempts.insert(id, attempt(0, Stage::Initial, attrs)), ..n };
    let request = packet(Kind::PreAccept, node, node, id, 0, attrs);
    let reply = packet(Kind::PreAcceptOk, node, node, id, 0, attrs);
    &&& s.nodes.len() == c.n
    &&& member(c, node)
    &&& s_ == (State { submitted: s.submitted.insert(id, attrs),
        ..replace_node(s, node, updated, broadcast(c, request).insert(reply)) })
}

pub open spec fn preaccept(s: State, s_: State, c: Constants, p: Packet) -> bool {
    let n = s.nodes[p.dst];
    let r = record(n, p.instance);
    let attrs = Attributes { deps: p.attrs.deps.union(
        known_conflicts(c, n, p.instance, p.attrs.payload)), ..p.attrs };
    let updated = Record { phase: Phase::PreAccepted, attrs,
        original: p.attrs.payload, initial_deps: p.attrs.deps, ..r };
    let reply = packet(Kind::PreAcceptOk, p.dst, p.src, p.instance, 0, attrs);
    &&& route(s, c, p)
    &&& p.kind is PreAccept
    &&& p.src == p.instance.owner
    &&& p.ballot == 0
    &&& p.attrs.payload is Command
    &&& r.promise == 0
    &&& r.phase is Initial
    &&& s_ == replace_node(s, p.dst, Node { log: n.log.insert(p.instance, updated), ..n }, set![reply])
}

pub open spec fn union_reply_deps(batch: Map<int, Packet>) -> Set<Instance> {
    batch.dom().map(|node: int| batch[node].attrs.deps).flatten()
}

/// The coordinator fixes one proposal before broadcasting it. Its own
/// Accepted/Committed record is durable; the remaining attempt is volatile.
pub open spec fn publish(s: State, c: Constants, node: int, id: Instance,
    b: int, attrs: Attributes, commit: bool) -> State {
    let n = s.nodes[node];
    let r = record(n, id);
    let kind = if commit { Kind::Commit } else { Kind::Accept };
    let updated = Record { promise: b, accepted_ballot: b, attrs,
        phase: if commit { Phase::Committed } else { Phase::Accepted }, ..r };
    let output = broadcast(c, packet(kind, node, node, id, b, attrs));
    let output = if commit { output } else {
        output.insert(packet(Kind::AcceptOk, node, node, id, b, attrs))
    };
    replace_node(s, node, Node { log: n.log.insert(id, updated),
        attempts: n.attempts.insert(id,
            attempt(b, if commit { Stage::Done } else { Stage::Accepting }, attrs)), ..n }, output)
}

pub open spec fn finish_preaccept(s: State, s_: State, c: Constants,
    node: int, id: Instance, batch: Map<int, Packet>) -> bool {
    let r = record(s.nodes[node], id);
    let attrs = Attributes { payload: r.attrs.payload, deps: union_reply_deps(batch) };
    let fast = fast_quorum(c, batch.dom()) && forall |q: int| #[trigger] batch.dom().contains(q)
        ==> batch[q].attrs.deps == r.initial_deps;
    &&& s.nodes.len() == c.n
    &&& member(c, node)
    &&& node == id.owner
    &&& active(s, node, id, 0, Stage::Initial)
    &&& r.phase is PreAccepted
    &&& majority(c, batch.dom())
    &&& replies(s, c, node, id, 0, Kind::PreAcceptOk, batch)
    &&& s_ == publish(s, c, node, id, 0, attrs, fast)
}

pub open spec fn accept(s: State, s_: State, c: Constants, p: Packet) -> bool {
    let n = s.nodes[p.dst];
    let r = record(n, p.instance);
    let updated = Record { promise: p.ballot, accepted_ballot: p.ballot,
        phase: Phase::Accepted, attrs: p.attrs, ..r };
    let reply = packet(Kind::AcceptOk, p.dst, p.src, p.instance, p.ballot, p.attrs);
    &&& route(s, c, p)
    &&& p.kind is Accept
    &&& owns_ballot(c, p.src, p.instance, p.ballot)
    &&& r.promise <= p.ballot
    &&& (r.promise == p.ballot ==> !(r.phase is Committed))
    &&& s_ == replace_node(s, p.dst, Node { log: n.log.insert(p.instance, updated), ..n }, set![reply])
}

pub open spec fn finish_accept(s: State, s_: State, c: Constants,
    node: int, id: Instance, b: int, batch: Map<int, Packet>) -> bool {
    let r = record(s.nodes[node], id);
    &&& s.nodes.len() == c.n
    &&& member(c, node)
    &&& active(s, node, id, b, Stage::Accepting)
    &&& r.phase is Accepted
    &&& r.accepted_ballot == b
    &&& majority(c, batch.dom())
    &&& replies(s, c, node, id, b, Kind::AcceptOk, batch)
    &&& s_ == publish(s, c, node, id, b, r.attrs, true)
}

pub open spec fn learn(s: State, s_: State, c: Constants, p: Packet) -> bool {
    let n = s.nodes[p.dst];
    let r = record(n, p.instance);
    let updated = Record { accepted_ballot: p.ballot, phase: Phase::Committed,
        attrs: p.attrs, ..r };
    &&& route(s, c, p)
    &&& p.kind is Commit
    &&& owns_ballot(c, p.src, p.instance, p.ballot)
    &&& r.promise == p.ballot
    &&& s_ == replace_node(s, p.dst, Node { log: n.log.insert(p.instance, updated), ..n }, Set::empty())
}

pub open spec fn reboot(s: State, s_: State, c: Constants, node: int) -> bool {
    &&& s.nodes.len() == c.n
    &&& member(c, node)
    &&& s_ == replace_node(s, node,
        Node { attempts: Map::empty(), ..s.nodes[node] }, Set::empty())
}

} // verus!
