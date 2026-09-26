//! Baseline EPaxos* Figure 5, excluding the highlighted optimizations.
use super::types::*;
use super::model::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

/// A timeout concerns an instance the replica learned about, including a
/// missing dependency. It cannot invent an unused future client identity.
pub open spec fn known_instance(n: Node, id: Instance) -> bool {
    n.log.dom().contains(id) || exists |other: Instance|
        #[trigger] n.log.dom().contains(other) && n.log[other].attrs.deps.contains(id)
}

pub open spec fn recovery_reply(src: int, dst: int, id: Instance, b: int, r: Record) -> Packet {
    Packet { snapshot: r, ..packet(Kind::RecoverOk, src, dst, id, b, empty_attrs()) }
}

pub open spec fn begin_recovery(s: State, s_: State, c: Constants,
    node: int, id: Instance, b: int) -> bool {
    let n = s.nodes[node];
    let r = record(n, id);
    let updated = Record { promise: b, ..r };
    let request = packet(Kind::Recover, node, node, id, b, empty_attrs());
    &&& s.nodes.len() == c.n
    &&& member(c, node)
    &&& member(c, id.owner)
    &&& known_instance(n, id)
    &&& b > r.promise
    &&& b > 0
    &&& owns_ballot(c, node, id, b)
    &&& s_ == replace_node(s, node, Node { log: n.log.insert(id, updated),
        attempts: n.attempts.insert(id, attempt(b, Stage::Recovering, empty_attrs())), ..n },
        broadcast(c, request).insert(recovery_reply(node, node, id, b, updated)))
}

pub open spec fn recover(s: State, s_: State, c: Constants, p: Packet) -> bool {
    let n = s.nodes[p.dst];
    let r = record(n, p.instance);
    let updated = Record { promise: p.ballot, ..r };
    &&& route(s, c, p)
    &&& p.kind is Recover
    &&& p.ballot > 0
    &&& owns_ballot(c, p.src, p.instance, p.ballot)
    &&& r.promise < p.ballot
    &&& s_ == replace_node(s, p.dst, Node { log: n.log.insert(p.instance, updated), ..n },
        set![recovery_reply(p.dst, p.src, p.instance, p.ballot, updated)])
}

pub open spec fn maximal(batch: Map<int, Packet>, q: int) -> bool {
    batch.dom().contains(q) && forall |other: int| #[trigger] batch.dom().contains(other)
        ==> batch[other].snapshot.accepted_ballot <= batch[q].snapshot.accepted_ballot
}

pub open spec fn maximal_committed(batch: Map<int, Packet>) -> Set<int> {
    batch.dom().filter(|q: int| maximal(batch, q) && batch[q].snapshot.phase is Committed)
}

pub open spec fn maximal_accepted(batch: Map<int, Packet>) -> Set<int> {
    batch.dom().filter(|q: int| maximal(batch, q) && batch[q].snapshot.phase is Accepted)
}

pub open spec fn pending_support(batch: Map<int, Packet>) -> Set<int> {
    batch.dom().filter(|q: int| batch[q].snapshot.phase is PreAccepted
        && batch[q].snapshot.attrs.deps == batch[q].snapshot.initial_deps)
}

pub open spec fn invalidates(c: Constants, n: Node, id: Instance,
    attrs: Attributes, other: Instance) -> bool {
    let r = record(n, other);
    &&& other != id
    &&& !attrs.deps.contains(other)
    &&& if r.phase is Committed {
        !(r.attrs.payload is Nop) && conflicts(c, r.attrs.payload, attrs.payload)
            && !r.attrs.deps.contains(id)
    } else {
        !(r.original is Unknown) && conflicts(c, r.original, attrs.payload)
            && !r.initial_deps.contains(id)
    }
}

pub open spec fn invalidations(c: Constants, n: Node, id: Instance,
    attrs: Attributes) -> Set<Invalidation> {
    n.log.dom().filter(|other: Instance| invalidates(c, n, id, attrs, other))
        .map(|other: Instance| Invalidation { instance: other,
            committed: n.log[other].phase is Committed })
}

pub open spec fn validation_record(r: Record, attrs: Attributes) -> Record {
    Record { attrs: Attributes { payload: attrs.payload, ..r.attrs },
        original: attrs.payload, initial_deps: attrs.deps, ..r }
}

pub open spec fn validation_reply(c: Constants, n: Node, p: Packet) -> Packet {
    Packet { invalidating: invalidations(c, n, p.instance, p.attrs),
        ..packet(Kind::ValidateOk, p.dst, p.src, p.instance, p.ballot, empty_attrs()) }
}

/// Duplicate hardening: a Validate cannot modify accepted attributes. A
/// legitimate validation recipient reported a non-stable record in RecoverOk.
/// This also rejects delayed validation after accepting or committing Nop.
pub open spec fn can_validate(r: Record, b: int) -> bool {
    r.promise == b && !stable(r)
}

pub open spec fn start_validation(s: State, c: Constants, node: int,
    id: Instance, b: int, attrs: Attributes, q: Set<int>) -> State {
    let n = s.nodes[node];
    let p = packet(Kind::Validate, node, node, id, b, attrs);
    let a = Attempt { quorum: q, ..attempt(b, Stage::Validating, attrs) };
    let output = q.map(|dst: int| Packet { dst, ..p });
    let self_receive = q.contains(node) && can_validate(record(n, id), b);
    let log = if self_receive { n.log.insert(id, validation_record(record(n, id), attrs)) }
        else { n.log };
    let output = if self_receive { output.insert(validation_reply(c, n, p)) } else { output };
    replace_node(s, node, Node { log, attempts: n.attempts.insert(id, a), ..n }, output)
}

/// The nondeterministic selector q ranges only over the paper's eligible
/// highest-ballot records, or the pending support if none is stable.
pub open spec fn finish_recovery(s: State, s_: State, c: Constants,
    node: int, id: Instance, b: int, batch: Map<int, Packet>, q: int) -> bool {
    let committed = maximal_committed(batch);
    let accepted = maximal_accepted(batch);
    let support = pending_support(batch);
    &&& s.nodes.len() == c.n
    &&& member(c, node)
    &&& active(s, node, id, b, Stage::Recovering)
    &&& majority(c, batch.dom())
    &&& replies(s, c, node, id, b, Kind::RecoverOk, batch)
    &&& if committed.len() > 0 {
        committed.contains(q) && s_ == publish(s, c, node, id, b, batch[q].snapshot.attrs, true)
    } else if accepted.len() > 0 {
        accepted.contains(q) && s_ == publish(s, c, node, id, b, batch[q].snapshot.attrs, false)
    } else if support.len() >= batch.dom().len() - c.e {
        support.contains(q) && s_ == start_validation(s, c, node, id, b,
            batch[q].snapshot.attrs, batch.dom())
    } else {
        s_ == publish(s, c, node, id, b, nop_attrs(), false)
    }
}

pub open spec fn validate(s: State, s_: State, c: Constants, p: Packet) -> bool {
    let n = s.nodes[p.dst];
    let r = record(n, p.instance);
    &&& route(s, c, p)
    &&& p.kind is Validate
    &&& p.ballot > 0
    &&& owns_ballot(c, p.src, p.instance, p.ballot)
    &&& can_validate(r, p.ballot)
    &&& s_ == replace_node(s, p.dst,
        Node { log: n.log.insert(p.instance, validation_record(r, p.attrs)), ..n },
        set![validation_reply(c, n, p)])
}

pub open spec fn finish_validation(s: State, s_: State, c: Constants,
    node: int, id: Instance, b: int, batch: Map<int, Packet>) -> bool {
    let n = s.nodes[node];
    let a = n.attempts[id];
    let invalidating = batch.dom().map(|q: int| batch[q].invalidating).flatten();
    let committed = invalidating.filter(|i: Invalidation| i.committed);
    &&& s.nodes.len() == c.n
    &&& member(c, node)
    &&& active(s, node, id, b, Stage::Validating)
    &&& batch.dom() == a.quorum
    &&& replies(s, c, node, id, b, Kind::ValidateOk, batch)
    &&& if invalidating.len() == 0 {
        s_ == publish(s, c, node, id, b, a.candidate, false)
    } else if committed.len() > 0 {
        s_ == publish(s, c, node, id, b, nop_attrs(), false)
    } else {
        s_ == replace_node(s, node, Node { attempts: n.attempts.insert(id,
            Attempt { stage: Stage::Waiting, invalidating, ..a }), ..n },
            broadcast(c, packet(Kind::Waiting, node, node, id, b, a.candidate)))
    }
}

pub enum Resolution { Ready, Invalidated { instance: Instance }, Waiting { packet: Packet } }

pub open spec fn resolve_waiting(s: State, s_: State, c: Constants,
    node: int, id: Instance, b: int, resolution: Resolution) -> bool {
    let n = s.nodes[node];
    let a = n.attempts[id];
    let invalid_ids = a.invalidating.map(|i: Invalidation| i.instance);
    &&& s.nodes.len() == c.n
    &&& member(c, node)
    &&& active(s, node, id, b, Stage::Waiting)
    &&& match resolution {
        Resolution::Ready => {
            &&& forall |other: Instance| #[trigger] invalid_ids.contains(other) ==> {
                let r = record(n, other);
                r.phase is Committed && (r.attrs.payload is Nop || r.attrs.deps.contains(id))
            }
            &&& s_ == publish(s, c, node, id, b, a.candidate, false)
        },
        Resolution::Invalidated { instance: other } => {
            let r = record(n, other);
            &&& invalid_ids.contains(other)
            &&& r.phase is Committed
            &&& !(r.attrs.payload is Nop)
            &&& !r.attrs.deps.contains(id)
            &&& s_ == publish(s, c, node, id, b, nop_attrs(), false)
        },
        Resolution::Waiting { packet: p } => {
            &&& route(s, c, p)
            &&& p.kind is Waiting
            &&& p.dst == node
            &&& invalid_ids.contains(p.instance)
            &&& s_ == publish(s, c, node, id, b, nop_attrs(), false)
        },
    }
}

} // verus!
