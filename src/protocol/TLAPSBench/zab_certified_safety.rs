//! Quorum-certified prefixes cannot conflict, even across epochs and historical times.
use vstd::prelude::*;
use super::zab::{*,equal};
use super::zab_connections as connections;
use super::zab_collections as collections;
use super::zab_entry_origins::through;
use super::zab_epoch_retention as retention;
use super::zab_history_compare as compare;
use super::zab_ack_certificates as acks;
use super::zab_commit_certificates::certified;
use super::zab_certified_retention as later;
use super::temporal::Behavior;
verus! {
pub open spec fn agree(a: Seq<Txn>,ka: int,d: Seq<Txn>,kd: int) -> bool {
    forall |p: int| 0 <= p <= ka && p <= kd ==> #[trigger] equal(a[p],d[p])
}
pub proof fn common(a: Seq<Txn>,ka: int,d: Seq<Txn>,kd: int,reference: Seq<Txn>)
    requires through(a,reference,ka),through(d,reference,kd)
    ensures agree(a,ka,d,kd)
{
    assert forall |p: int| 0 <= p <= ka && p <= kd implies #[trigger] equal(a[p],d[p]) by {
        assert(equal(a[p],reference[p])); assert(equal(d[p],reference[p]));
    }
}
pub proof fn quorum_safety(b: Behavior<LState>,c: Constants,ta: int,ea: int,a: Seq<Txn>,ka: int,td: int,ed: int,d: Seq<Txn>,kd: int)
    requires connections::safety_spec(b,c),ta >= 0,td >= 0,ea > 0,ed > 0,certified(b,c,ta,ea,a,ka),certified(b,c,td,ed,d,kd)
    ensures agree(a,ka,d,kd)
{
    let ia=choose |i: int| c.servers.contains(i) && exists |q: Set<int>| quorum(q,c)
        && forall |j: int| #![trigger q.contains(j)] q.contains(j) ==> acks::certificate(b,c,ta,i,ea,a,ka,j);
    let qa=choose |q: Set<int>| quorum(q,c) && forall |j: int| #![trigger q.contains(j)] q.contains(j) ==> acks::certificate(b,c,ta,ia,ea,a,ka,j);
    let id=choose |i: int| c.servers.contains(i) && exists |q: Set<int>| quorum(q,c)
        && forall |j: int| #![trigger q.contains(j)] q.contains(j) ==> acks::certificate(b,c,td,i,ed,d,kd,j);
    let qd=choose |q: Set<int>| quorum(q,c) && forall |j: int| #![trigger q.contains(j)] q.contains(j) ==> acks::certificate(b,c,td,id,ed,d,kd,j);
    let voter=collections::intersect_quorums(qa,qd,c);
    assert(acks::certificate(b,c,ta,ia,ea,a,ka,voter)); assert(acks::certificate(b,c,td,id,ed,d,kd,voter));
    let sa=choose |read: int| acks::witness(b,ta,ia,ea,a,ka,voter,read);
    let sd=choose |read: int| acks::witness(b,td,id,ed,d,kd,voter,read);
    if ea < ed {
        later::higher_epoch(b,c,ta,ea,a,ka,ed); assert(through(a,b[sd].nodes[voter].history,ka));
        common(a,ka,d,kd,b[sd].nodes[voter].history);
    } else if ed < ea {
        later::higher_epoch(b,c,td,ed,d,kd,ea); assert(through(d,b[sa].nodes[voter].history,kd));
        common(a,ka,d,kd,b[sa].nodes[voter].history);
    } else if sa <= sd {
        retention::between(b,c,sa,sd,voter); compare::extend(a,b[sa].nodes[voter].history,b[sd].nodes[voter].history,ka);
        common(a,ka,d,kd,b[sd].nodes[voter].history);
    } else {
        retention::between(b,c,sd,sa,voter); compare::extend(d,b[sd].nodes[voter].history,b[sa].nodes[voter].history,kd);
        common(a,ka,d,kd,b[sa].nodes[voter].history);
    }
}
} // verus!
