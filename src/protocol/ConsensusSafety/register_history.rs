//! Linearizability of finite register histories via an explicit strict total order.
//! Writes are listed in execution order. Pending writes that have executed are
//! included in the completion; unexecuted invocations may be omitted.
use vstd::prelude::*;
verus! {
pub struct Write { pub value: int, pub call: int, pub commit: int, pub reply: Option<int> }
pub struct Read { pub call: int, pub execute: int, pub reply: int, pub cut: int, pub result: int }
pub struct History { pub writes: Seq<Write>, pub reads: Map<int, Read>, pub initial: int }
pub type Op = (int, int); // (0, write index) or (1, read identifier)
pub open spec fn valid(h: History, op: Op) -> bool {
    (op.0 == 0 && 0 <= op.1 < h.writes.len()) || (op.0 == 1 && h.reads.dom().contains(op.1))
}
pub open spec fn invocation(h: History, op: Op) -> int {
    if op.0 == 0 { h.writes[op.1].call } else { h.reads[op.1].call }
}
pub open spec fn response(h: History, op: Op) -> Option<int> {
    if op.0 == 0 { h.writes[op.1].reply } else { Some(h.reads[op.1].reply) }
}
pub open spec fn rank(h: History, op: Op) -> int {
    if op.0 == 0 { 2 * op.1 + 1 } else { 2 * h.reads[op.1].cut }
}
pub open spec fn tie(h: History, op: Op) -> int {
    if op.0 == 0 { 0 } else { h.reads[op.1].reply }
}
pub open spec fn before(h: History, a: Op, b: Op) -> bool {
    rank(h, a) < rank(h, b) || (rank(h, a) == rank(h, b)
        && (tie(h, a) < tie(h, b) || (tie(h, a) == tie(h, b) && a.1 < b.1)))
}
pub open spec fn prefix_value(h: History, n: int) -> int {
    if n == 0 { h.initial } else { h.writes[n - 1].value }
}
pub open spec fn execution_ok(h: History) -> bool {
    &&& forall|i: int| 0 <= i < h.writes.len() ==> h.writes[i].call < h.writes[i].commit
        && match h.writes[i].reply { Some(t) => h.writes[i].commit < t, None => true }
    &&& forall|i: int, j: int| 0 <= i < j < h.writes.len() ==> h.writes[i].commit < h.writes[j].commit
    &&& forall|r: int| h.reads.dom().contains(r) ==> h.reads[r].call < h.reads[r].execute < h.reads[r].reply
        && 0 <= h.reads[r].cut <= h.writes.len() && h.reads[r].result == prefix_value(h, h.reads[r].cut)
    &&& forall|r: int, i: int| h.reads.dom().contains(r) && 0 <= i < h.reads[r].cut
        ==> h.writes[i].commit <= h.reads[r].execute
}
pub open spec fn fresh(h: History) -> bool {
    forall|r: int, i: int| h.reads.dom().contains(r) && 0 <= i < h.writes.len()
        && h.writes[i].commit < h.reads[r].call ==> i < h.reads[r].cut
}
// A strict total order of operations is a sequential history. Every completed
// operation appears; the included pending writes obtain responses in its
// completion. The last clause gives the register's sequential specification.
pub open spec fn linearization(h: History, order: spec_fn(Op, Op) -> bool) -> bool {
    &&& forall|a: Op| valid(h, a) ==> !(order)(a, a)
    &&& forall|a: Op, b: Op| valid(h, a) && valid(h, b) && a != b ==> (order)(a, b) != (order)(b, a)
    &&& forall|a: Op, b: Op, c: Op| valid(h, a) && valid(h, b) && valid(h, c)
        && (order)(a, b) && (order)(b, c) ==> (order)(a, c)
    &&& forall|a: Op, b: Op| valid(h, a) && valid(h, b) && response(h, a) is Some
        && response(h, a)->Some_0 < invocation(h, b) ==> (order)(a, b)
    &&& forall|r: int| h.reads.dom().contains(r) ==> {
        let x = h.reads[r];
        if x.cut == 0 {
            x.result == h.initial && forall|i: int| 0 <= i < h.writes.len() ==> !(#[trigger] (order)((0, i), (1, r)))
        } else {
            0 <= x.cut - 1 < h.writes.len() && x.result == h.writes[x.cut - 1].value
            && (order)((0, x.cut - 1), (1, r))
            && forall|i: int| 0 <= i < h.writes.len() && #[trigger] (order)((0, i), (1, r))
                ==> i == x.cut - 1 || (order)((0, i), (0, x.cut - 1))
        }
    }
}
pub proof fn ranks_distinguish_kinds(h: History, a: Op, b: Op)
    requires valid(h, a), valid(h, b), rank(h, a) == rank(h, b),
    ensures a.0 == b.0, a.0 == 0 ==> a == b,
{}
pub proof fn real_time(h: History, a: Op, b: Op)
    requires execution_ok(h), fresh(h), valid(h, a), valid(h, b), response(h, a) is Some,
        response(h, a)->Some_0 < invocation(h, b),
    ensures before(h, a, b),
{
    if a.0 == 0 && b.0 == 0 {
        assert(h.writes[a.1].commit < h.writes[b.1].commit);
        if a.1 > b.1 { assert(h.writes[b.1].commit < h.writes[a.1].commit); }
    } else if a.0 == 0 && b.0 == 1 {
        assert(h.writes[a.1].commit < h.reads[b.1].call);
        assert(a.1 < h.reads[b.1].cut);
    } else if a.0 == 1 && b.0 == 0 {
        if b.1 < h.reads[a.1].cut {
            assert(h.writes[b.1].commit <= h.reads[a.1].execute);
            assert(false);
        }
    } else {
        if h.reads[a.1].cut > h.reads[b.1].cut {
            let i = h.reads[a.1].cut - 1;
            assert(0 <= i < h.writes.len());
            assert(h.writes[i].commit <= h.reads[a.1].execute < h.reads[b.1].call);
            assert(i < h.reads[b.1].cut);
        }
    }
}
pub proof fn history_linearizable(h: History)
    requires execution_ok(h), fresh(h),
    ensures linearization(h, |a: Op, b: Op| before(h, a, b)),
        exists|order: spec_fn(Op, Op) -> bool| linearization(h, order),
{
    let order = |a: Op, b: Op| before(h, a, b);
    assert forall|a: Op, b: Op| valid(h, a) && valid(h, b) && a != b
        implies (order)(a, b) != (order)(b, a) by {
        if rank(h, a) == rank(h, b) { ranks_distinguish_kinds(h, a, b); }
    }
    assert forall|a: Op, b: Op| valid(h, a) && valid(h, b) && response(h, a) is Some
        && response(h, a)->Some_0 < invocation(h, b) implies (order)(a, b) by {
        real_time(h, a, b);
    }
    assert(linearization(h, order));
}
} // verus!
