//! Event order and transaction endpoints in append-only reachable histories.
use vstd::prelude::*;
use super::cahill::*;
use super::cahill_history as history;
use super::cahill_lifecycle as lifecycle;
use super::cahill_support as support;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures, vstd::set::Set::lemma_map_contains };
pub proof fn prefix(h: Seq<Event>,d: Seq<Event>)
    requires h.is_prefix_of(d)
    ensures all(h).subset_of(all(d)),committed(h).subset_of(committed(d)),aborted(h).subset_of(aborted(d))
{
    assert(d =~= h+d.skip(h.len() as int)); history::concat(h,d.skip(h.len() as int));
}
pub proof fn event_summary(h: Seq<Event>,i: int)
    requires 0 <= i < h.len()
    ensures all(h).contains(h[i].txn),h[i].op == Op::Commit ==> committed(h).contains(h[i].txn),
        h[i].op is Abort ==> aborted(h).contains(h[i].txn)
{
    lifecycle::event_member(h,i);
    if h[i].op == Op::Commit { assert(h.to_set().filter(|e: Event| e.op == Op::Commit).contains(h[i])); }
    if h[i].op is Abort { assert(h.to_set().filter(|e: Event| e.op is Abort).contains(h[i])); }
}
pub proof fn permitted(h: Seq<Event>,i: int)
    requires lifecycle::valid(h),0 <= i < h.len()
    ensures lifecycle::permitted(h.take(i),h[i])
{
    lifecycle::prefix_valid(h,i+1); assert(h.take(i+1).drop_last() =~= h.take(i)); assert(h.take(i+1).last() == h[i]);
}
pub proof fn ordered(h: Seq<Event>,i: int,j: int)
    requires lifecycle::valid(h),0 <= i < j < h.len(),h[i].txn == h[j].txn
    ensures h[i].op != Op::Commit,!(h[i].op is Abort),h[j].op != Op::Begin
{
    permitted(h,j); event_summary(h.take(j),i); assert(h.take(j)[i] == h[i]);
}
pub proof fn commit_member(h: Seq<Event>,t: int)
    ensures committed(h).contains(t) <==> h.contains(Event { txn: t,op: Op::Commit })
{
    if committed(h).contains(t) {
        let e=choose |e: Event| h.to_set().contains(e) && e.op == Op::Commit && e.txn == t;
        assert(e == (Event { txn: t,op: Op::Commit }));
    } else if h.contains(Event { txn: t,op: Op::Commit }) {
        assert(h.to_set().filter(|e: Event| e.op == Op::Commit).contains(Event { txn: t,op: Op::Commit }));
    }
}
pub proof fn disjoint(h: Seq<Event>)
    requires lifecycle::valid(h)
    ensures committed(h).disjoint(aborted(h))
{
    assert forall |t: int| committed(h).contains(t) implies !aborted(h).contains(t) by {
        if aborted(h).contains(t) {
            commit_member(h,t); let e=Event { txn: t,op: Op::Commit };
            let d=choose |d: Event| h.to_set().contains(d) && d.op is Abort && d.txn == t;
            let i=choose |i: int| 0 <= i < h.len() && h[i] == e;
            let j=choose |j: int| 0 <= j < h.len() && h[j] == d;
            if i < j { ordered(h,i,j); } else if j < i { ordered(h,j,i); }
        }
    }
}
pub proof fn endpoint(h: Seq<Event>,t: int)
    requires lifecycle::valid(h),committed(h).contains(t)
    ensures 1 <= start(h,t) < position(h,Event { txn: t,op: Op::Commit }) <= h.len(),
        h[position(h,Event { txn: t,op: Op::Commit })-1] == (Event { txn: t,op: Op::Commit }),
        forall |i: int| 0 <= i < h.len() && (#[trigger] h[i]).txn == t ==> i < position(h,Event { txn: t,op: Op::Commit }),
        forall |i: int| 0 <= i < h.len() && #[trigger] h[i] == (Event { txn: t,op: Op::Commit }) ==> i == position(h,Event { txn: t,op: Op::Commit })-1
{
    commit_member(h,t); let e=Event { txn: t,op: Op::Commit };
    let i=choose |i: int| 0 <= i < h.len() && h[i] == e;
    event_summary(h,i); lifecycle::start_position(h,t); let begin=lifecycle::unique_begin(h,t);
    assert forall |j: int| 0 <= j < h.len() && (#[trigger] h[j]).txn == t implies j <= i by {
        if i < j { ordered(h,i,j); }
    }
    assert forall |j: int| 0 <= j < h.len() && #[trigger] h[j] == e implies j == i by {
        if j < i { ordered(h,j,i); }
    }
    assert(h[i+1-1] == e); assert(position(h,e) == i+1);
}
pub proof fn step_prefix(s: LState,c: Constants,a: Action)
    ensures s.history.is_prefix_of(apply(s,c,a).history)
{
    reveal(apply); reveal(commit); reveal(read); reveal(acquire);
    match a {
        Action::Commit(t) => { assert(s.history.is_prefix_of(s.history.push(Event { txn: t,op: Op::Commit })+aborts(losers(s,c,t)))); },
        _ => {},
    }
}
pub proof fn between(b: Behavior<LState>,c: Constants,first: int,last: int)
    requires support::safety_spec(b,c),0 <= first <= last
    ensures b[first].history.is_prefix_of(b[last].history)
    decreases last-first
{
    if first < last {
        between(b,c,first,last-1); let a=support::step(b,c,last-1); step_prefix(b[last-1],c,a);
        assert forall |i: int| 0 <= i < b[first].history.len() implies b[first].history[i] == #[trigger] b[last].history[i] by {
            assert(b[first].history[i] == b[last-1].history[i]);
        }
    }
}
pub proof fn start_prefix(h: Seq<Event>,d: Seq<Event>,t: int)
    requires lifecycle::valid(d),h.is_prefix_of(d),all(h).contains(t)
    ensures start(h,t) == start(d,t)
{
    assert(h =~= d.take(h.len() as int)); lifecycle::prefix_valid(d,h.len() as int);
    prefix(h,d); lifecycle::start_position(h,t); lifecycle::start_position(d,t); let at=lifecycle::unique_begin(d,t);
    assert(d[start(h,t)-1] == h[start(h,t)-1]);
}
pub proof fn commit_prefix(h: Seq<Event>,d: Seq<Event>,t: int)
    requires lifecycle::valid(d),h.is_prefix_of(d),committed(h).contains(t)
    ensures position(h,Event { txn: t,op: Op::Commit }) == position(d,Event { txn: t,op: Op::Commit })
{
    assert(h =~= d.take(h.len() as int)); lifecycle::prefix_valid(d,h.len() as int);
    prefix(h,d); endpoint(h,t); endpoint(d,t);
    let pos=position(h,Event { txn: t,op: Op::Commit }); assert(d[pos-1] == h[pos-1]);
}
} // verus!
