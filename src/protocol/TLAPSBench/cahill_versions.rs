//! Snapshot versions precede the reader's begin; later committed writers are newer.
use vstd::prelude::*;
use super::cahill::*;
use super::cahill::sub;
use super::cahill_keys as keys_math;
use super::cahill_lifecycle as lifecycle;
use super::cahill_history_order as order;
use super::cahill_positions as positions;
use super::cahill_recent as recent;
use super::cahill_writer_intervals as intervals;
verus! {
broadcast use { vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq_lib::group_filter_ensures, vstd::seq::Seq::to_set_ensures, vstd::set::Set::lemma_map_contains };
pub proof fn access_bounds(h: Seq<Event>,e: Event)
    requires lifecycle::valid(h),h.contains(e),committed(h).contains(e.txn),e.op is Read || e.op is Write
    ensures start(h,e.txn) < position(h,e) < position(h,Event { txn: e.txn,op: Op::Commit })
{
    positions::found(h,e); let i=position(h,e)-1; order::endpoint(h,e.txn); let begin=lifecycle::unique_begin(h,e.txn);
    lifecycle::start_position(h,e.txn); assert(start(h,e.txn) == begin+1);
    assert(i != begin); assert(i != position(h,Event { txn: e.txn,op: Op::Commit })-1);
}
pub proof fn snapshot(s: LState,t: int,k: int)
    requires lifecycle::valid(s.history),all(s.history).contains(t),!s.txns[t].xlocks.contains(k),!version(s,t,k).is_empty()
    ensures exists |v: int| version(s,t,k) == set![v] && committed(s.history).contains(v) && s.history.contains(Event { txn: v,op: Op::Write(k) })
        && position(s.history,Event { txn: v,op: Op::Commit }) < start(s.history,t)
{
    let h=s.history; lifecycle::start_position(h,t); let first=start(h,t); let d=sub(h,1,first);
    assert(d =~= h.take(first)); lifecycle::prefix_valid(h,first); assert(d.is_prefix_of(h)); order::prefix(d,h);
    let p=|e: Event| e.op == Op::Write(k) && committed(d).contains(e.txn);
    let writes=d.filter(p); assert(writes.len() > 0); let e=writes.last(); let v=e.txn;
    d.lemma_filter_pred(p,writes.len() as int-1); assert(writes.contains(e)); d.lemma_filter_contains_rev(p,e);
    let i=choose |i: int| 0 <= i < d.len() && d[i] == e; assert(h[i] == e);
    order::endpoint(d,v); order::commit_prefix(d,h,v); order::endpoint(h,v);
    assert(position(h,Event { txn: v,op: Op::Commit }) != first);
    assert(version(s,t,k) =~= set![v]);
}
pub proof fn newer(s: LState,t: int,k: int,v: int,w: int)
    requires s.history.no_duplicates(),version(s,t,k) == set![v],s.history.contains(Event { txn: v,op: Op::Write(k) }),
        s.history.contains(Event { txn: w,op: Op::Write(k) }),position(s.history,Event { txn: v,op: Op::Write(k) }) < position(s.history,Event { txn: w,op: Op::Write(k) })
    ensures newer_versions(s,t,k).contains(w)
{
    let h=s.history; let p=|e: Event| e.op == Op::Write(k); let writes=h.filter(p);
    let ev=Event { txn: v,op: Op::Write(k) }; let ew=Event { txn: w,op: Op::Write(k) };
    positions::filter_order(h,p,ev,ew); positions::found(writes,ev); positions::found(writes,ew); positions::filter_unique(h,p);
    assert(version(s,t,k).contains(v));
    let chosen=choose |v: int| version(s,t,k).contains(v); assert(chosen == v);
    let index=choose |i: int| 1 <= i <= writes.len() && #[trigger] writes[i-1] == ev;
    positions::index(writes,index-1); assert(index == position(writes,ev));
    let at=position(writes,ew)-index-1; let tail=sub(writes,index+1,writes.len() as int);
    assert(0 <= at < tail.len()); assert(tail[at] == ew); lifecycle::event_member(tail,at);
}
pub proof fn committed_newer(s: LState,t: int,k: int,w: int)
    requires lifecycle::valid(s.history),s.history.no_duplicates(),intervals::safe(s),all(s.history).contains(t),
        committed(s.history).contains(w),keys(s.history,w,false).contains(k),start(s.history,t) < position(s.history,Event { txn: w,op: Op::Commit }),
        !s.txns[t].xlocks.contains(k),!version(s,t,k).is_empty()
    ensures newer_versions(s,t,k).contains(w)
{
    snapshot(s,t,k); let h=s.history;
    let v=choose |v: int| version(s,t,k) == set![v] && committed(h).contains(v) && h.contains(Event { txn: v,op: Op::Write(k) })
        && position(h,Event { txn: v,op: Op::Commit }) < start(h,t);
    let ev=Event { txn: v,op: Op::Write(k) }; let ew=Event { txn: w,op: Op::Write(k) };
    positions::found(h,ev); keys_math::member(h,v,false,k); assert(keys(h,v,false).contains(k));
    keys_math::member(h,w,false,k); let i=choose |i: int| 0 <= i < h.len() && keys_math::access(#[trigger] h[i],w,false) && keys_math::key(h[i]) == k;
    assert(h[i] == ew); assert(h.contains(ew));
    order::endpoint(h,v); order::endpoint(h,w); access_bounds(h,ev); access_bounds(h,ew);
    assert(intervals::before(h,v,w) || intervals::before(h,w,v)); assert(intervals::before(h,v,w));
    newer(s,t,k,v,w);
}
pub proof fn write_order(s: LState,t: int,w: int,k: int)
    requires lifecycle::valid(s.history),intervals::safe(s),committed(s.history).contains(t),committed(s.history).contains(w),
        s.history.contains(Event { txn: t,op: Op::Write(k) }),s.history.contains(Event { txn: w,op: Op::Write(k) }),
        position(s.history,Event { txn: t,op: Op::Write(k) }) < position(s.history,Event { txn: w,op: Op::Write(k) })
    ensures intervals::before(s.history,t,w)
{
    let h=s.history; let et=Event { txn: t,op: Op::Write(k) }; let ew=Event { txn: w,op: Op::Write(k) };
    positions::found(h,et); positions::found(h,ew); keys_math::member(h,t,false,k); keys_math::member(h,w,false,k);
    assert(keys(h,t,false).contains(k)); assert(keys(h,w,false).contains(k));
    access_bounds(h,et); access_bounds(h,ew); assert(intervals::before(h,t,w) || intervals::before(h,w,t));
}
} // verus!
