//! The source's WritersSince operator is exactly commit-after-begin order.
use vstd::prelude::*;
use super::cahill::*;
use super::cahill::sub;
use super::cahill_lifecycle as lifecycle;
use super::cahill_history_order as order;
use super::cahill_keys as keys_math;
verus! {
broadcast use { vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures, vstd::set::Set::lemma_map_contains };
pub proof fn member(s: LState,t: int,k: int,w: int)
    requires lifecycle::valid(s.history),all(s.history).contains(t)
    ensures writers_since(s,t,k).contains(w) <==> committed(s.history).contains(w)
        && start(s.history,t) < position(s.history,Event { txn: w,op: Op::Commit }) && keys(s.history,w,false).contains(k)
{
    let h=s.history; lifecycle::start_position(h,t); let first=start(h,t);
    let d=sub(h,first,h.len() as int); assert(d =~= h.subrange(first-1,h.len() as int));
    order::commit_member(d,w); order::commit_member(h,w); let e=Event { txn: w,op: Op::Commit };
    if committed(d).contains(w) {
        let i=choose |i: int| 0 <= i < d.len() && d[i] == e;
        assert(h[i+first-1] == e); order::event_summary(h,i+first-1); order::endpoint(h,w);
        assert(position(h,e) == i+first); assert(i != 0);
    }
    if committed(h).contains(w) && first < position(h,e) {
        order::endpoint(h,w); let i=position(h,e)-first; assert(d[i] == e); assert(d.contains(e));
    }
}
pub proof fn keys_prefix(h: Seq<Event>,d: Seq<Event>,t: int,read: bool)
    requires h.is_prefix_of(d)
    ensures keys(h,t,read).subset_of(keys(d,t,read))
{
    assert(d =~= h+d.skip(h.len() as int)); keys_math::concat(h,d.skip(h.len() as int),t,read);
}
pub proof fn ended_keys(h: Seq<Event>,d: Seq<Event>,t: int,read: bool)
    requires lifecycle::valid(d),h.is_prefix_of(d),committed(h).contains(t) || aborted(h).contains(t)
    ensures keys(h,t,read) =~= keys(d,t,read)
{
    keys_prefix(h,d,t,read);
    assert forall |k: int| keys(d,t,read).contains(k) implies keys(h,t,read).contains(k) by {
        keys_math::member(d,t,read,k); keys_math::member(h,t,read,k);
        let j=choose |j: int| 0 <= j < d.len() && keys_math::access(#[trigger] d[j],t,read) && keys_math::key(d[j]) == k;
        if j >= h.len() {
            assert(h.is_prefix_of(d.take(j))); order::prefix(h,d.take(j)); order::permitted(d,j); assert(false);
        } else { assert(h[j] == d[j]); }
    }
}
pub proof fn unchanged(s: LState,u: LState,t: int,k: int)
    requires lifecycle::valid(u.history),s.history.is_prefix_of(u.history),all(s.history).contains(t),committed(u.history) == committed(s.history)
    ensures writers_since(s,t,k) =~= writers_since(u,t,k)
{
    assert(s.history =~= u.history.take(s.history.len() as int)); lifecycle::prefix_valid(u.history,s.history.len() as int);
    order::prefix(s.history,u.history); order::start_prefix(s.history,u.history,t);
    assert forall |w: int| writers_since(s,t,k).contains(w) <==> writers_since(u,t,k).contains(w) by {
        member(s,t,k,w); member(u,t,k,w);
        if committed(s.history).contains(w) { order::commit_prefix(s.history,u.history,w); ended_keys(s.history,u.history,w,false); }
    }
}
pub proof fn new_committer(s: LState,u: LState,t: int,k: int,a: int)
    requires lifecycle::valid(u.history),s.history.is_prefix_of(u.history),all(s.history).contains(t),committed(u.history) == committed(s.history).insert(a),
        keys(u.history,a,false) == keys(s.history,a,false)
    ensures writers_since(u,t,k).subset_of(writers_since(s,t,k).union(if keys(s.history,a,false).contains(k) { set![a] } else { Set::empty() }))
{
    assert(s.history =~= u.history.take(s.history.len() as int)); lifecycle::prefix_valid(u.history,s.history.len() as int);
    order::prefix(s.history,u.history); order::start_prefix(s.history,u.history,t);
    assert forall |w: int| writers_since(u,t,k).contains(w)
        implies writers_since(s,t,k).union(if keys(s.history,a,false).contains(k) { set![a] } else { Set::empty() }).contains(w) by {
        member(s,t,k,w); member(u,t,k,w);
        if w != a { order::commit_prefix(s.history,u.history,w); ended_keys(s.history,u.history,w,false); }
    }
}
} // verus!
