//! Committed transactions writing the same key have disjoint lifetimes.
use vstd::prelude::*;
use super::cahill::*;
use super::cahill_support as support;
use super::cahill_records as records;
use super::cahill_lifecycle as lifecycle;
use super::cahill_history_order as order;
use super::cahill_recent as recent;
use super::cahill_first_committer as first;
use super::cahill_commit_effect as effect;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::seq_lib::group_seq_properties };
pub open spec fn before(h: Seq<Event>,t: int,w: int) -> bool { position(h,Event { txn: t,op: Op::Commit }) < start(h,w) }
pub open spec fn safe(s: LState) -> bool {
    forall |t: int,w: int,k: int| committed(s.history).contains(t) && committed(s.history).contains(w) && t != w
        && #[trigger] keys(s.history,t,false).contains(k) && #[trigger] keys(s.history,w,false).contains(k)
        ==> before(s.history,t,w) || before(s.history,w,t)
}
pub proof fn stable(h: Seq<Event>,d: Seq<Event>,t: int,w: int)
    requires lifecycle::valid(d),h.is_prefix_of(d),committed(h).contains(t),committed(h).contains(w)
    ensures before(h,t,w) == before(d,t,w)
{
    assert(h =~= d.take(h.len() as int)); lifecycle::prefix_valid(d,h.len() as int);
    order::endpoint(h,t); order::endpoint(h,w); order::prefix(h,d);
    order::commit_prefix(h,d,t); order::start_prefix(h,d,w);
}
pub proof fn precedes_new(s: LState,c: Constants,a: Action,t: int,w: int,k: int)
    requires support::inductive(s,c),records::exact(s,c),lifecycle::valid(s.history),first::safe(s,c),enabled(s,c,a),effect::added(s,a) == Some(t),
        committed(s.history).contains(w),keys(s.history,w,false).contains(k),keys(s.history,t,false).contains(k)
    ensures before(apply(s,c,a).history,w,t)
{
    let u=apply(s,c,a); effect::summary(s,c,a); lifecycle::preserve(s,c,a); order::step_prefix(s,c,a);
    assert(records::node(s,t)); assert(first::protected(s,t,k)); assert(writers_since(s,t,k).is_empty());
    recent::member(s,t,k,w); lifecycle::start_position(s.history,t); order::endpoint(s.history,w);
    let end=position(s.history,Event { txn: w,op: Op::Commit });
    assert(end != start(s.history,t)); order::start_prefix(s.history,u.history,t); order::commit_prefix(s.history,u.history,w);
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::inductive(s,c),records::exact(s,c),lifecycle::valid(s.history),first::safe(s,c),safe(s),enabled(s,c,a)
    ensures safe(apply(s,c,a))
{
    let u=apply(s,c,a); effect::summary(s,c,a); lifecycle::preserve(s,c,a); order::step_prefix(s,c,a);
    assert forall |t: int,w: int,k: int| committed(u.history).contains(t) && committed(u.history).contains(w) && t != w
        && #[trigger] keys(u.history,t,false).contains(k) && #[trigger] keys(u.history,w,false).contains(k)
        implies before(u.history,t,w) || before(u.history,w,t) by {
        if committed(s.history).contains(t) && committed(s.history).contains(w) {
            recent::ended_keys(s.history,u.history,t,false); recent::ended_keys(s.history,u.history,w,false);
            stable(s.history,u.history,t,w); stable(s.history,u.history,w,t);
        } else {
            effect::keys_unchanged(s,c,a,t,false); effect::keys_unchanged(s,c,a,w,false);
            if !committed(s.history).contains(t) { precedes_new(s,c,a,t,w,k); }
            else { precedes_new(s,c,a,w,t,k); }
        }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires support::safety_spec(b,c),time >= 0
    ensures safe(b[time])
    decreases time
{
    if time == 0 { assert(b[0].history.to_set() =~= Set::<Event>::empty()); }
    else {
        at(b,c,time-1); support::at(b,c,time-1); records::at(b,c,time-1); lifecycle::at(b,c,time-1); first::at(b,c,time-1);
        let a=support::step(b,c,time-1); preserve(b[time-1],c,a);
    }
}
} // verus!
