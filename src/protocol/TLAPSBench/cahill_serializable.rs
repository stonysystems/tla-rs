//! Every benchmark dependency strictly increases a committed transaction's rank.
use vstd::prelude::*;
use super::cahill::*;
use super::cahill_keys as keys_math;
use super::cahill_support as support;
use super::cahill_lifecycle as lifecycle;
use super::cahill_unique as unique;
use super::cahill_history_order as order;
use super::cahill_positions as positions;
use super::cahill_writer_intervals as intervals;
use super::cahill_versions as versions;
use super::cahill_overlap as overlap;
use super::cahill_overlap_safety as overlap_safety;
use super::cahill_conflicts as conflicts;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq_lib::group_filter_ensures, vstd::seq::Seq::to_set_ensures, vstd::set::Set::lemma_map_contains };
pub open spec fn rank(s: LState,t: int) -> int {
    if s.txns[t].outgoing { start(s.history,t) } else { position(s.history,Event { txn: t,op: Op::Commit }) }
}
pub proof fn bounds(s: LState,t: int)
    requires lifecycle::valid(s.history),committed(s.history).contains(t)
    ensures start(s.history,t) <= rank(s,t) <= position(s.history,Event { txn: t,op: Op::Commit })
{
    order::endpoint(s.history,t);
}
pub proof fn before_rank(s: LState,t: int,w: int)
    requires lifecycle::valid(s.history),committed(s.history).contains(t),committed(s.history).contains(w),intervals::before(s.history,t,w)
    ensures rank(s,t) < rank(s,w)
{
    bounds(s,t); bounds(s,w);
}
pub proof fn overlap_rank(s: LState,c: Constants,t: int,w: int,k: int)
    requires lifecycle::valid(s.history),conflicts::safe(s,c),overlap::safe(s,c),c.txns.contains(t),c.txns.contains(w),
        committed(s.history).contains(t),committed(s.history).contains(w),overlap::edge(s,t,w,k)
    ensures rank(s,t) < rank(s,w)
{
    order::endpoint(s.history,t); order::endpoint(s.history,w); lifecycle::start_position(s.history,t);
    assert(s.txns[t].outgoing && s.txns[w].incoming); assert(!s.txns[w].outgoing);
    assert(start(s.history,t) != position(s.history,Event { txn: w,op: Op::Commit }));
}
pub proof fn dependency_rank(s: LState,c: Constants,t: int,w: int)
    requires support::inductive(s,c),lifecycle::valid(s.history),s.history.no_duplicates(),intervals::safe(s),conflicts::safe(s,c),overlap::safe(s,c),dependency(s.history,c,t,w)
    ensures rank(s,t) < rank(s,w)
{
    let h=s.history; let p=|e: Event| committed(h).contains(e.txn); let ch=h.filter(p);
    let tc=Event { txn: t,op: Op::Commit }; let wc=Event { txn: w,op: Op::Commit };
    let tb=Event { txn: t,op: Op::Begin }; let wb=Event { txn: w,op: Op::Begin };
    order::endpoint(h,t); order::endpoint(h,w); order::commit_member(h,t); order::commit_member(h,w);
    order::event_summary(h,position(h,tc)-1); order::event_summary(h,position(h,wc)-1);
    assert(c.txns.contains(t) && c.txns.contains(w));
    lifecycle::start_position(h,t); lifecycle::start_position(h,w); positions::found(h,tb); positions::found(h,wb);
    assert(h.contains(tb) && h.contains(wb));
    positions::filter_order(h,p,tc,wb); positions::filter_order(h,p,tb,wc);
    positions::filtered_keys(h,p,t,true); positions::filtered_keys(h,p,w,true);
    let k=choose |k: int| c.keys.contains(k) && {
        let aw=position(ch,Event { txn: t,op: Op::Write(k) }); let bw=position(ch,Event { txn: w,op: Op::Write(k) });
        aw != -1 && bw != -1 && aw < bw
        || aw != -1 && keys(ch,w,true).contains(k) && position(ch,tc) < position(ch,wb)
        || keys(h,t,true).contains(k) && bw != -1 && position(ch,tb) < position(ch,wc)
    };
    let tw=Event { txn: t,op: Op::Write(k) }; let ww=Event { txn: w,op: Op::Write(k) };
    positions::found(ch,tw); positions::found(ch,ww);
    if position(ch,tw) != -1 { ch.lemma_filter_len(p); h.lemma_filter_contains_rev(p,tw); }
    if position(ch,ww) != -1 { h.lemma_filter_contains_rev(p,ww); }
    if position(ch,tw) != -1 && position(ch,ww) != -1 && position(ch,tw) < position(ch,ww) {
        positions::filter_order(h,p,tw,ww); versions::write_order(s,t,w,k); before_rank(s,t,w);
    } else if position(ch,tw) != -1 && keys(ch,w,true).contains(k) && position(ch,tc) < position(ch,wb) {
        assert(intervals::before(h,t,w)); before_rank(s,t,w);
    } else {
        assert(keys(h,t,true).contains(k) && position(ch,ww) != -1 && position(ch,tb) < position(ch,wc));
        positions::found(h,ww); keys_math::member(h,w,false,k); assert(keys(h,w,false).contains(k)); order::disjoint(h);
        if intervals::before(h,t,w) { before_rank(s,t,w); }
        else { assert(overlap::edge(s,t,w,k)); overlap_rank(s,c,t,w,k); }
    }
}
pub proof fn increasing(s: LState,p: Seq<int>,n: int)
    requires 0 < n < p.len(),forall |i: int| 0 <= i < p.len()-1 ==> rank(s,#[trigger] p[i]) < rank(s,p[i+1])
    ensures rank(s,p[0]) < rank(s,p[n])
    decreases n
{
    assert(rank(s,p[n-1]) < rank(s,p[(n-1)+1])); if n > 1 { increasing(s,p,n-1); }
}
pub proof fn acyclic(s: LState,c: Constants)
    requires support::inductive(s,c),lifecycle::valid(s.history),s.history.no_duplicates(),intervals::safe(s),conflicts::safe(s,c),overlap::safe(s,c)
    ensures serializable(s,c)
{
    assert forall |p: Seq<int>| !#[trigger] cycle(s.history,c,p) by {
        if cycle(s.history,c,p) {
            assert forall |i: int| 0 <= i < p.len()-1 implies rank(s,#[trigger] p[i]) < rank(s,p[i+1]) by {
                assert(dependency(s.history,c,p[i],p[i+1])); dependency_rank(s,c,p[i],p[i+1]);
            }
            increasing(s,p,p.len() as int-1); assert(p[p.len() as int-1] == p[0]);
        }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires support::safety_spec(b,c),time >= 0
    ensures serializable(b[time],c)
{
    support::at(b,c,time); lifecycle::at(b,c,time); unique::at(b,c,time); intervals::at(b,c,time); conflicts::at(b,c,time); overlap_safety::at(b,c,time);
    acyclic(b[time],c);
}
pub proof fn benchmark_serializable(b: Behavior<LState>,c: Constants)
    requires support::safety_spec(b,c)
    ensures forall |time: int| time >= 0 ==> #[trigger] serializable(b[time],c)
{
    assert forall |time: int| time >= 0 implies #[trigger] serializable(b[time],c) by { at(b,c,time); }
}
} // verus!
