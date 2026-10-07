//! Overlapping read/write accesses require the two corresponding conflict flags.
use vstd::prelude::*;
use super::cahill::*;
use super::cahill_keys as keys_math;
use super::cahill_lifecycle as lifecycle;
use super::cahill_history_order as order;
use super::cahill_flags as flags;
use super::cahill_writer_intervals as intervals;
verus! {
broadcast use { vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn separated(h: Seq<Event>,t: int,w: int) -> bool {
    committed(h).contains(t) && intervals::before(h,t,w) || committed(h).contains(w) && intervals::before(h,w,t)
}
pub open spec fn edge(s: LState,t: int,w: int,k: int) -> bool {
    t != w && keys(s.history,t,true).contains(k) && keys(s.history,w,false).contains(k)
    && !aborted(s.history).contains(t) && !aborted(s.history).contains(w) && !separated(s.history,t,w)
}
pub open spec fn safe(s: LState,c: Constants) -> bool {
    forall |t: int,w: int,k: int| c.txns.contains(t) && c.txns.contains(w) && #[trigger] edge(s,t,w,k) ==> s.txns[t].outgoing && s.txns[w].incoming
}
pub proof fn old_overlap(h: Seq<Event>,d: Seq<Event>,t: int,w: int)
    requires lifecycle::valid(d),h.is_prefix_of(d),all(h).contains(t),all(h).contains(w),!separated(d,t,w)
    ensures !separated(h,t,w)
{
    order::prefix(h,d); order::start_prefix(h,d,t); order::start_prefix(h,d,w);
    if committed(h).contains(t) { order::commit_prefix(h,d,t); }
    if committed(h).contains(w) { order::commit_prefix(h,d,w); }
}
pub proof fn inherited(s: LState,u: LState,c: Constants,t: int,w: int,k: int)
    requires lifecycle::valid(u.history),s.history.is_prefix_of(u.history),safe(s,c),flags::retained(s,u,c),c.txns.contains(t),c.txns.contains(w),
        edge(u,t,w,k),keys(s.history,t,true).contains(k),keys(s.history,w,false).contains(k)
    ensures u.txns[t].outgoing,u.txns[w].incoming
{
    keys_math::member_all(s.history,t,true,k); keys_math::member_all(s.history,w,false,k); order::prefix(s.history,u.history);
    old_overlap(s.history,u.history,t,w); assert(edge(s,t,w,k));
    assert(flags::node(s,u,t)); assert(flags::node(s,u,w));
}
pub open spec fn same_keys(s: LState,u: LState,t: int) -> bool {
    keys(u.history,t,true) == keys(s.history,t,true) && keys(u.history,t,false) == keys(s.history,t,false)
}
pub proof fn unchanged(s: LState,u: LState,c: Constants)
    requires lifecycle::valid(u.history),s.history.is_prefix_of(u.history),safe(s,c),flags::retained(s,u,c),
        forall |t: int| c.txns.contains(t) ==> #[trigger] same_keys(s,u,t)
    ensures safe(u,c)
{
    assert forall |t: int,w: int,k: int| c.txns.contains(t) && c.txns.contains(w) && #[trigger] edge(u,t,w,k) implies u.txns[t].outgoing && u.txns[w].incoming by {
        assert(same_keys(s,u,t)); assert(same_keys(s,u,w));
        inherited(s,u,c,t,w,k);
    }
}
} // verus!
