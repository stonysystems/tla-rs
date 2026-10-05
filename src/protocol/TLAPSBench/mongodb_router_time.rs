//! A transaction's selected router and read timestamp cannot change after selection.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn selected(s: LState,c: Constants,r: int,t: int) -> bool {
    c.routers.contains(r) && c.txns.contains(t) && s.routers[r][t].read_ts != c.no_value
}
pub open spec fn owns(s: LState,c: Constants,t: int,ts: int) -> bool {
    exists |r: int| #[trigger] selected(s,c,r,t) && s.routers[r][t].read_ts == ts
}
pub open spec fn unique(s: LState,c: Constants,t: int) -> bool {
    forall |r: int,q: int| #[trigger] selected(s,c,r,t) && #[trigger] selected(s,c,q,t) ==> r == q
}
pub open spec fn router(s: LState,c: Constants,r: int,t: int) -> bool {
    let x=s.routers[r][t];
    (x.read_ts == c.no_value || c.timestamps.contains(x.read_ts))
    && (x.count > 0 || x.participants.len() > 0 || x.committing ==> selected(s,c,r,t))
}
pub open spec fn safe(s: LState,c: Constants) -> bool {
    (forall |t: int| c.txns.contains(t) ==> #[trigger] unique(s,c,t))
    && forall |r: int,t: int| c.routers.contains(r) && c.txns.contains(t) ==> #[trigger] router(s,c,r,t)
}
pub proof fn selected_retained(s: LState,c: Constants,a: Action,r: int,t: int)
    requires support::shape(s,c),enabled(s,c,a),selected(s,c,r,t)
    ensures selected(apply(s,c,a),c,r,t),apply(s,c,a).routers[r][t].read_ts == s.routers[r][t].read_ts
{
    reveal(enabled); reveal(apply);
    if let Action::RouterStart { r: ar,t: at,ts }=a { if at == t { assert(s.routers[r][t].read_ts == c.no_value); assert(false); } }
}
pub proof fn owns_retained(s: LState,c: Constants,a: Action,t: int,ts: int)
    requires support::shape(s,c),enabled(s,c,a),owns(s,c,t,ts)
    ensures owns(apply(s,c,a),c,t,ts)
{
    let r=choose |r: int| #[trigger] selected(s,c,r,t) && s.routers[r][t].read_ts == ts;
    selected_retained(s,c,a,r,t);
}
pub proof fn valid_time(s: LState,c: Constants,t: int,ts: int)
    requires safe(s,c),owns(s,c,t,ts)
    ensures c.txns.contains(t),c.timestamps.contains(ts),ts != c.no_value
{
    let r=choose |r: int| #[trigger] selected(s,c,r,t) && s.routers[r][t].read_ts == ts;
    assert(router(s,c,r,t));
}
pub proof fn same_time(s: LState,c: Constants,t: int,a: int,d: int)
    requires safe(s,c),owns(s,c,t,a),owns(s,c,t,d)
    ensures a == d
{
    let r=choose |r: int| #[trigger] selected(s,c,r,t) && s.routers[r][t].read_ts == a;
    let q=choose |q: int| #[trigger] selected(s,c,q,t) && s.routers[q][t].read_ts == d;
    assert(unique(s,c,t)); assert(r == q);
}
pub proof fn initial_safe(c: Constants,catalog: IMap<int,int>)
    ensures safe(initial(c,catalog),c)
{
    let s=initial(c,catalog);
    assert forall |t: int| c.txns.contains(t) implies #[trigger] unique(s,c,t) by {}
    assert forall |r: int,t: int| c.routers.contains(r) && c.txns.contains(t) implies #[trigger] router(s,c,r,t) by {}
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::shape(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    reveal(enabled); reveal(apply); let u=apply(s,c,a);
    assert forall |r: int,t: int| c.routers.contains(r) && c.txns.contains(t) implies #[trigger] router(u,c,r,t) by {
        assert(router(s,c,r,t));
        if let Action::RouterStart { r: ar,t: at,ts }=a {
            if at == t && ar == r { assert(s.routers[r][t].read_ts == c.no_value); }
        }
    }
    assert forall |t: int| c.txns.contains(t) implies #[trigger] unique(u,c,t) by {
        assert(unique(s,c,t));
        assert forall |r: int,q: int| #[trigger] selected(u,c,r,t) && #[trigger] selected(u,c,q,t) implies r == q by {
            if let Action::RouterStart { r: ar,t: at,ts }=a {
                if at == t { assert(s.routers[r][t].read_ts == c.no_value); assert(s.routers[q][t].read_ts == c.no_value); }
            }
            if selected(s,c,r,t) && selected(s,c,q,t) { assert(r == q); }
        }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires support::safety_spec(b,c),time >= 0
    ensures safe(b[time],c)
    decreases time
{
    if time == 0 { initial_safe(c,b[0].catalog); }
    else { at(b,c,time-1); support::at(b,c,time-1); let a=support::step(b,c,time-1); preserve(b[time-1],c,a); }
}
} // verus!
