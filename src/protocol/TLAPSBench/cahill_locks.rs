//! Exclusive lock ownership and the identity selected by the deadlock owner function.
use vstd::prelude::*;
use super::cahill::*;
use super::cahill_support as support;
use super::temporal::Behavior;
verus! {
pub open spec fn exclusive(s: LState,c: Constants) -> bool {
    forall |t: int,u: int,k: int| c.txns.contains(t) && c.txns.contains(u) && #[trigger] s.txns[t].xlocks.contains(k) && #[trigger] s.txns[u].xlocks.contains(k) ==> t == u
}
pub open spec fn retains(s: LState,u: LState,c: Constants) -> bool {
    forall |t: int| c.txns.contains(t) ==> #[trigger] u.txns[t].xlocks.subset_of(s.txns[t].xlocks)
}
pub proof fn retain(s: LState,u: LState,c: Constants)
    requires exclusive(s,c),retains(s,u,c)
    ensures exclusive(u,c)
{
    assert forall |t: int,v: int,k: int| c.txns.contains(t) && c.txns.contains(v) && #[trigger] u.txns[t].xlocks.contains(k) && #[trigger] u.txns[v].xlocks.contains(k) implies t == v by {
        assert(u.txns[t].xlocks.subset_of(s.txns[t].xlocks)); assert(u.txns[v].xlocks.subset_of(s.txns[v].xlocks));
    }
}
pub proof fn acquire_exclusive(s: LState,c: Constants,t: int,k: int)
    requires exclusive(s,c),!locked(s,c,k)
    ensures exclusive(acquire(s,c,t,k),c)
{
    reveal(acquire); let u=acquire(s,c,t,k);
    assert forall |i: int,j: int,key: int| c.txns.contains(i) && c.txns.contains(j) && #[trigger] u.txns[i].xlocks.contains(key) && #[trigger] u.txns[j].xlocks.contains(key) implies i == j by {
        assert(!s.txns[i].xlocks.contains(k)); assert(!s.txns[j].xlocks.contains(k));
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires exclusive(s,c),enabled(s,c,a)
    ensures exclusive(apply(s,c,a),c)
{
    reveal(enabled); reveal(apply); reveal(commit); reveal(read);
    match a {
        Action::Finish(t) => { acquire_exclusive(s,c,t,s.txns[t].waiting.unwrap()); },
        Action::Write { txn: t,key: k,victim: v } => {
            if writers_since(s,t,k).is_empty() && !locked(s,c,k) { acquire_exclusive(s,c,t,k); }
            else { let u=apply(s,c,a); assert(retains(s,u,c)); retain(s,u,c); }
        },
        _ => { let u=apply(s,c,a); assert(retains(s,u,c)); retain(s,u,c); },
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires support::safety_spec(b,c),time >= 0
    ensures exclusive(b[time],c)
    decreases time
{
    if time > 0 { at(b,c,time-1); let a=support::step(b,c,time-1); preserve(b[time-1],c,a); }
}
pub proof fn owner_correct(s: LState,c: Constants,k: int,t: int)
    requires support::inductive(s,c),exclusive(s,c),c.txns.contains(t),s.txns[t].xlocks.contains(k)
    ensures owner(s,k) == Some(t),active(s.history).contains(t)
{
    assert(support::node(s,c,t)); let q=active(s.history).filter(|r: int| s.txns[r].xlocks.contains(k)); assert(q.contains(t));
    assert(q =~= set![t]) by { assert forall |r: int| q.contains(r) implies r == t by { assert(c.txns.contains(r)); } }
    let r=choose |r: int| q.contains(r); assert(r == t);
}
pub proof fn owner_exists(s: LState,c: Constants,k: int)
    requires support::inductive(s,c),locked(s,c,k)
    ensures owner(s,k) is Some
{
    let t=choose |t: int| #![trigger c.txns.contains(t)] c.txns.contains(t) && s.txns[t].xlocks.contains(k); assert(support::node(s,c,t));
    assert(active(s.history).filter(|r: int| s.txns[r].xlocks.contains(k)).contains(t));
}
} // verus!
