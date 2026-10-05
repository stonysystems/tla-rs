//! Successive committed writers of a key are ordered before the next writer's snapshot.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
use super::mongodb_storage_lifecycle as lifecycle;
use super::mongodb_storage_contents as contents;
use super::mongodb_write_conflicts as conflicts;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn prior(n: LShard,q: int) -> bool {
    forall |p: int,k: int| 0 <= p < q && !n.log[p].prepare && #[trigger] n.log[p].data.dom().contains(k) && n.log[q].data.dom().contains(k)
        ==> n.log[p].ts <= n.txns[n.log[q].txn].snapshot.ts
}
pub open spec fn safe(s: LState,c: Constants) -> bool {
    forall |i: int,q: int| c.shards.contains(i) && 0 <= q < s.shards[i].log.len() && !s.shards[i].log[q].prepare ==> #[trigger] prior(s.shards[i],q)
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::shape(s,c),lifecycle::safe(s,c),contents::safe(s,c),conflicts::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a); reveal(enabled); reveal(apply);
    assert forall |i: int,q: int| c.shards.contains(i) && 0 <= q < u.shards[i].log.len() && !u.shards[i].log[q].prepare implies #[trigger] prior(u.shards[i],q) by {
        let n=s.shards[i]; let d=u.shards[i]; let t=d.log[q].txn; assert(lifecycle::row(s,c,i)); assert(conflicts::row(s,c,i));
        if q < n.log.len() {
            assert(d.log[q] == n.log[q]); assert(prior(n,q)); assert(c.txns.contains(t)); assert(lifecycle::node(n,t));
            assert(lifecycle::recorded(n.log,t,false)); lifecycle::committed_fixed(s,c,a,i,t);
        }
        assert forall |p: int,k: int| 0 <= p < q && !d.log[p].prepare && #[trigger] d.log[p].data.dom().contains(k) && d.log[q].data.dom().contains(k)
            implies d.log[p].ts <= d.txns[d.log[q].txn].snapshot.ts by {
            assert(p < n.log.len()); assert(d.log[p] == n.log[p]);
            if q == n.log.len() {
                assert(contents::node(s,c,i,t)); assert(n.txns[t].snapshot.writes.contains(k)); assert(n.txns[t].snapshot.active);
                assert(conflicts::clear(n,t,k));
            }
        }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires support::safety_spec(b,c),time >= 0
    ensures safe(b[time],c)
    decreases time
{
    if time > 0 {
        at(b,c,time-1); support::at(b,c,time-1); lifecycle::at(b,c,time-1); contents::at(b,c,time-1); conflicts::at(b,c,time-1);
        let a=support::step(b,c,time-1); preserve(b[time-1],c,a);
    }
}
pub proof fn increasing(s: LState,c: Constants,i: int,p: int,q: int,k: int)
    requires lifecycle::safe(s,c),safe(s,c),c.shards.contains(i),0 <= p < q < s.shards[i].log.len(),
        !s.shards[i].log[p].prepare,!s.shards[i].log[q].prepare,s.shards[i].log[p].data.dom().contains(k),s.shards[i].log[q].data.dom().contains(k)
    ensures s.shards[i].log[p].ts <= s.shards[i].txns[s.shards[i].log[q].txn].snapshot.ts < s.shards[i].log[q].ts
{
    let n=s.shards[i]; assert(prior(n,q)); assert(lifecycle::row(s,c,i)); assert(lifecycle::node(n,n.log[q].txn));
}
} // verus!
