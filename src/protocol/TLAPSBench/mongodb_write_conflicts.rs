//! Active writers are exclusive and no committed write can enter their snapshot interval.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
use super::mongodb_storage_lifecycle as lifecycle;
use super::mongodb_storage_contents as contents;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn exclusive(n: LShard,c: Constants) -> bool {
    forall |t: int,w: int,k: int| c.txns.contains(t) && c.txns.contains(w)
        && n.txns[t].snapshot.active && n.txns[w].snapshot.active
        && #[trigger] n.txns[t].snapshot.writes.contains(k) && #[trigger] n.txns[w].snapshot.writes.contains(k) ==> t == w
}
pub open spec fn clear(n: LShard,t: int,k: int) -> bool {
    forall |p: int| 0 <= p < n.log.len() && !(#[trigger] n.log[p]).prepare && n.log[p].data.dom().contains(k) ==> n.log[p].ts <= n.txns[t].snapshot.ts
}
pub open spec fn row(s: LState,c: Constants,i: int) -> bool {
    let n=s.shards[i]; exclusive(n,c)
    && forall |t: int,k: int| c.txns.contains(t) && n.txns[t].snapshot.active && n.txns[t].snapshot.writes.contains(k) ==> #[trigger] clear(n,t,k)
}
pub open spec fn safe(s: LState,c: Constants) -> bool { forall |i: int| c.shards.contains(i) ==> #[trigger] row(s,c,i) }
pub proof fn checked(s: LState,c: Constants,i: int,t: int,k: int)
    requires support::shape(s,c),lifecycle::safe(s,c),c.shards.contains(i),c.txns.contains(t),s.shards[i].txns[t].snapshot.active,!write_conflict(s.shards[i],c,t,k)
    ensures clear(s.shards[i],t,k),forall |w: int| #![trigger c.txns.contains(w)] c.txns.contains(w) && s.shards[i].txns[w].snapshot.active && s.shards[i].txns[w].snapshot.writes.contains(k) ==> w == t
{
    let n=s.shards[i]; assert(lifecycle::row(s,c,i)); assert(lifecycle::node(n,t));
    assert forall |p: int| 0 <= p < n.log.len() && !(#[trigger] n.log[p]).prepare && n.log[p].data.dom().contains(k) implies n.log[p].ts <= n.txns[t].snapshot.ts by {
        let w=n.log[p].txn; assert(c.txns.contains(w));
        if w == t { assert(lifecycle::recorded(n.log,t,false)); assert(false); }
        if n.log[p].ts > n.txns[t].snapshot.ts {
            assert(exists |i: int| 0 <= i < n.log.len() && !(#[trigger] n.log[i]).prepare && n.log[i].ts > n.txns[t].snapshot.ts && n.log[i].data.dom().contains(k));
            assert(write_conflict(n,c,t,k)); assert(false);
        }
    }
    assert forall |w: int| #![trigger c.txns.contains(w)] c.txns.contains(w) && n.txns[w].snapshot.active && n.txns[w].snapshot.writes.contains(k) implies w == t by {
        if w != t { assert(write_conflict(n,c,t,k)); }
    }
}
pub proof fn initial_safe(c: Constants,catalog: IMap<int,int>)
    ensures safe(initial(c,catalog),c)
{
    let s=initial(c,catalog);
    assert forall |i: int| c.shards.contains(i) implies #[trigger] row(s,c,i) by {}
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::shape(s,c),lifecycle::safe(s,c),contents::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a); reveal(enabled); reveal(apply);
    if let Action::Write(i,t,k)=a { if !write_conflict(s.shards[i],c,t,k) { checked(s,c,i,t,k); } }
    assert forall |i: int| c.shards.contains(i) implies #[trigger] row(u,c,i) by {
        let n=s.shards[i]; let d=u.shards[i]; assert(row(s,c,i));
        assert(exclusive(d,c)) by {
            assert forall |t: int,w: int,k: int| c.txns.contains(t) && c.txns.contains(w) && d.txns[t].snapshot.active && d.txns[w].snapshot.active
                && #[trigger] d.txns[t].snapshot.writes.contains(k) && #[trigger] d.txns[w].snapshot.writes.contains(k) implies t == w by {
                if n.txns[t].snapshot.writes.contains(k) && n.txns[w].snapshot.writes.contains(k) { assert(t == w); }
            }
        }
        assert forall |t: int,k: int| c.txns.contains(t) && d.txns[t].snapshot.active && d.txns[t].snapshot.writes.contains(k) implies #[trigger] clear(d,t,k) by {
            if n.txns[t].snapshot.writes.contains(k) { assert(clear(n,t,k)); }
            else { assert(clear(n,t,k)); }
            assert(n.txns[t].snapshot.active); assert(d.txns[t].snapshot.ts == n.txns[t].snapshot.ts);
            assert forall |p: int| 0 <= p < d.log.len() && !(#[trigger] d.log[p]).prepare && d.log[p].data.dom().contains(k) implies d.log[p].ts <= d.txns[t].snapshot.ts by {
                if p < n.log.len() { assert(d.log[p] == n.log[p]); }
                else {
                    if let Action::Commit(m)=a {
                        assert(i == m.shard); assert(contents::node(s,c,i,m.txn)); assert(n.txns[m.txn].snapshot.writes.contains(k));
                        assert(n.txns[t].snapshot.writes.contains(k)); assert(t == m.txn); assert(false);
                    }
                }
            }
        }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires support::safety_spec(b,c),time >= 0
    ensures safe(b[time],c)
    decreases time
{
    if time == 0 { initial_safe(c,b[0].catalog); }
    else {
        at(b,c,time-1); support::at(b,c,time-1); lifecycle::at(b,c,time-1); contents::at(b,c,time-1);
        let a=support::step(b,c,time-1); preserve(b[time-1],c,a);
    }
}
} // verus!
