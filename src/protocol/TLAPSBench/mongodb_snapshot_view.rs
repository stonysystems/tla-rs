//! Active reads use the current timestamped snapshot, including prepared commits that finish late.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
use super::mongodb_maximum as maxima;
use super::mongodb_storage_lifecycle as lifecycle;
use super::mongodb_storage_contents as contents;
use super::mongodb_snapshot_values as values;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn refresh(n: LShard,c: Constants,t: int,k: int) -> bool {
    exists |other: int,p: int,m: int| #![trigger c.txns.contains(other), n.log[p], n.log[m]] c.txns.contains(other) && other != t && 0 <= p < n.log.len() && 0 <= m < n.log.len()
        && n.log[p].prepare && n.log[p].txn == other && !n.log[m].prepare && n.log[m].txn == other && n.log[m].ts <= n.txns[t].snapshot.ts
        && n.log[m].data.dom().contains(k) && !n.txns[t].snapshot.writes.contains(k)
}
pub open spec fn view(n: LShard,c: Constants,t: int,k: int) -> bool {
    n.txns[t].snapshot.active && c.keys.contains(k) && !n.txns[t].snapshot.writes.contains(k) && !refresh(n,c,t,k)
        ==> n.txns[t].snapshot.data[k] == snapshot_read(n,c,k,n.txns[t].snapshot.ts)
}
pub open spec fn safe(s: LState,c: Constants) -> bool {
    forall |i: int,t: int,k: int| c.shards.contains(i) && c.txns.contains(t) ==> #[trigger] view(s.shards[i],c,t,k)
}
pub proof fn log_prefix(s: LState,c: Constants,a: Action,i: int)
    requires support::shape(s,c),enabled(s,c,a),c.shards.contains(i)
    ensures s.shards[i].log.is_prefix_of(apply(s,c,a).shards[i].log)
{
    reveal(apply);
}
pub proof fn refresh_retained(n: LShard,d: LShard,c: Constants,t: int,k: int)
    requires n.log.is_prefix_of(d.log),n.txns[t].snapshot.ts == d.txns[t].snapshot.ts,!d.txns[t].snapshot.writes.contains(k),refresh(n,c,t,k)
    ensures refresh(d,c,t,k)
{
    let (other,p,m)=choose |other: int,p: int,m: int| #![trigger c.txns.contains(other), n.log[p], n.log[m]] c.txns.contains(other) && other != t && 0 <= p < n.log.len() && 0 <= m < n.log.len()
        && n.log[p].prepare && n.log[p].txn == other && !n.log[m].prepare && n.log[m].txn == other && n.log[m].ts <= n.txns[t].snapshot.ts
        && n.log[m].data.dom().contains(k) && !n.txns[t].snapshot.writes.contains(k);
    assert(d.log[p] == n.log[p]); assert(d.log[m] == n.log[m]);
}
pub proof fn late_commit(s: LState,c: Constants,m: Commit,t: int,k: int)
    requires support::shape(s,c),lifecycle::safe(s,c),enabled(s,c,Action::Commit(m)),c.txns.contains(t),t != m.txn,
        s.shards[m.shard].txns[t].snapshot.active,!s.shards[m.shard].txns[t].snapshot.writes.contains(k)
    ensures {
        let u=apply(s,c,Action::Commit(m)); let d=u.shards[m.shard];
        values::eligible(d.log.last(),k,d.txns[t].snapshot.ts) ==> refresh(d,c,t,k)
    },
{
    reveal(enabled); reveal(apply); let n=s.shards[m.shard]; let u=apply(s,c,Action::Commit(m)); let d=u.shards[m.shard];
    if values::eligible(d.log.last(),k,d.txns[t].snapshot.ts) {
        if m.ts == c.no_value {
            maxima::next_above(s,c,m.shard,m.txn); maxima::active_member(n,c,t); assert(log_ts(n).union(active_read_ts(n,c)).contains(n.txns[t].snapshot.ts)); assert(false);
        } else {
            assert(lifecycle::row(s,c,m.shard)); assert(lifecycle::node(n,m.txn));
            let p=choose |p: int| 0 <= p < n.log.len() && (#[trigger] n.log[p]).txn == m.txn && n.log[p].prepare;
            let at=n.log.len() as int; assert(d.log[p] == n.log[p]); assert(d.log[at] == d.log.last());
        }
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::shape(s,c),lifecycle::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a); reveal(enabled); reveal(apply);
    assert forall |i: int,t: int,k: int| c.shards.contains(i) && c.txns.contains(t) implies #[trigger] view(u.shards[i],c,t,k) by {
        let n=s.shards[i]; let d=u.shards[i]; assert(view(n,c,t,k)); log_prefix(s,c,a,i);
        if d.txns[t].snapshot.active && c.keys.contains(k) && !d.txns[t].snapshot.writes.contains(k) && !refresh(d,c,t,k) {
            if a == Action::Start(i,t) { values::same_log(n,d,c,k,d.txns[t].snapshot.ts); }
            else {
                assert(n.txns[t].snapshot.active); assert(d.txns[t].snapshot.ts == n.txns[t].snapshot.ts); assert(!n.txns[t].snapshot.writes.contains(k));
                if refresh(n,c,t,k) { refresh_retained(n,d,c,t,k); assert(false); }
                assert(d.txns[t].snapshot.data[k] == n.txns[t].snapshot.data[k]);
                if d.log == n.log { values::same_log(n,d,c,k,n.txns[t].snapshot.ts); }
                else {
                    let e=d.log.last(); assert(d.log == n.log.push(e));
                    if let Action::Commit(m)=a { assert(m.shard == i && m.txn != t); late_commit(s,c,m,t,k); }
                    assert(!values::eligible(e,k,n.txns[t].snapshot.ts)); values::append_ignored(n,d,c,k,n.txns[t].snapshot.ts,e);
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
    if time > 0 {
        at(b,c,time-1); support::at(b,c,time-1); lifecycle::at(b,c,time-1); let a=support::step(b,c,time-1); preserve(b[time-1],c,a);
    }
}
pub proof fn read_current(s: LState,c: Constants,i: int,t: int,k: int)
    requires contents::safe(s,c),safe(s,c),c.shards.contains(i),c.txns.contains(t),c.keys.contains(k),s.shards[i].txns[t].snapshot.active
    ensures txn_read(s.shards[i],c,t,k) == if s.shards[i].txns[t].snapshot.writes.contains(k) { t } else { snapshot_read(s.shards[i],c,k,s.shards[i].txns[t].snapshot.ts) }
{
    let n=s.shards[i]; assert(contents::node(s,c,i,t)); assert(view(n,c,t,k));
    if n.txns[t].snapshot.writes.contains(k) { assert(!refresh(n,c,t,k)); assert(n.txns[t].snapshot.data[k] == t); }
}
} // verus!
