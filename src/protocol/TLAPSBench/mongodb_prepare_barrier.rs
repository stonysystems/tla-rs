//! Prepared writers stay after every earlier successful reader's snapshot timestamp.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
use super::mongodb_maximum as maxima;
use super::mongodb_storage_lifecycle as lifecycle;
use super::mongodb_storage_contents as contents;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn read_key(ops: Seq<Operation>,k: int) -> bool { exists |p: int| 0 <= p < ops.len() && (#[trigger] ops[p]).kind == Kind::Read && ops[p].key == k }
pub proof fn append(ops: Seq<Operation>,o: Operation,k: int)
    ensures read_key(ops.push(o),k) <==> read_key(ops,k) || o.kind == Kind::Read && o.key == k
{
    if read_key(ops.push(o),k) {
        let p=choose |p: int| 0 <= p < ops.push(o).len() && (#[trigger] ops.push(o)[p]).kind == Kind::Read && ops.push(o)[p].key == k;
        if p < ops.len() { assert(ops.push(o)[p] == ops[p]); }
    }
    if read_key(ops,k) {
        let p=choose |p: int| 0 <= p < ops.len() && (#[trigger] ops[p]).kind == Kind::Read && ops[p].key == k;
        assert(ops.push(o)[p] == ops[p]);
    }
    assert(ops.push(o)[ops.len() as int] == o);
}
pub open spec fn node(n: LShard,c: Constants,r: int) -> bool {
    forall |w: int,k: int| c.txns.contains(w) && r != w && (n.txns[r].snapshot.active || n.txns[r].snapshot.committed)
        && #[trigger] read_key(n.txns[r].ops,k) && n.txns[w].snapshot.active && n.txns[w].snapshot.prepared && #[trigger] n.txns[w].snapshot.writes.contains(k)
        ==> n.txns[w].snapshot.prepare_ts > n.txns[r].snapshot.ts
}
pub open spec fn safe(s: LState,c: Constants) -> bool { forall |i: int,r: int| c.shards.contains(i) && c.txns.contains(r) ==> #[trigger] node(s.shards[i],c,r) }
pub proof fn prepare_after_reader(s: LState,c: Constants,m: Prepare,r: int)
    requires support::shape(s,c),lifecycle::safe(s,c),enabled(s,c,Action::Prepare(m)),c.txns.contains(r),
        s.shards[m.shard].txns[r].snapshot.active || s.shards[m.shard].txns[r].snapshot.committed
    ensures next_ts(s.shards[m.shard],c) > s.shards[m.shard].txns[r].snapshot.ts
{
    reveal(enabled); let n=s.shards[m.shard]; maxima::next_above(s,c,m.shard,m.txn); let q=log_ts(n).union(active_read_ts(n,c));
    if n.txns[r].snapshot.active {
        maxima::active_member(n,c,r); assert(q.contains(n.txns[r].snapshot.ts));
    } else {
        assert(lifecycle::row(s,c,m.shard)); assert(lifecycle::node(n,r));
        let p=choose |p: int| 0 <= p < n.log.len() && (#[trigger] n.log[p]).txn == r && !n.log[p].prepare;
        maxima::log_member(n,p); assert(q.contains(n.log[p].ts)); assert(n.log[p].ts > n.txns[r].snapshot.ts);
    }
}
pub proof fn read_checked(s: LState,c: Constants,i: int,r: int,k: int,w: int)
    requires enabled(s,c,Action::Read(i,r,k)),c.txns.contains(w),w != r,s.shards[i].txns[w].snapshot.active,s.shards[i].txns[w].snapshot.prepared,s.shards[i].txns[w].snapshot.writes.contains(k)
    ensures s.shards[i].txns[w].snapshot.prepare_ts > s.shards[i].txns[r].snapshot.ts
{
    reveal(enabled); if s.shards[i].txns[w].snapshot.prepare_ts <= s.shards[i].txns[r].snapshot.ts { assert(prepare_conflict(s.shards[i],c,r,k)); }
}
pub proof fn initial_safe(c: Constants,catalog: IMap<int,int>)
    ensures safe(initial(c,catalog),c)
{
    let s=initial(c,catalog); assert forall |i: int,r: int| c.shards.contains(i) && c.txns.contains(r) implies #[trigger] node(s.shards[i],c,r) by {}
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::shape(s,c),lifecycle::safe(s,c),contents::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a); reveal(enabled); reveal(apply);
    assert forall |i: int,r: int| c.shards.contains(i) && c.txns.contains(r) implies #[trigger] node(u.shards[i],c,r) by {
        let n=s.shards[i]; let d=u.shards[i]; assert(node(n,c,r)); assert(lifecycle::row(s,c,i)); assert(lifecycle::node(n,r)); assert(contents::node(s,c,i,r));
        assert forall |w: int,k: int| c.txns.contains(w) && r != w && (d.txns[r].snapshot.active || d.txns[r].snapshot.committed)
            && #[trigger] read_key(d.txns[r].ops,k) && d.txns[w].snapshot.active && d.txns[w].snapshot.prepared && #[trigger] d.txns[w].snapshot.writes.contains(k)
            implies d.txns[w].snapshot.prepare_ts > d.txns[r].snapshot.ts by {
            match a {
                Action::Start(j,t) => { if i == j && r == t { assert(!lifecycle::recorded(n.log,r,true)); assert(!super::mongodb_read_time::started(n.txns[r])); assert(n.txns[r].ops.len() == 0); assert(false); } },
                Action::Read(j,t,key) => { if i == j && r == t { append(n.txns[r].ops,Operation { kind: Kind::Read,key,value: txn_read(n,c,r,key) },k); } },
                Action::Write(j,t,key) => { if i == j && r == t { append(n.txns[r].ops,Operation { kind: Kind::Write,key,value: r },k); } },
                _ => {},
            }
            assert(n.txns[r].snapshot.active || n.txns[r].snapshot.committed); lifecycle::timestamp_fixed(s,c,a,i,r);
            if a == Action::Read(i,r,k) { read_checked(s,c,i,r,k,w); }
            else {
                assert(read_key(n.txns[r].ops,k));
                if let Action::Prepare(m)=a {
                    if m.shard == i && m.txn == w { prepare_after_reader(s,c,m,r); }
                    else { assert(n.txns[w].snapshot.active && n.txns[w].snapshot.prepared && n.txns[w].snapshot.writes.contains(k)); }
                } else { assert(n.txns[w].snapshot.active && n.txns[w].snapshot.prepared && n.txns[w].snapshot.writes.contains(k)); }
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
