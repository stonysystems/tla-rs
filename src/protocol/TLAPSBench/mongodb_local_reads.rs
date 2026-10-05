//! Every retained local read agrees with its timestamped snapshot and preceding local writes.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
use super::mongodb_storage_lifecycle as lifecycle;
use super::mongodb_storage_contents as contents;
use super::mongodb_prepare_barrier as barrier;
use super::mongodb_snapshot_view as view;
use super::mongodb_snapshot_values as values;
use super::mongodb_read_stability as stability;
use super::mongodb_operations as operations;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn node(n: LShard,c: Constants,t: int) -> bool {
    let x=n.txns[t]; (x.snapshot.active || x.snapshot.committed) ==>
    forall |p: int| 0 <= p < x.ops.len() && (#[trigger] x.ops[p]).kind == Kind::Read ==> x.ops[p].value ==
        if write_keys(x.ops.take(p)).contains(x.ops[p].key) { t } else { snapshot_read(n,c,x.ops[p].key,x.snapshot.ts) }
}
pub open spec fn safe(s: LState,c: Constants) -> bool { forall |i: int,t: int| c.shards.contains(i) && c.txns.contains(t) ==> #[trigger] node(s.shards[i],c,t) }
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::shape(s,c),lifecycle::safe(s,c),contents::safe(s,c),barrier::safe(s,c),view::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a); reveal(enabled); reveal(apply);
    assert forall |i: int,t: int| c.shards.contains(i) && c.txns.contains(t) implies #[trigger] node(u.shards[i],c,t) by {
        let n=s.shards[i]; let d=u.shards[i]; let old=n.txns[t]; let x=d.txns[t];
        assert(node(n,c,t)); assert(contents::node(s,c,i,t)); assert(lifecycle::row(s,c,i)); assert(lifecycle::node(n,t));
        if x.snapshot.active || x.snapshot.committed {
            assert forall |p: int| 0 <= p < x.ops.len() && (#[trigger] x.ops[p]).kind == Kind::Read implies x.ops[p].value ==
                if write_keys(x.ops.take(p)).contains(x.ops[p].key) { t } else { snapshot_read(d,c,x.ops[p].key,x.snapshot.ts) } by {
                let k=x.ops[p].key;
                if p < old.ops.len() {
                    assert(x.ops[p] == old.ops[p]); assert(x.ops.take(p) =~= old.ops.take(p));
                    if a == Action::Start(i,t) {
                        assert(!lifecycle::recorded(n.log,t,true)); assert(!super::mongodb_read_time::started(old)); assert(old.ops.len() == 0); assert(false);
                    }
                    assert(old.snapshot.active || old.snapshot.committed); assert(barrier::read_key(old.ops,k)); stability::past_read(s,c,a,i,t,k);
                } else {
                    assert(a == Action::Read(i,t,k)); assert(p == old.ops.len()); assert(x.ops.take(p) =~= old.ops);
                    view::read_current(s,c,i,t,k); assert(!old.snapshot.aborted); assert(old.snapshot.writes == write_keys(old.ops));
                    values::same_log(n,d,c,k,old.snapshot.ts);
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
        at(b,c,time-1); support::at(b,c,time-1); lifecycle::at(b,c,time-1); contents::at(b,c,time-1); barrier::at(b,c,time-1); view::at(b,c,time-1);
        let a=support::step(b,c,time-1); preserve(b[time-1],c,a);
    }
}
pub open spec fn snapshot(n: LShard,c: Constants,t: int) -> IMap<int,int> {
    IMap::new(|k: int| c.keys.contains(k),|k: int| snapshot_read(n,c,k,n.txns[t].snapshot.ts))
}
pub proof fn complete_local(b: Behavior<LState>,c: Constants,time: int,i: int,t: int)
    requires support::safety_spec(b,c),time >= 0,c.shards.contains(i),c.txns.contains(t),b[time].shards[i].txns[t].snapshot.committed
    ensures complete(snapshot(b[time].shards[i],c,t),b[time].shards[i].txns[t].ops)
{
    at(b,c,time); contents::at(b,c,time); let s=b[time]; let n=s.shards[i]; let ops=n.txns[t].ops; let base=snapshot(n,c,t);
    assert(node(n,c,t)); assert(contents::node(s,c,i,t)); assert(base.dom() =~= c.keys);
    assert forall |p: int| 0 <= p < ops.len() && (#[trigger] ops[p]).kind == Kind::Read implies ops[p].value == effects(base,ops.take(p))[ops[p].key] by {
        operations::valid_prefix(ops,c,t,p); operations::effects_value(base,ops.take(p),c,t,ops[p].key);
    }
}
} // verus!
