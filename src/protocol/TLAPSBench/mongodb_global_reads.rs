//! Per-shard read correctness composes through the observed operation projection.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
use super::mongodb_transaction_time as times;
use super::mongodb_projection as projection;
use super::mongodb_operations as operations;
use super::mongodb_local_reads as local;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq_lib::group_filter_ensures };
pub proof fn project_at(ops: Seq<Operation>,catalog: IMap<int,int>,p: int)
    requires 0 <= p < ops.len()
    ensures {
        let i=catalog[ops[p].key]; let all=projection::project(ops,catalog,i); let prefix=projection::project(ops.take(p),catalog,i); let j=prefix.len() as int;
        0 <= j < all.len() && all[j] == ops[p] && all.take(j) == prefix
    },
{
    let i=catalog[ops[p].key]; let before=ops.take(p); let one=seq![ops[p]]; let rest=ops.subrange(p+1,ops.len() as int);
    assert(ops =~= (before+one)+rest); assert(operations::owned(one,catalog,i)); projection::owned_filter(one,catalog,i,i);
    projection::concat(before,one,catalog,i); projection::concat(before+one,rest,catalog,i);
    let prefix=projection::project(before,catalog,i); let all=projection::project(ops,catalog,i); let j=prefix.len() as int;
    assert(all[j] == ops[p]); assert(all.take(j) =~= prefix);
}
pub proof fn project_writes(ops: Seq<Operation>,catalog: IMap<int,int>,k: int)
    ensures write_keys(projection::project(ops,catalog,catalog[k])).contains(k) <==> write_keys(ops).contains(k)
{
    let f=projection::on_shard(catalog,catalog[k]); let all=ops.filter(f);
    operations::write_member(ops,k); operations::write_member(all,k);
    if write_keys(ops).contains(k) {
        let p=choose |p: int| 0 <= p < ops.len() && (#[trigger] ops[p]).kind == Kind::Write && ops[p].key == k;
        ops.lemma_filter_contains(f,p); let q=choose |q: int| 0 <= q < all.len() && all[q] == ops[p];
    }
    if write_keys(all).contains(k) {
        let q=choose |q: int| 0 <= q < all.len() && (#[trigger] all[q]).kind == Kind::Write && all[q].key == k;
        assert(all.contains(all[q])); ops.lemma_filter_contains_rev(f,all[q]); let p=choose |p: int| 0 <= p < ops.len() && ops[p] == all[q];
    }
}
pub proof fn selected(s: LState,c: Constants,t: int)
    requires times::facts(s,c),valid_constants(c),c.txns.contains(t),s.ops[t].len() > 0
    ensures super::mongodb_participants::selected(s,c,t),times::read_ts(s,c,t) >= 0
{
    assert(operations::valid(s.ops[t],c,t)); let i=s.catalog[s.ops[t][0].key]; project_at(s.ops[t],s.catalog,0);
    assert(c.shards.contains(i)); assert(projection::node(s,c,i,t)); assert(s.shards[i].txns[t].snapshot.committed); times::local_read_ts(s,c,i,t);
}
pub open spec fn snapshot(s: LState,c: Constants,t: int) -> IMap<int,int> {
    IMap::new(|k: int| c.keys.contains(k),|k: int| snapshot_read(s.shards[s.catalog[k]],c,k,times::read_ts(s,c,t)))
}
pub proof fn read(s: LState,c: Constants,t: int,p: int)
    requires times::facts(s,c),local::safe(s,c),c.txns.contains(t),0 <= p < s.ops[t].len(),s.ops[t][p].kind == Kind::Read
    ensures s.ops[t][p].value == if write_keys(s.ops[t].take(p)).contains(s.ops[t][p].key) { t } else { snapshot(s,c,t)[s.ops[t][p].key] }
{
    let ops=s.ops[t]; let k=ops[p].key; let i=s.catalog[k]; assert(operations::valid(ops,c,t)); assert(c.keys.contains(k)); assert(c.shards.contains(i));
    project_at(ops,s.catalog,p); let prefix=projection::project(ops.take(p),s.catalog,i); let j=prefix.len() as int;
    assert(projection::node(s,c,i,t)); let x=s.shards[i].txns[t]; assert(x.snapshot.committed); assert(x.ops[j] == ops[p]); assert(x.ops.take(j) == prefix);
    assert(local::node(s.shards[i],c,t)); times::local_read_ts(s,c,i,t); project_writes(ops.take(p),s.catalog,k);
}
pub proof fn complete_global(s: LState,c: Constants,t: int)
    requires times::facts(s,c),local::safe(s,c),c.txns.contains(t)
    ensures complete(snapshot(s,c,t),s.ops[t])
{
    assert(operations::valid(s.ops[t],c,t)); let base=snapshot(s,c,t); assert(base.dom() =~= c.keys);
    assert forall |p: int| 0 <= p < s.ops[t].len() && (#[trigger] s.ops[t][p]).kind == Kind::Read implies s.ops[t][p].value == effects(base,s.ops[t].take(p))[s.ops[t][p].key] by {
        read(s,c,t,p); operations::valid_prefix(s.ops[t],c,t,p); operations::effects_value(base,s.ops[t].take(p),c,t,s.ops[t][p].key);
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0
    ensures forall |t: int| c.txns.contains(t) ==> #[trigger] complete(snapshot(b[tick],c,t),b[tick].ops[t])
{
    times::at(b,c,tick); local::at(b,c,tick);
    assert forall |t: int| c.txns.contains(t) implies #[trigger] complete(snapshot(b[tick],c,t),b[tick].ops[t]) by { complete_global(b[tick],c,t); }
}
} // verus!
