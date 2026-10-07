//! Filtering the observed transaction history by shard gives exactly that shard's committed operations.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
use super::mongodb_storage_lifecycle as lifecycle;
use super::mongodb_storage_contents as contents;
use super::mongodb_operations as operations;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq_lib::group_filter_ensures };
pub open spec fn on_shard(catalog: IMap<int,int>,i: int) -> spec_fn(Operation) -> bool { |o: Operation| catalog[o.key] == i }
pub open spec fn project(ops: Seq<Operation>,catalog: IMap<int,int>,i: int) -> Seq<Operation> { ops.filter(on_shard(catalog,i)) }
pub proof fn owned_filter(ops: Seq<Operation>,catalog: IMap<int,int>,i: int,j: int)
    requires operations::owned(ops,catalog,i)
    ensures project(ops,catalog,j) == if i == j { ops } else { Seq::empty() }
    decreases ops.len()
{
    reveal(Seq::filter);
    if ops.len() > 0 {
        let d=ops.drop_last(); assert(operations::owned(d,catalog,i)) by {
            assert forall |p: int| 0 <= p < d.len() implies #[trigger] catalog[d[p].key] == i by { assert(d[p] == ops[p]); }
        }
        owned_filter(d,catalog,i,j); assert(catalog[ops.last().key] == i); assert(d.push(ops.last()) =~= ops);
    }
}
pub proof fn concat(a: Seq<Operation>,d: Seq<Operation>,catalog: IMap<int,int>,i: int)
    ensures project(a+d,catalog,i) == project(a,catalog,i)+project(d,catalog,i)
{
    Seq::filter_distributes_over_add(a,d,on_shard(catalog,i));
}
pub open spec fn node(s: LState,c: Constants,i: int,t: int) -> bool {
    project(s.ops[t],s.catalog,i) == if s.shards[i].txns[t].snapshot.committed { s.shards[i].txns[t].ops } else { Seq::empty() }
}
pub open spec fn safe(s: LState,c: Constants) -> bool {
    forall |i: int,t: int| c.shards.contains(i) && c.txns.contains(t) ==> #[trigger] node(s,c,i,t)
}
pub proof fn initial_safe(c: Constants,catalog: IMap<int,int>)
    ensures safe(initial(c,catalog),c)
{
    reveal(Seq::filter); let s=initial(c,catalog);
    assert forall |i: int,t: int| c.shards.contains(i) && c.txns.contains(t) implies #[trigger] node(s,c,i,t) by {}
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::shape(s,c),lifecycle::safe(s,c),contents::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a); reveal(enabled); reveal(apply);
    assert forall |i: int,t: int| c.shards.contains(i) && c.txns.contains(t) implies #[trigger] node(u,c,i,t) by {
        assert(node(s,c,i,t)); assert(lifecycle::row(s,c,i)); assert(lifecycle::node(s.shards[i],t));
        if s.shards[i].txns[t].snapshot.committed { lifecycle::committed_fixed(s,c,a,i,t); }
        if let Action::Commit(m)=a {
            if t == m.txn {
                assert(contents::node(s,c,m.shard,t)); concat(s.ops[t],s.shards[m.shard].txns[t].ops,s.catalog,i);
                owned_filter(s.shards[m.shard].txns[t].ops,s.catalog,m.shard,i);
                if i == m.shard { assert(!s.shards[i].txns[t].snapshot.committed); }
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
pub proof fn written_key(s: LState,c: Constants,t: int,k: int)
    requires support::shape(s,c),safe(s,c),c.txns.contains(t),c.keys.contains(k),operations::valid(s.ops[t],c,t)
    ensures write_keys(s.ops[t]).contains(k) <==> s.shards[s.catalog[k]].txns[t].snapshot.committed && write_keys(s.shards[s.catalog[k]].txns[t].ops).contains(k)
{
    let i=s.catalog[k]; assert(c.shards.contains(i)); assert(support::shard(s,c,i)); assert(node(s,c,i,t));
    let p=on_shard(s.catalog,i);
    assert(project(s.ops[t],s.catalog,i) == s.ops[t].filter(p));
    operations::write_member(s.ops[t],k); operations::write_member(project(s.ops[t],s.catalog,i),k);
    if write_keys(s.ops[t]).contains(k) {
        let j=choose |j: int| 0 <= j < s.ops[t].len() && (#[trigger] s.ops[t][j]).kind == Kind::Write && s.ops[t][j].key == k;
        s.ops[t].lemma_filter_contains(p,j); let n=choose |n: int| 0 <= n < s.ops[t].filter(p).len() && s.ops[t].filter(p)[n] == s.ops[t][j];
    }
    if write_keys(project(s.ops[t],s.catalog,i)).contains(k) {
        let n=choose |n: int| 0 <= n < s.ops[t].filter(p).len() && (#[trigger] s.ops[t].filter(p)[n]).kind == Kind::Write && s.ops[t].filter(p)[n].key == k;
        let e=s.ops[t].filter(p)[n]; assert(s.ops[t].filter(p).contains(e)); s.ops[t].lemma_filter_contains_rev(p,e);
        let j=choose |j: int| 0 <= j < s.ops[t].len() && s.ops[t][j] == e;
    }
    if !s.shards[i].txns[t].snapshot.committed { operations::write_member(Seq::empty(),k); }
}
} // verus!
