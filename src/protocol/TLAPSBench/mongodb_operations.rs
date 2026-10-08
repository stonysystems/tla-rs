//! Summaries of operation sequences used by storage and the observed transaction history.
use vstd::prelude::*;
use super::mongodb::*;
verus! {
broadcast use { vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures, vstd::set::Set::lemma_map_contains };
pub proof fn write_member(ops: Seq<Operation>,k: int)
    ensures write_keys(ops).contains(k) <==> exists |i: int| 0 <= i < ops.len() && (#[trigger] ops[i]).kind == Kind::Write && ops[i].key == k
{
    let q=ops.to_set().filter(|o: Operation| o.kind == Kind::Write); q.lemma_map_contains(|o: Operation| o.key,k);
    if write_keys(ops).contains(k) {
        let o=choose |o: Operation| #![trigger q.contains(o)] q.contains(o) && o.key == k; assert(ops.to_set().contains(o));
        let i=choose |i: int| 0 <= i < ops.len() && ops[i] == o;
    }
    if exists |i: int| 0 <= i < ops.len() && (#[trigger] ops[i]).kind == Kind::Write && ops[i].key == k {
        let i=choose |i: int| 0 <= i < ops.len() && (#[trigger] ops[i]).kind == Kind::Write && ops[i].key == k;
        assert(q.contains(ops[i]));
    }
}
pub proof fn writes_concat(a: Seq<Operation>,d: Seq<Operation>)
    ensures write_keys(a+d) =~= write_keys(a).union(write_keys(d))
{
    assert forall |k: int| #![trigger write_keys(a+d).contains(k)] write_keys(a+d).contains(k) <==> write_keys(a).union(write_keys(d)).contains(k) by {
        write_member(a+d,k); write_member(a,k); write_member(d,k);
        if write_keys(a+d).contains(k) {
            let i=choose |i: int| 0 <= i < (a+d).len() && (#[trigger] (a+d)[i]).kind == Kind::Write && (a+d)[i].key == k;
            if i < a.len() { assert((a+d)[i] == a[i]); } else { assert((a+d)[i] == d[i-a.len()]); }
        }
        if write_keys(a).contains(k) {
            let i=choose |i: int| 0 <= i < a.len() && (#[trigger] a[i]).kind == Kind::Write && a[i].key == k; assert((a+d)[i] == a[i]);
        }
        if write_keys(d).contains(k) {
            let i=choose |i: int| 0 <= i < d.len() && (#[trigger] d[i]).kind == Kind::Write && d[i].key == k; assert((a+d)[i+a.len()] == d[i]);
        }
    }
}
pub proof fn writes_append(ops: Seq<Operation>,o: Operation)
    ensures write_keys(ops.push(o)) =~= if o.kind == Kind::Write { write_keys(ops).insert(o.key) } else { write_keys(ops) }
{
    writes_concat(ops,seq![o]); assert(ops.push(o) =~= ops+seq![o]);
    assert forall |k: int| write_keys(seq![o]).contains(k) <==> o.kind == Kind::Write && o.key == k by { write_member(seq![o],k); assert(seq![o][0] == o); }
}
pub open spec fn valid(ops: Seq<Operation>,c: Constants,t: int) -> bool {
    forall |i: int| 0 <= i < ops.len() ==> c.keys.contains((#[trigger] ops[i]).key)
        && (c.txns.contains(ops[i].value) || ops[i].value == c.no_value) && (ops[i].kind == Kind::Write ==> ops[i].value == t)
}
pub open spec fn owned(ops: Seq<Operation>,catalog: IMap<int,int>,shard: int) -> bool {
    forall |i: int| 0 <= i < ops.len() ==> #[trigger] catalog[ops[i].key] == shard
}
pub proof fn valid_prefix(ops: Seq<Operation>,c: Constants,t: int,n: int)
    requires valid(ops,c,t),0 <= n <= ops.len()
    ensures valid(ops.take(n),c,t)
{
    assert forall |p: int| 0 <= p < ops.take(n).len() implies c.keys.contains((#[trigger] ops.take(n)[p]).key)
        && (c.txns.contains(ops.take(n)[p].value) || ops.take(n)[p].value == c.no_value)
        && (ops.take(n)[p].kind == Kind::Write ==> ops.take(n)[p].value == t) by { assert(ops.take(n)[p] == ops[p]); }
}
pub proof fn effects_value(base: IMap<int,int>,ops: Seq<Operation>,c: Constants,t: int,k: int)
    requires base.dom() == c.keys,valid(ops,c,t),c.keys.contains(k)
    ensures effects(base,ops).dom() == c.keys,effects(base,ops)[k] == if write_keys(ops).contains(k) { t } else { base[k] }
    decreases ops.len()
{
    if ops.len() == 0 { assert(ops.to_set() =~= Set::<Operation>::empty()); assert(write_keys(ops) =~= Set::<int>::empty()); }
    else {
        let d=ops.drop_last(); let o=ops.last(); assert(d =~= ops.take(ops.len() as int-1)); valid_prefix(ops,c,t,ops.len() as int-1);
        effects_value(base,d,c,t,k); writes_append(d,o); assert(d.push(o) =~= ops);
        assert(effects(base,ops).dom() =~= c.keys);
    }
}
} // verus!
