//! A finite order by commit timestamp for writers and read timestamp for read-only transactions.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_transaction_time as times;
use super::mongodb_global_reads as reads;
use super::mongodb_observed as observed;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures };
pub open spec fn ordered(order: Seq<int>,rank: spec_fn(int) -> int) -> bool {
    forall |p: int,q: int| 0 <= p < q < order.len() ==> rank(#[trigger] order[p]) <= rank(#[trigger] order[q])
}
pub proof fn least(q: Set<int>,rank: spec_fn(int) -> int) -> (m: int)
    requires !q.is_empty()
    ensures q.contains(m),forall |t: int| q.contains(t) ==> rank(m) <= rank(t)
    decreases q.len()
{
    let n=choose |n: int| q.contains(n);
    if q.remove(n).is_empty() { n }
    else { let m=least(q.remove(n),rank); if rank(n) <= rank(m) { n } else { m } }
}
pub proof fn build(q: Set<int>,rank: spec_fn(int) -> int) -> (order: Seq<int>)
    ensures order.to_set() == q,order.no_duplicates(),ordered(order,rank)
    decreases q.len()
{
    if q.is_empty() { Seq::empty() }
    else {
        let m=least(q,rank); let rest=build(q.remove(m),rank); let order=seq![m]+rest;
        assert(order.to_set() =~= q); assert(!rest.contains(m));
        assert forall |p: int,j: int| 0 <= p < j < order.len() implies order[p] != order[j] && rank(#[trigger] order[p]) <= rank(#[trigger] order[j]) by {
            assert(order[j] == rest[j-1]);
            if p > 0 { assert(order[p] == rest[p-1]); }
            else { assert(order[p] == m); assert(q.contains(order[j])); }
        }
        assert(order.no_duplicates()); order
    }
}
pub proof fn cut(order: Seq<int>,rank: spec_fn(int) -> int,limit: int) -> (n: int)
    requires ordered(order,rank)
    ensures 0 <= n <= order.len(),forall |p: int| 0 <= p < order.len() ==> (p < n <==> rank(#[trigger] order[p]) <= limit)
    decreases order.len()
{
    if order.len() == 0 { 0 }
    else {
        let last=(order.len()-1) as int;
        if rank(order[last]) <= limit {
            assert forall |p: int| 0 <= p < order.len() implies rank(#[trigger] order[p]) <= limit by { if p < last { assert(rank(order[p]) <= rank(order[last])); } }
            order.len() as int
        } else {
            let d=order.drop_last(); assert(ordered(d,rank)); let n=cut(d,rank,limit);
            assert forall |p: int| 0 <= p < order.len() implies (p < n <==> rank(#[trigger] order[p]) <= limit) by { if p < last { assert(d[p] == order[p]); } }
            n
        }
    }
}
pub open spec fn rank(s: LState,c: Constants) -> spec_fn(int) -> int {
    |t: int| if times::writer(s,t) { 2*times::commit_ts(s,c,t) } else { 2*times::read_ts(s,c,t)+1 }
}
pub open spec fn valid_order(s: LState,c: Constants,order: Seq<int>) -> bool {
    order.to_set().to_iset() == observed::observed(s,c) && order.no_duplicates() && ordered(order,rank(s,c))
}
pub proof fn construct(s: LState,c: Constants) -> (order: Seq<int>)
    requires times::facts(s,c)
    ensures valid_order(s,c,order)
{
    let q=observed::observed(s,c).to_set().unwrap(); assert(q.to_iset() =~= observed::observed(s,c)); build(q,rank(s,c))
}
pub proof fn snapshot_cut(s: LState,c: Constants,order: Seq<int>,p: int) -> (n: int)
    requires times::facts(s,c),valid_constants(c),valid_order(s,c,order),0 <= p < order.len()
    ensures 0 <= n <= p,forall |j: int| 0 <= j < order.len() ==> (j < n <==> rank(s,c)(#[trigger] order[j]) <= 2*times::read_ts(s,c,order[p]))
{
    let t=order[p]; assert(order.to_set().contains(t)); assert(c.txns.contains(t)); reads::selected(s,c,t);
    if times::writer(s,t) { times::after_read(s,c,t); }
    let n=cut(order,rank(s,c),2*times::read_ts(s,c,t)); assert(rank(s,c)(t) > 2*times::read_ts(s,c,t)); n
}
} // verus!
