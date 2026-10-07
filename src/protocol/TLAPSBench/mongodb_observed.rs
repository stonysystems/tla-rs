//! Only finitely many transactions have observed operations, all with legal keys and values.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
use super::mongodb_operations as operations;
use super::mongodb_storage_contents as contents;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn observed(s: LState,c: Constants) -> ISet<int> { c.txns.filter(|t: int| s.ops[t].len() > 0) }
pub open spec fn safe(s: LState,c: Constants) -> bool {
    observed(s,c).finite() && forall |t: int| c.txns.contains(t) ==> #[trigger] operations::valid(s.ops[t],c,t)
}
pub proof fn initial_safe(c: Constants,catalog: IMap<int,int>)
    ensures safe(initial(c,catalog),c)
{
    let s=initial(c,catalog); assert(observed(s,c) =~= ISet::<int>::empty());
    assert forall |t: int| c.txns.contains(t) implies #[trigger] operations::valid(s.ops[t],c,t) by {}
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::shape(s,c),contents::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a); reveal(enabled); reveal(apply);
    if let Action::Commit(m)=a {
        assert(contents::node(s,c,m.shard,m.txn)); let bound=observed(s,c).insert(m.txn);
        assert(observed(u,c).subset_of(bound)); assert(bound.finite()); vstd::iset_lib::lemma_iset_subset_finite(bound,observed(u,c));
    } else { assert(observed(u,c) =~= observed(s,c)); }
    assert forall |t: int| c.txns.contains(t) implies #[trigger] operations::valid(u.ops[t],c,t) by {
        assert(operations::valid(s.ops[t],c,t));
        if let Action::Commit(m)=a {
            if t == m.txn {
                assert(contents::node(s,c,m.shard,t));
                assert forall |p: int| 0 <= p < u.ops[t].len() implies c.keys.contains((#[trigger] u.ops[t][p]).key)
                    && (c.txns.contains(u.ops[t][p].value) || u.ops[t][p].value == c.no_value)
                    && (u.ops[t][p].kind == Kind::Write ==> u.ops[t][p].value == t) by {
                    if p < s.ops[t].len() { assert(u.ops[t][p] == s.ops[t][p]); }
                    else { assert(u.ops[t][p] == s.shards[m.shard].txns[t].ops[p-s.ops[t].len()]); }
                }
            }
        }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires support::safety_spec(b,c),time >= 0
    ensures safe(b[time],c),well_formed_ops(b[time],c)
    decreases time
{
    if time == 0 { initial_safe(c,b[0].catalog); }
    else { at(b,c,time-1); support::at(b,c,time-1); contents::at(b,c,time-1); let a=support::step(b,c,time-1); preserve(b[time-1],c,a); }
    support::at(b,c,time);
    assert forall |t: int,i: int| c.txns.contains(t) && 0 <= i < b[time].ops[t].len() implies
        c.keys.contains((#[trigger] b[time].ops[t][i]).key) && (c.txns.contains(b[time].ops[t][i].value) || b[time].ops[t][i].value == c.no_value) by {
        assert(operations::valid(b[time].ops[t],c,t));
    }
}
} // verus!
