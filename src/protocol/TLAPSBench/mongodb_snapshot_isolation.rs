//! The benchmark snapshot-isolation predicate follows from timestamp order and read snapshots.
use vstd::prelude::*;
use super::mongodb::*;
use super::mongodb_support as support;
use super::mongodb_transaction_time as times;
use super::mongodb_global_reads as reads;
use super::mongodb_local_reads as local;
use super::mongodb_operations as operations;
use super::mongodb_write_order as writes;
use super::mongodb_order as order;
use super::mongodb_execution as exec;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures };
pub proof fn one_snapshot(s: LState,c: Constants,q: Seq<int>,p: int)
    requires valid_constants(c),times::facts(s,c),writes::safe(s,c),local::safe(s,c),order::valid_order(s,c,q),0 <= p < q.len()
    ensures has_snapshot(s,c,q,p)
{
    let t=q[p]; let cut=order::snapshot_cut(s,c,q,p); let prefix=q.take(cut);
    assert(q.to_set().contains(t)); assert(c.txns.contains(t));
    assert forall |j: int| 0 <= j < prefix.len() implies c.txns.contains(#[trigger] prefix[j]) by { assert(prefix[j] == q[j]); assert(q.to_set().contains(q[j])); }
    exec::domain(s,c,prefix); let base=execution(s,c,prefix); let snapshot=reads::snapshot(s,c,t);
    assert(base =~= snapshot) by {
        assert(snapshot.dom() =~= c.keys);
        assert forall |k: int| c.keys.contains(k) implies #[trigger] base[k] == snapshot[k] by { exec::snapshot_value(s,c,q,cut,times::read_ts(s,c,t),k); }
    }
    reads::complete_global(s,c,t);
    assert forall |j: int| cut <= j < p implies #[trigger] write_keys(s.ops[q[j]]).disjoint(write_keys(s.ops[q[p]])) by {
        let w=q[j]; assert(q.to_set().contains(w)); assert(c.txns.contains(w)); assert(w != t);
        if !write_keys(s.ops[w]).disjoint(write_keys(s.ops[t])) {
            let k=choose |k: int| write_keys(s.ops[w]).contains(k) && write_keys(s.ops[t]).contains(k);
            assert(times::writer(s,w)); assert(times::writer(s,t)); assert(order::rank(s,c)(w) <= order::rank(s,c)(t));
            exec::write_separation(s,c,w,t,k); assert(order::rank(s,c)(w) <= 2*times::read_ts(s,c,t)); assert(j < cut); assert(false);
        }
    }
    assert(snapshot_at(s,c,q,p,cut));
}
pub proof fn state(s: LState,c: Constants)
    requires valid_constants(c),times::facts(s,c),writes::safe(s,c),local::safe(s,c)
    ensures snapshot_isolation(s,c)
{
    let q=order::construct(s,c);
    assert forall |p: int| 0 <= p < q.len() implies #[trigger] has_snapshot(s,c,q,p) by { one_snapshot(s,c,q,p); }
    assert(si_order(s,c,q));
    assert forall |t: int,p: int| c.txns.contains(t) && 0 <= p < s.ops[t].len() implies
        c.keys.contains((#[trigger] s.ops[t][p]).key) && (c.txns.contains(s.ops[t][p].value) || s.ops[t][p].value == c.no_value) by { assert(operations::valid(s.ops[t],c,t)); }
}
pub proof fn benchmark_snapshot_isolation(b: Behavior<LState>,c: Constants)
    requires support::safety_spec(b,c),forall |tick: int| tick >= 0 ==> #[trigger] single_write_per_key(b[tick],c)
    ensures forall |tick: int| tick >= 0 ==> #[trigger] snapshot_isolation(b[tick],c)
{
    assert forall |tick: int| tick >= 0 implies #[trigger] snapshot_isolation(b[tick],c) by {
        times::at(b,c,tick); writes::at(b,c,tick); local::at(b,c,tick); state(b[tick],c);
    }
}
} // verus!
