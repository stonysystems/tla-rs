//! Necessary conditions that the original goals impose on out-of-domain values.
//! These conditional lemmas are not proofs or refutations of the benchmark goals.
use vstd::prelude::*;
use super::zookeeper as model;
use super::zookeeper_bad_index as trace;
use super::zookeeper_trace_ids as ids;
use super::zab::{self as z,Txn,Zxid,Proposal};
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub proof fn integrity_requires_undefined_value()
    ensures model::integrity(trace::state(197),trace::constants()) ==>
        trace::state(197).election.nodes[ids::c()].history[3].value == 0
{
    ids::geometry(); reveal(trace::state); reveal(trace::state_197);
    let s=trace::state(197); let p=model::goal_state(s); let t=s.election.nodes[ids::c()].history[3];
    assert(s.election.nodes[ids::c()].history.len() == 3);
    if model::integrity(s,trace::constants()) {
        assert(z::proposed(p,p.nodes[ids::c()].history[4-1]));
        let q=choose |q: Proposal| p.proposals.contains(q) && q.zxid == t.zxid && q.value == t.value;
        assert forall |q: Proposal| p.proposals.contains(q) implies q.value == 0 by {}
        assert(q.value == 0);
    }
}
pub proof fn global_order_requires_undefined_epoch()
    ensures model::global_primary_order(trace::state(191),trace::constants()) ==>
        trace::state(191).election.nodes[ids::c()].history[3].zxid.epoch >= 4
{
    ids::geometry(); reveal(trace::state); reveal(trace::state_191);
    let s=trace::state(191); let p=model::goal_state(s);
    assert(s.election.nodes[ids::c()].history.len() == 3);
    if model::global_primary_order(s,trace::constants()) {
        assert(z::epoch_order(p.nodes[ids::c()],4,2));
    }
}
pub proof fn local_order_restricts_undefined_transaction()
    ensures (trace::state(191).election.nodes[ids::c()].history[3].zxid == (Zxid { epoch: 1,counter: 2 })
        && trace::state(191).election.nodes[ids::c()].history[3].value == 0) ==>
        !model::local_primary_order(trace::state(191),trace::constants())
{
    ids::geometry(); reveal(trace::state); reveal(trace::state_191);
    let s=trace::state(191); let p=model::goal_state(s); let n=p.nodes[ids::c()];
    let ta=Txn { zxid: Zxid { epoch: 1,counter: 1 },value: 0,ack: Set::empty(),epoch: 0 };
    let tb=Txn { zxid: Zxid { epoch: 1,counter: 2 },value: 0,ack: Set::empty(),epoch: 0 };
    let pa=Proposal { source: ids::a(),epoch: 1,zxid: ta.zxid,value: 0 };
    let pb=Proposal { source: ids::a(),epoch: 1,zxid: tb.zxid,value: 0 };
    assert(n.history.len() == 3 && n.committed.index == 4);
    assert(p.proposals.contains(pa) && p.proposals.contains(pb));
    if z::equal(n.history[3],tb) {
        assert(1 <= 4int <= n.committed.index && z::equal(n.history[4int-1],tb));
        assert(exists |k: int| k == 4 && #[trigger] z::equal(n.history[k-1],tb));
        assert(z::contains_txn(n,tb));
        assert forall |k: int| 1 <= k < 4 implies !#[trigger] z::equal(n.history[k-1],ta) by {}
        assert(!z::before(n,ta,tb));
        if model::local_primary_order(s,trace::constants()) {
            assert(z::local_at(p,ids::a(),1,ids::c()));
            assert(z::before(n,ta,tb));
            assert(false);
        }
    }
}
} // verus!
