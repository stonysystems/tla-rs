//! Benchmark Integrity and GlobalPrimaryOrder from transaction provenance and bounded histories.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role};
use super::zookeeper_support as support;
use super::zookeeper_commit_bounds as bounds;
use super::zookeeper_log_records as records;
use super::zookeeper_log_order as order;
use super::zookeeper_log_math as logs;
use super::temporal::Behavior;
verus! {
pub proof fn integrity_at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0
    ensures integrity(b[tick],c)
{
    bounds::at(b,c,tick); records::at(b,c,tick); support::at(b,c,tick);
    let s=b[tick]; let p=goal_state(s);
    assert forall |i: int,k: int| c.servers.contains(i) && p.nodes[i].role == Role::Following && 1 <= k <= p.nodes[i].committed.index
        implies #[trigger] z::proposed(p,p.nodes[i].history[k-1]) by {
        assert(bounds::node(s,i)); assert(records::node(s,i));
        assert(super::zookeeper_proposal_records::recorded(s,s.election.nodes[i].history[k-1].zxid,s.election.nodes[i].history[k-1].value));
        let t=s.election.nodes[i].history[k-1];
        let witness=choose |q: z::Proposal| s.proposals.contains(q) && q.zxid == t.zxid && q.value == t.value;
        assert(p.proposals.contains(witness) && witness.zxid == p.nodes[i].history[k-1].zxid && witness.value == p.nodes[i].history[k-1].value);
    }
}
pub proof fn global_primary_order_at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0
    ensures global_primary_order(b[tick],c)
{
    bounds::at(b,c,tick); order::at(b,c,tick); support::at(b,c,tick);
    let s=b[tick]; let p=goal_state(s);
    assert forall |i: int,x: int,y: int| c.servers.contains(i) && p.nodes[i].committed.index >= 2 && 1 <= x <= p.nodes[i].committed.index && 1 <= y <= p.nodes[i].committed.index
        implies #[trigger] z::epoch_order(p.nodes[i],x,y) by {
        assert(bounds::node(s,i)); assert(order::node(s,i));
        if y <= x { logs::ordered(s.election.nodes[i].history,y-1,x-1); }
    }
}
pub proof fn benchmark_integrity(b: Behavior<LState>,c: Constants)
    requires support::safety_spec(b,c)
    ensures forall |tick: int| tick >= 0 ==> #[trigger] integrity(b[tick],c)
{
    assert forall |tick: int| tick >= 0 implies #[trigger] integrity(b[tick],c) by { integrity_at(b,c,tick); }
}
pub proof fn benchmark_global_primary_order(b: Behavior<LState>,c: Constants)
    requires support::safety_spec(b,c)
    ensures forall |tick: int| tick >= 0 ==> #[trigger] global_primary_order(b[tick],c)
{
    assert forall |tick: int| tick >= 0 implies #[trigger] global_primary_order(b[tick],c) by { global_primary_order_at(b,c,tick); }
}
} // verus!
