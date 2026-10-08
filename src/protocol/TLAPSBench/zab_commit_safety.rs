//! Benchmark consistency and ordering follow from reachable committed-prefix certificates.
use vstd::prelude::*;
use super::zab::{*,equal};
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_committed_prefixes as prefixes;
use super::zab_commit_certificates::certified;
use super::temporal::Behavior;
verus! {
pub proof fn prefix_point(b: Behavior<LState>,c: Constants,time: int,i: int,j: int,k: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),c.servers.contains(j),1 <= k <= b[time].nodes[i].committed.index,k <= b[time].nodes[j].committed.index
    ensures equal(b[time].nodes[i].history[k-1],b[time].nodes[j].history[k-1])
{
    prefixes::at(b,c,time); logs::at(b,c,time); let s=b[time]; logs::facts(s,c,i,j);
    assert(prefixes::node(b,c,time,i)); assert(prefixes::node(b,c,time,j));
    let n=s.nodes[i]; let d=s.nodes[j]; let x=n.committed.index-1; let y=d.committed.index-1;
    if k > 1 {
        let e=prefixes::certificate_for(b,c,time,i);
        let f=prefixes::certificate_for(b,c,time,j);
        super::zab_certified_safety::quorum_safety(b,c,time,e,n.history,x,time,f,d.history,y);
        assert(equal(n.history[k-1],d.history[k-1]));
    }
}
pub proof fn prefix_at(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0
    ensures prefix_consistency(b[time],c)
{
    prefixes::at(b,c,time); let s=b[time];
    assert forall |i: int| #![trigger c.servers.contains(i)] c.servers.contains(i) implies s.nodes[i].committed.index >= 0 by { assert(prefixes::node(b,c,time,i)); }
    assert forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 1 <= k <= s.nodes[i].committed.index && k <= s.nodes[j].committed.index
        implies #[trigger] equal(s.nodes[i].history[k-1],s.nodes[j].history[k-1]) by { prefix_point(b,c,time,i,j,k); }
}
pub proof fn agreement_at(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0
    ensures agreement(b[time],c)
{
    prefix_at(b,c,time); let s=b[time];
    assert forall |i: int,j: int,x: int,y: int| c.servers.contains(i) && c.servers.contains(j) && s.nodes[i].role == Role::Following && s.nodes[j].role == Role::Following && 1 <= x <= s.nodes[i].committed.index && 1 <= y <= s.nodes[j].committed.index
        implies #[trigger] contains_txn(s.nodes[j],s.nodes[i].history[x-1]) || #[trigger] contains_txn(s.nodes[i],s.nodes[j].history[y-1]) by {
        if x <= s.nodes[j].committed.index {
            assert(equal(s.nodes[i].history[x-1],s.nodes[j].history[x-1])); assert(equal(s.nodes[j].history[x-1],s.nodes[i].history[x-1]));
        } else { assert(y <= s.nodes[i].committed.index); assert(equal(s.nodes[i].history[y-1],s.nodes[j].history[y-1])); }
    }
}
pub proof fn total_order_at(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0
    ensures total_order(b[time],c)
{
    prefixes::at(b,c,time); let s=b[time];
    assert forall |i: int,j: int,x: int,y: int| c.servers.contains(i) && c.servers.contains(j) && s.nodes[j].committed.index >= 2 && 1 <= x < y <= s.nodes[i].committed.index && contains_txn(s.nodes[j],s.nodes[i].history[y-1])
        implies #[trigger] before(s.nodes[j],s.nodes[i].history[x-1],s.nodes[i].history[y-1]) by {
        assert(prefixes::node(b,c,time,i)); assert(prefixes::node(b,c,time,j));
        let p=choose |p: int| 1 <= p <= s.nodes[j].committed.index && #[trigger] equal(s.nodes[j].history[p-1],s.nodes[i].history[y-1]);
        super::zab_log_matching::historical_matching(b,c,time,i,time,j,y-1,p-1);
        assert(equal(s.nodes[i].history[x-1],s.nodes[j].history[x-1])); assert(equal(s.nodes[j].history[x-1],s.nodes[i].history[x-1]));
        assert(equal(s.nodes[j].history[y-1],s.nodes[i].history[y-1]));
    }
}
pub proof fn global_order_at(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0
    ensures global_primary_order(b[time],c)
{
    prefixes::at(b,c,time); logs::at(b,c,time); let s=b[time];
    assert forall |i: int,x: int,y: int| c.servers.contains(i) && s.nodes[i].committed.index >= 2 && 1 <= x <= s.nodes[i].committed.index && 1 <= y <= s.nodes[i].committed.index
        implies #[trigger] epoch_order(s.nodes[i],x,y) by {
        assert(prefixes::node(b,c,time,i)); logs::facts(s,c,i,i);
        if y < x { math::ordered(s.nodes[i].history,y-1,x-1); }
    }
}
pub proof fn benchmark_safety(b: Behavior<LState>,c: Constants)
    requires connections::safety_spec(b,c)
    ensures forall |time: int| time >= 0 ==> #[trigger] prefix_consistency(b[time],c),
        forall |time: int| time >= 0 ==> #[trigger] agreement(b[time],c),
        forall |time: int| time >= 0 ==> #[trigger] total_order(b[time],c),
        forall |time: int| time >= 0 ==> #[trigger] global_primary_order(b[time],c)
{
    assert forall |time: int| time >= 0 implies #[trigger] prefix_consistency(b[time],c) by { prefix_at(b,c,time); }
    assert forall |time: int| time >= 0 implies #[trigger] agreement(b[time],c) by { agreement_at(b,c,time); }
    assert forall |time: int| time >= 0 implies #[trigger] total_order(b[time],c) by { total_order_at(b,c,time); }
    assert forall |time: int| time >= 0 implies #[trigger] global_primary_order(b[time],c) by { global_order_at(b,c,time); }
}
} // verus!
