//! Committed-log agreement and the benchmark's every-quorum prefix property.
use vstd::prelude::*;
use super::etcd::{*,sub};
use super::etcd_election as election;
use super::etcd_logs as logs;
use super::etcd_prefixes as prefixes;
use super::etcd_history_trace as trace;
use super::etcd_commit_history::{self as history,Decision};
use super::etcd_election_prefixes as packets;
use super::etcd_completeness as completeness;
use super::etcd_retention as retention;
use super::etcd_stable_prefixes as stable;
use super::etcd_committed_prefixes as committed_proof;
use super::temporal::Behavior;
verus! {
pub proof fn decision_compatible(b: Behavior<LState>,c: Constants,time: int,a: Decision,d: Decision)
    requires election::safety_spec(b,c),time >= 0,trace::at(b,c,time).decisions.contains(a),trace::at(b,c,time).decisions.contains(d)
    ensures retention::compatible(a.log,d.log)
{
    trace::valid(b,c,time); trace::decision_log(b,c,time,a); trace::decision_log(b,c,time,d); let g=trace::at(b,c,time);
    assert(history::decision_valid(g,c,a)); assert(history::decision_valid(g,c,d));
    if a.term == d.term {
        if a.log.len() <= d.log.len() { assert(prefixes::same_term(a.log,d.log)); }
        else { assert(prefixes::same_term(d.log,a.log)); }
    } else if a.term < d.term {
        let t=trace::decision_origin(b,c,time,d); completeness::historical_completeness(b,c,time,t,d.leader,a);
        packets::common_prefix(a.log,d.log,b[t].nodes[d.leader].log);
    } else {
        let t=trace::decision_origin(b,c,time,a); completeness::historical_completeness(b,c,time,t,a.leader,d);
        packets::common_prefix(a.log,d.log,b[t].nodes[a.leader].log);
    }
}
pub proof fn covered_compatible(b: Behavior<LState>,c: Constants,time: int,h: Seq<nat>,v: Seq<nat>,ht: nat,vt: nat)
    requires election::safety_spec(b,c),time >= 0,committed_proof::covered(trace::at(b,c,time),h,ht),committed_proof::covered(trace::at(b,c,time),v,vt)
    ensures retention::compatible(h,v)
{
    if h.len() > 0 && v.len() > 0 {
        let a=choose |a: Decision| trace::at(b,c,time).decisions.contains(a) && a.term <= ht && #[trigger] logs::prefix_of(h,a.log);
        let d=choose |d: Decision| trace::at(b,c,time).decisions.contains(d) && d.term <= vt && #[trigger] logs::prefix_of(v,d.log);
        decision_compatible(b,c,time,a,d);
        if logs::prefix_of(a.log,d.log) { logs::prefix_transitive(h,a.log,d.log); packets::common_prefix(h,v,d.log); }
        else { logs::prefix_transitive(v,d.log,a.log); packets::common_prefix(h,v,a.log); }
    }
}
pub proof fn prefix_definition(h: Seq<nat>,v: Seq<nat>)
    requires logs::prefix_of(h,v)
    ensures prefix(h,v)
{ assert(h =~= sub(v,1,h.len() as int)); }
pub proof fn covered_quorum(b: Behavior<LState>,c: Constants,time: int,h: Seq<nat>,t: nat,q: Set<int>) -> (j: int)
    requires election::safety_spec(b,c),time >= 0,committed_proof::covered(trace::at(b,c,time),h,t),quorum(q,c)
    ensures q.contains(j),prefix(h,b[time].nodes[j].log)
{
    if h.len() == 0 {
        assert(!q.is_empty()); let j=q.choose(); prefix_definition(h,b[time].nodes[j].log); j
    } else {
        let d=choose |d: Decision| trace::at(b,c,time).decisions.contains(d) && d.term <= t && #[trigger] logs::prefix_of(h,d.log);
        trace::valid(b,c,time); assert(history::decision_valid(trace::at(b,c,time),c,d)); stable::quorum_retained(b,c,time,d);
        let j=election::majorities_intersect(d.quorum,q,c);
        assert(logs::prefix_of(d.log,b[time].nodes[j].log)); logs::prefix_transitive(h,d.log,b[time].nodes[j].log);
        prefix_definition(h,b[time].nodes[j].log); j
    }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,time: int)
    requires election::safety_spec(b,c),time >= 0
    ensures log_inv(b[time],c),quorum_log(b[time],c)
{
    trace::valid(b,c,time); committed_proof::safety_at(b,c,time); let g=trace::at(b,c,time); let s=b[time];
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies prefix(committed(s.nodes[i]),committed(s.nodes[j])) || prefix(committed(s.nodes[j]),committed(s.nodes[i])) by {
        assert(committed_proof::node(g,i)); assert(committed_proof::node(g,j));
        let h=committed(s.nodes[i]); let v=committed(s.nodes[j]); covered_compatible(b,c,time,h,v,s.nodes[i].term,s.nodes[j].term);
        if logs::prefix_of(h,v) { prefix_definition(h,v); } else { prefix_definition(v,h); }
    }
    assert forall |i: int,q: Set<int>| c.servers.contains(i) && quorum(q,c) implies exists |j: int| q.contains(j) && prefix(committed(s.nodes[i]),s.nodes[j].log) by {
        assert(committed_proof::node(g,i)); covered_quorum(b,c,time,committed(s.nodes[i]),s.nodes[i].term,q);
    }
}
pub proof fn benchmark_safety(b: Behavior<LState>,c: Constants)
    requires election::safety_spec(b,c)
    ensures forall |time: int| time >= 0 ==> #[trigger] log_inv(b[time],c),
        forall |time: int| time >= 0 ==> #[trigger] quorum_log(b[time],c)
{
    assert forall |time: int| time >= 0 implies #[trigger] log_inv(b[time],c) by { safety_at(b,c,time); }
    assert forall |time: int| time >= 0 implies #[trigger] quorum_log(b[time],c) by { safety_at(b,c,time); }
}
} // verus!
