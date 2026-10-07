//! Eligible elections are unique and contain every lower-term direct decision.
//! These are the induction steps; eligibility itself is proved separately.
use vstd::prelude::*;
use super::hashicorp::{*,sub};
use super::hashicorp_config as configs;
use super::hashicorp_types as types;
use super::hashicorp_order as order;
use super::hashicorp_history::{self as history,step};
use super::hashicorp_prefixes as prefixes;
use super::hashicorp_candidates as candidates;
use super::hashicorp_election_trace as elections;
use super::hashicorp_certificates as certificates;
use super::hashicorp_vote_witness::{self as witness,trace};
use super::hashicorp_config_lineage as lineage;
use super::hashicorp_config_barriers as barriers;
use super::hashicorp_config_adjacency as adjacency;
use super::hashicorp_commits as commits;
use super::hashicorp_retention::{self as retention,decision,decided,complete_below};
use super::hashicorp_eligibility::eligible;
use super::temporal::Behavior;
verus! {
pub open spec fn complete(b: Behavior<LState>,c: Constants,horizon: int,e: Event) -> bool {
    forall |at: int,i: int| 0 <= at < horizon && (#[trigger] decision(b,c,at,i)) && b[at].nodes[i].term < e.term ==> prefix(decided(b,at,i),e.entries)
}
pub proof fn anchor_for_entry(b: Behavior<LState>,c: Constants,horizon: int,e: Event) -> (origin: (int,int))
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,e.term),complete_below(b,c,horizon,e.term),horizon >= 0,
        b[horizon].elections.contains(e),last_config(e.entries) > 0
    ensures 0 <= origin.0 < horizon,decision(b,c,origin.0,origin.1),c.servers.contains(origin.1),
        b[origin.0].nodes[origin.1].term == e.entries[last_config(e.entries)-1].term,
        prefix(decided(b,origin.0,origin.1),e.entries),adjacency::anchor(e.entries,e.entries,decided(b,origin.0,origin.1).len() as int)
{
    let at=elections::election_origin(b,c,horizon,e); elections::election_log(b,c,horizon,e); types::last_config_valid(e.entries);
    let k=last_config(e.entries) as int-1; let origin=barriers::barrier_for_entry(b,c,horizon,e.term,at,e.server,k);
    let d=decided(b,origin.0,origin.1); assert(prefix(sub(e.entries,1,k),e.entries)); retention::transitive(d,sub(e.entries,1,k),e.entries);
    assert(d[d.len()-1] == e.entries[d.len()-1]); origin
}
pub proof fn move_anchor(h: Seq<Entry>,v: Seq<Entry>,d: Seq<Entry>)
    requires prefix(d,h),prefix(d,v),adjacency::anchor(h,h,d.len() as int)
    ensures adjacency::anchor(h,v,d.len() as int)
{}
pub proof fn prefix_inside(h: Seq<Entry>,d: Seq<Entry>,length: int)
    requires prefix(d,h),d.len() <= length <= h.len()
    ensures prefix(d,sub(h,1,length))
{ assert(sub(sub(h,1,length),1,d.len() as int) =~= d); }
pub proof fn higher_entry_contains(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,time: int,i: int,k: int,at: int,writer: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),complete_below(b,c,horizon,bound),
        0 <= time <= horizon,c.servers.contains(i),0 <= k < b[time].nodes[i].log.len(),0 <= at < horizon,decision(b,c,at,writer),
        b[at].nodes[writer].term < b[time].nodes[i].log[k].term < bound
    ensures prefix(decided(b,at,writer),b[time].nodes[i].log)
{
    let origin=prefixes::prefix_origin(b,c,horizon,bound,time,i,k); let h=decided(b,at,writer); let v=b[time].nodes[i].log;
    assert(prefix(h,b[origin.0].nodes[origin.1].log)); candidates::created_extends(b,c,origin.0,origin.1,k,v[k]);
    retention::transitive(h,b[origin.0].nodes[origin.1].log,b[origin.0+1].nodes[origin.1].log);
    assert(prefix(sub(v,1,k+1),v)); retention::transitive(h,sub(v,1,k+1),v);
}
pub proof fn anchor_from_later_config(b: Behavior<LState>,c: Constants,horizon: int,e: Event,time: int,i: int) -> (start: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,e.term),complete_below(b,c,horizon,e.term),
        0 <= time <= horizon,c.servers.contains(i),b[horizon].elections.contains(e),last_config(e.entries) > 0,last_config(b[time].nodes[i].log) > 0,
        adjacency::old_configs(b[time].nodes[i].log,e.term),
        e.entries[last_config(e.entries)-1].term < b[time].nodes[i].log[last_config(b[time].nodes[i].log)-1].term
        || e.entries[last_config(e.entries)-1].term == b[time].nodes[i].log[last_config(b[time].nodes[i].log)-1].term && last_config(e.entries) <= last_config(b[time].nodes[i].log)
    ensures adjacency::anchor(e.entries,b[time].nodes[i].log,start)
{
    let barrier=anchor_for_entry(b,c,horizon,e); let h=decided(b,barrier.0,barrier.1); let v=b[time].nodes[i].log;
    let k=last_config(e.entries) as int-1; let q=last_config(v) as int-1; types::last_config_valid(v);
    if e.entries[k].term < v[q].term { higher_entry_contains(b,c,horizon,e.term,time,i,q,barrier.0,barrier.1); }
    else {
        let elected=elections::election_origin(b,c,horizon,e); elections::election_log(b,c,horizon,e); types::last_config_valid(e.entries);
        let a=prefixes::prefix_origin(b,c,horizon,e.term,elected,e.server,k); let d=prefixes::prefix_origin(b,c,horizon,e.term,time,i,q);
        prefix_inside(e.entries,h,k+1); candidates::ordered_creations(b,c,horizon,e.term,a.0,a.1,k,e.entries[k],d.0,d.1,q,v[q]);
        retention::transitive(h,b[a.0+1].nodes[a.1].log,b[d.0+1].nodes[d.1].log);
        assert(prefix(sub(v,1,q+1),v)); retention::transitive(h,sub(v,1,q+1),v);
    }
    move_anchor(e.entries,v,h); h.len() as int
}
pub proof fn eligible_configurations(b: Behavior<LState>,c: Constants,horizon: int,a: Event,d: Event)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,a.term),complete_below(b,c,horizon,a.term),horizon >= 0,
        b[horizon].elections.contains(a),b[horizon].elections.contains(d),a.term == d.term,eligible(b,c,horizon,a),eligible(b,c,horizon,d)
    ensures lineage::adjacent(certificates::configuration(a,c),certificates::configuration(d,c))
{
    let left=elections::election_origin(b,c,horizon,a); let right=elections::election_origin(b,c,horizon,d);
    elections::election_log(b,c,horizon,a); elections::election_log(b,c,horizon,d);
    assert(adjacency::old_configs(a.entries,a.term) && adjacency::old_configs(d.entries,d.term));
    if last_config(a.entries) == 0 {
        assert(sub(a.entries,1,0) =~= sub(d.entries,1,0)); adjacency::configurations_adjacent(b,c,horizon,a,right,d.server,0);
    } else if last_config(d.entries) == 0 {
        assert(sub(a.entries,1,0) =~= sub(d.entries,1,0)); adjacency::configurations_adjacent(b,c,horizon,d,left,a.server,0);
    } else {
        let k=last_config(a.entries) as int-1; let q=last_config(d.entries) as int-1;
        if a.entries[k].term < d.entries[q].term || a.entries[k].term == d.entries[q].term && k <= q {
            let start=anchor_from_later_config(b,c,horizon,a,right,d.server); adjacency::configurations_adjacent(b,c,horizon,a,right,d.server,start);
        } else {
            let start=anchor_from_later_config(b,c,horizon,d,left,a.server); adjacency::configurations_adjacent(b,c,horizon,d,left,a.server,start);
        }
    }
}
pub proof fn unique_eligible(b: Behavior<LState>,c: Constants,horizon: int,a: Event,d: Event)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,a.term),complete_below(b,c,horizon,a.term),horizon >= 0,
        b[horizon].elections.contains(a),b[horizon].elections.contains(d),a.term == d.term,eligible(b,c,horizon,a),eligible(b,c,horizon,d)
    ensures a.server == d.server
{
    eligible_configurations(b,c,horizon,a,d); witness::trace_valid(b,c,horizon); let g=trace(b,c,horizon);
    assert(certificates::certificate(g,c,a)); assert(certificates::certificate(g,c,d));
    let av=certificates::configuration(a,c); let dv=certificates::configuration(d,c);
    let j=lineage::adjacent_quorums(certificates::voters(g,c,a).intersect(av),certificates::voters(g,c,d).intersect(dv),av,dv);
    certificates::intersecting_certificates(g,c,a,d,j);
}
pub proof fn eligible_contains(b: Behavior<LState>,c: Constants,horizon: int,e: Event,at: int,i: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,e.term),complete_below(b,c,horizon,e.term),horizon >= 0,
        b[horizon].elections.contains(e),eligible(b,c,horizon,e),0 <= at < horizon,decision(b,c,at,i),b[at].nodes[i].term < e.term
    ensures prefix(decided(b,at,i),e.entries)
{
    let elected=elections::election_origin(b,c,horizon,e); elections::election_log(b,c,horizon,e); commits::decision_certificate(b,c,at,i);
    let g=order::safety_at(b,c,at); assert(order::node(g.state.nodes[i])); let v=b[at].nodes[i].log; let h=decided(b,at,i);
    assert(adjacency::old_configs(v,e.term));
    if last_config(e.entries) == 0 {
        assert(sub(e.entries,1,0) =~= sub(v,1,0)); adjacency::configurations_adjacent(b,c,horizon,e,at,i,0);
    } else {
        types::last_config_valid(e.entries); let k=last_config(e.entries) as int-1;
        if b[at].nodes[i].term < e.entries[k].term { higher_entry_contains(b,c,horizon,e.term,elected,e.server,k,at,i); return; }
        let barrier=anchor_for_entry(b,c,horizon,e); let d=decided(b,barrier.0,barrier.1);
        if e.entries[k].term < b[at].nodes[i].term { assert(prefix(d,v)); }
        else {
            let origin=prefixes::prefix_origin(b,c,horizon,e.term,elected,e.server,k); let created=origin.0; let writer=origin.1;
            assert(writer == i); candidates::created_extends(b,c,created,writer,k,e.entries[k]);
            if at < created {
                history::continuous(b,c,i,at,created); assert(prefix(h,v)); retention::transitive(h,v,b[created].nodes[i].log);
                retention::transitive(h,b[created].nodes[i].log,b[created+1].nodes[i].log);
                assert(prefix(sub(e.entries,1,k+1),e.entries)); retention::transitive(h,sub(e.entries,1,k+1),e.entries); return;
            }
            assert(created != at); history::continuous(b,c,i,created+1,at);
            prefix_inside(e.entries,d,k+1); retention::transitive(d,b[created+1].nodes[i].log,v);
        }
        move_anchor(e.entries,v,d); adjacency::configurations_adjacent(b,c,horizon,e,at,i,d.len() as int);
    }
    types::safety_at(b,c,at); assert(types::node(b[at].nodes[i],c));
    assert(lineage::adjacent(b[at].nodes[i].latest_config,certificates::configuration(e,c)));
}
pub proof fn complete_eligible(b: Behavior<LState>,c: Constants,horizon: int,e: Event)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,e.term),complete_below(b,c,horizon,e.term),horizon >= 0,
        b[horizon].elections.contains(e),eligible(b,c,horizon,e)
    ensures complete(b,c,horizon,e)
{
    assert forall |at: int,i: int| 0 <= at < horizon && (#[trigger] decision(b,c,at,i)) && b[at].nodes[i].term < e.term implies prefix(decided(b,at,i),e.entries) by {
        eligible_contains(b,c,horizon,e,at,i);
    }
}
} // verus!
