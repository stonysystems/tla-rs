//! An eligible candidate's configuration is adjacent to a log sharing the
//! commit that preceded its last configuration entry. No adjacency is assumed.
use vstd::prelude::*;
use super::hashicorp::{*,sub};
use super::hashicorp_config as configs;
use super::hashicorp_types as types;
use super::hashicorp_order as order;
use super::hashicorp_prefixes as prefixes;
use super::hashicorp_election_trace as elections;
use super::hashicorp_certificates as certificates;
use super::hashicorp_config_lineage as lineage;
use super::hashicorp_config_logs as logs;
use super::hashicorp_config_barriers as barriers;
use super::hashicorp_eligibility::{self as eligibility,eligible};
use super::hashicorp_retention::{self as retention,decision,decided,complete_below};
use super::temporal::Behavior;
verus! {
pub open spec fn old_configs(h: Seq<Entry>,term: nat) -> bool {
    forall |k: int| 0 <= k < h.len() && (#[trigger] h[k]).kind == EntryKind::Config ==> h[k].term < term
}
pub open spec fn anchor(h: Seq<Entry>,v: Seq<Entry>,start: int) -> bool {
    0 <= start <= h.len() && start <= v.len() && sub(h,1,start) == sub(v,1,start)
    && if last_config(h) == 0 { start == 0 } else {
        0 < start < last_config(h) && last_config(sub(h,1,last_config(h) as int-1)) <= start
        && h[start-1].term == h[last_config(h)-1].term
    }
}
pub proof fn eligible_entry(b: Behavior<LState>,c: Constants,horizon: int,e: Event,time: int,i: int,k: int) -> (origin: (int,int))
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,e.term),complete_below(b,c,horizon,e.term),eligible(b,c,horizon,e),
        0 <= time <= horizon,c.servers.contains(i),0 <= k < b[time].nodes[i].log.len(),b[time].nodes[i].log[k].kind == EntryKind::Config,
        b[time].nodes[i].log[k].term < e.term,lineage::adjacent(lineage::parent(b[time].nodes[i].log,k,c),certificates::configuration(e,c))
    ensures prefix(decided(b,origin.0,origin.1),e.entries),prefix(decided(b,origin.0,origin.1),b[time].nodes[i].log),
        0 < decided(b,origin.0,origin.1).len() <= k,
        log_term(decided(b,origin.0,origin.1),decided(b,origin.0,origin.1).len() as int) == b[time].nodes[i].log[k].term,
        logs::configuration(decided(b,origin.0,origin.1),c) == lineage::parent(b[time].nodes[i].log,k,c),
        last_config(sub(b[time].nodes[i].log,1,k)) <= decided(b,origin.0,origin.1).len()
{
    let origin=barriers::barrier_for_entry(b,c,horizon,e.term,time,i,k); let d=decided(b,origin.0,origin.1); let h=b[time].nodes[i].log;
    assert(prefix(d,e.entries)); assert(prefix(sub(h,1,k),h)); retention::transitive(d,sub(h,1,k),h); origin
}
pub proof fn first_agrees(b: Behavior<LState>,c: Constants,horizon: int,e: Event,time: int,i: int,start: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,e.term),complete_below(b,c,horizon,e.term),eligible(b,c,horizon,e),
        0 <= time <= horizon,c.servers.contains(i),b[horizon].elections.contains(e),anchor(e.entries,b[time].nodes[i].log,start),
        last_config(e.entries) > 0,old_configs(b[time].nodes[i].log,e.term),logs::first_config(b[time].nodes[i].log,start) < b[time].nodes[i].log.len()
    ensures logs::first_config(b[time].nodes[i].log,start) == last_config(e.entries) as int-1,
        b[time].nodes[i].log[logs::first_config(b[time].nodes[i].log,start)] == e.entries[last_config(e.entries)-1]
{
    let elected=elections::election_origin(b,c,horizon,e); elections::election_log(b,c,horizon,e); let h=e.entries; let v=b[time].nodes[i].log;
    let a=last_config(h) as int-1; let k=logs::first_config(v,start);
    types::last_config_valid(h); logs::before_last(h,start); logs::first_config_properties(v,start);
    logs::configuration_no_configs(h,c,start,a); logs::first_parent(v,c,start);
    assert(lineage::parent(v,k,c) == lineage::parent(h,a,c));
    lineage::adjacent_entry(b,c,horizon,e.term,elected,e.server,a);
    let origin=eligible_entry(b,c,horizon,e,time,i,k); let d=decided(b,origin.0,origin.1);
    if a < d.len() {
        logs::configuration_prefix(h,c,d.len() as int); assert(d == sub(h,1,d.len() as int)); assert(false);
    }
    let g=order::safety_at(b,c,time); assert(order::node(g.state.nodes[i]));
    assert(d[d.len()-1] == h[d.len()-1]); assert(h[d.len()-1].term <= h[a].term);
    assert(sub(h,1,start)[start-1] == sub(v,1,start)[start-1]); assert(v[start-1].term <= v[k].term);
    assert(h[a].term == v[k].term);
    barriers::same_term_first(b,c,horizon,e.term,elected,e.server,time,i,start);
}
pub proof fn no_next_after_change(b: Behavior<LState>,c: Constants,horizon: int,e: Event,time: int,i: int,k: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,e.term),complete_below(b,c,horizon,e.term),eligible(b,c,horizon,e),
        0 <= time <= horizon,c.servers.contains(i),0 <= k < b[time].nodes[i].log.len(),b[time].nodes[i].log[k].kind == EntryKind::Config,
        old_configs(b[time].nodes[i].log,e.term),last_config(e.entries) <= k,
        lineage::adjacent(b[time].nodes[i].log[k].config,certificates::configuration(e,c))
    ensures logs::first_config(b[time].nodes[i].log,k+1) == b[time].nodes[i].log.len()
{
    let v=b[time].nodes[i].log; let next=logs::first_config(v,k+1);
    logs::first_config_properties(v,k+1); logs::first_parent(v,c,k+1); logs::configuration_after_entry(v,c,k);
    if next < v.len() {
        let origin=eligible_entry(b,c,horizon,e,time,i,next); let d=decided(b,origin.0,origin.1);
        logs::entry_below_last(v,next,k); assert(k < d.len());
        assert(d[k] == v[k]); assert(d[k] == e.entries[k]);
        logs::after_last(e.entries,k); assert(false);
    }
}
pub proof fn configurations_adjacent(b: Behavior<LState>,c: Constants,horizon: int,e: Event,time: int,i: int,start: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,e.term),complete_below(b,c,horizon,e.term),eligible(b,c,horizon,e),
        0 <= time <= horizon,c.servers.contains(i),b[horizon].elections.contains(e),anchor(e.entries,b[time].nodes[i].log,start),
        old_configs(b[time].nodes[i].log,e.term)
    ensures lineage::adjacent(certificates::configuration(e,c),logs::configuration(b[time].nodes[i].log,c))
{
    let h=e.entries; let v=b[time].nodes[i].log; let first=logs::first_config(v,start);
    logs::first_config_properties(v,start); logs::first_parent(v,c,start);
    if last_config(h) == 0 {
        assert(certificates::configuration(e,c) == c.servers);
        if first < v.len() {
            lineage::adjacent_entry(b,c,horizon,e.term,time,i,first);
            no_next_after_change(b,c,horizon,e,time,i,first);
            logs::first_parent(v,c,first+1); logs::configuration_after_entry(v,c,first);
        }
    } else {
        let elected=elections::election_origin(b,c,horizon,e); let a=last_config(h) as int-1;
        types::last_config_valid(h); logs::before_last(h,start); logs::configuration_no_configs(h,c,start,a);
        elections::election_log(b,c,horizon,e);
        if first == v.len() { lineage::adjacent_entry(b,c,horizon,e.term,elected,e.server,a); }
        else {
            first_agrees(b,c,horizon,e,time,i,start); let next=logs::first_config(v,first+1);
            logs::first_config_properties(v,first+1); logs::first_parent(v,c,first+1); logs::configuration_after_entry(v,c,first);
            if next < v.len() {
                lineage::adjacent_entry(b,c,horizon,e.term,time,i,next);
                no_next_after_change(b,c,horizon,e,time,i,next);
                logs::first_parent(v,c,next+1); logs::configuration_after_entry(v,c,next);
            }
        }
    }
}
} // verus!
