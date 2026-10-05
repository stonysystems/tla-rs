//! Every configuration entry has a prior current-term commit in its parent
//! configuration. All facts are conditional on the earlier-term induction.
use vstd::prelude::*;
use super::hashicorp::{*,sub};
use super::hashicorp_config as configs;
use super::hashicorp_types as types;
use super::hashicorp_history as history;
use super::hashicorp_prefixes as prefixes;
use super::hashicorp_candidates as candidates;
use super::hashicorp_commits as commits;
use super::hashicorp_config_lineage as lineage;
use super::hashicorp_config_commit as commit;
use super::hashicorp_config_logs as logs;
use super::hashicorp_retention::{self as retention,decision,decided,complete_below};
use super::temporal::Behavior;
verus! {
pub proof fn barrier_for_entry(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,time: int,i: int,k: int) -> (origin: (int,int))
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),complete_below(b,c,horizon,bound),
        0 <= time <= horizon,c.servers.contains(i),0 <= k < b[time].nodes[i].log.len(),
        b[time].nodes[i].log[k].kind == EntryKind::Config,b[time].nodes[i].log[k].term < bound
    ensures 0 <= origin.0 < time,decision(b,c,origin.0,origin.1),c.servers.contains(origin.1),
        b[origin.0].nodes[origin.1].term == b[time].nodes[i].log[k].term,
        b[origin.0].nodes[origin.1].latest_config == lineage::parent(b[time].nodes[i].log,k,c),
        prefix(decided(b,origin.0,origin.1),sub(b[time].nodes[i].log,1,k)),
        0 < decided(b,origin.0,origin.1).len() <= k,
        log_term(decided(b,origin.0,origin.1),decided(b,origin.0,origin.1).len() as int) == b[time].nodes[i].log[k].term,
        logs::configuration(decided(b,origin.0,origin.1),c) == lineage::parent(b[time].nodes[i].log,k,c),
        last_config(sub(b[time].nodes[i].log,1,k)) <= decided(b,origin.0,origin.1).len()
{
    let edge=lineage::configuration_origin(b,c,horizon,bound,time,i,k); let at=commit::proposal_certificate(b,c,horizon,bound,edge.at,edge.server,edge.member);
    let n=b[edge.at].nodes[edge.server]; let h=decided(b,at,edge.server);
    types::safety_at(b,c,edge.at); configs::safety_at(b,c,edge.at); assert(types::node(n,c)); assert(configs::node_inv(n));
    commits::decision_certificate(b,c,at,edge.server);
    logs::configuration_prefix(n.log,c,n.commit as int); assert(prefix(h,n.log));
    (at,edge.server)
}
pub proof fn same_term_first(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,left: int,i: int,right: int,j: int,start: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),0 <= left <= horizon,0 <= right <= horizon,
        c.servers.contains(i),c.servers.contains(j),0 <= start <= b[left].nodes[i].log.len(),start <= b[right].nodes[j].log.len(),
        logs::first_config(b[left].nodes[i].log,start) < b[left].nodes[i].log.len(),logs::first_config(b[right].nodes[j].log,start) < b[right].nodes[j].log.len(),
        b[left].nodes[i].log[logs::first_config(b[left].nodes[i].log,start)].term == b[right].nodes[j].log[logs::first_config(b[right].nodes[j].log,start)].term,
        b[left].nodes[i].log[logs::first_config(b[left].nodes[i].log,start)].term < bound
    ensures logs::first_config(b[left].nodes[i].log,start) == logs::first_config(b[right].nodes[j].log,start),
        b[left].nodes[i].log[logs::first_config(b[left].nodes[i].log,start)] == b[right].nodes[j].log[logs::first_config(b[right].nodes[j].log,start)]
{
    let h=b[left].nodes[i].log; let v=b[right].nodes[j].log; let k=logs::first_config(h,start); let q=logs::first_config(v,start);
    logs::first_config_properties(h,start); logs::first_config_properties(v,start);
    let a=prefixes::prefix_origin(b,c,horizon,bound,left,i,k); let d=prefixes::prefix_origin(b,c,horizon,bound,right,j,q);
    if k < q {
        candidates::ordered_creations(b,c,horizon,bound,a.0,a.1,k,h[k],d.0,d.1,q,v[q]);
        assert(sub(v,1,q+1)[k] == sub(h,1,k+1)[k]); assert(v[k].kind == EntryKind::Config); assert(false);
    } else if q < k {
        candidates::ordered_creations(b,c,horizon,bound,d.0,d.1,q,v[q],a.0,a.1,k,h[k]);
        assert(sub(h,1,k+1)[q] == sub(v,1,q+1)[q]); assert(h[q].kind == EntryKind::Config); assert(false);
    }
    prefixes::same_creation(b,c,horizon,bound,a.0,d.0,a.1,d.1,k,h[k],v[q]);
}
} // verus!
