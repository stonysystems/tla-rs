//! Turn the voting log comparison into prefix inclusion using earlier-term
//! leader completeness. The term-induction hypotheses remain explicit.
use vstd::prelude::*;
use super::hashicorp::{*,sub};
use super::hashicorp_config as configs;
use super::hashicorp_order as order;
use super::hashicorp_history::{self as history,step};
use super::hashicorp_prefixes as prefixes;
use super::hashicorp_commits as commits;
use super::hashicorp_retention::{self as retention,decision,decided,complete_below};
use super::temporal::Behavior;
verus! {
pub proof fn created_extends(b: Behavior<LState>,c: Constants,at: int,i: int,k: int,e: Entry)
    requires configs::safety_spec(b,c),at >= 0,history::created(b,c,at,i,k,e)
    ensures prefix(b[at].nodes[i].log,b[at+1].nodes[i].log),b[at+1].nodes[i].role == Role::Leader,b[at+1].nodes[i].term == e.term
{
    history::step_valid(b,c,at); reveal(protocol_apply);
    assert(sub(b[at+1].nodes[i].log,1,b[at].nodes[i].log.len() as int) =~= b[at].nodes[i].log);
}
pub proof fn ordered_creations(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,left: int,i: int,k: int,e: Entry,right: int,j: int,q: int,f: Entry)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),0 <= left < horizon,0 <= right < horizon,
        history::created(b,c,left,i,k,e),history::created(b,c,right,j,q,f),e.term == f.term,e.term < bound,k <= q
    ensures i == j,left <= right,prefix(b[left+1].nodes[i].log,b[right+1].nodes[j].log)
{
    assert(i == j); created_extends(b,c,left,i,k,e); created_extends(b,c,right,j,q,f);
    if right < left { history::continuous(b,c,i,right+1,left); assert(false); }
    history::continuous(b,c,i,left+1,right+1);
}
pub proof fn same_last_term(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,left: int,i: int,right: int,j: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),0 <= left <= horizon,0 <= right <= horizon,c.servers.contains(i),c.servers.contains(j),
        0 < b[left].nodes[i].log.len() <= b[right].nodes[j].log.len(),
        log_term(b[left].nodes[i].log,b[left].nodes[i].log.len() as int) == log_term(b[right].nodes[j].log,b[right].nodes[j].log.len() as int),
        log_term(b[left].nodes[i].log,b[left].nodes[i].log.len() as int) < bound
    ensures prefix(b[left].nodes[i].log,b[right].nodes[j].log)
{
    let h=b[left].nodes[i].log; let v=b[right].nodes[j].log; let k=h.len() as int-1; let q=v.len() as int-1;
    let a=prefixes::prefix_origin(b,c,horizon,bound,left,i,k); let d=prefixes::prefix_origin(b,c,horizon,bound,right,j,q);
    ordered_creations(b,c,horizon,bound,a.0,a.1,k,h[k],d.0,d.1,q,v[q]);
    assert(sub(h,1,h.len() as int) =~= h); assert(sub(v,1,v.len() as int) =~= v);
}
pub proof fn from_comparison(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,time: int,i: int,vote: int,j: int,at: int,writer: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),complete_below(b,c,horizon,bound),
        0 <= time <= horizon,0 <= vote <= horizon,0 <= at < horizon,c.servers.contains(i),c.servers.contains(j),decision(b,c,at,writer),
        prefix(decided(b,at,writer),b[vote].nodes[j].log),
        log_term(b[time].nodes[i].log,b[time].nodes[i].log.len() as int) < bound,
        up_to_date(b[vote].nodes[j].log,log_term(b[time].nodes[i].log,b[time].nodes[i].log.len() as int),b[time].nodes[i].log.len())
    ensures prefix(decided(b,at,writer),b[time].nodes[i].log)
{
    commits::decision_certificate(b,c,at,writer); let h=decided(b,at,writer); let candidate=b[time].nodes[i].log; let voter=b[vote].nodes[j].log;
    let g=order::safety_at(b,c,vote); assert(order::node(g.state.nodes[j]));
    assert(h.len() > 0 && h.len() <= voter.len());
    assert(h[h.len()-1] == voter[h.len()-1]); assert(h[h.len()-1] == b[at].nodes[writer].log[h.len()-1]);
    assert(voter[h.len()-1].term <= voter[voter.len()-1].term);
    assert(b[at].nodes[writer].term <= log_term(voter,voter.len() as int));
    if log_term(candidate,candidate.len() as int) == log_term(voter,voter.len() as int) {
        same_last_term(b,c,horizon,bound,vote,j,time,i); retention::transitive(h,voter,candidate);
    } else {
        assert(candidate.len() > 0); let k=candidate.len() as int-1;
        let origin=prefixes::prefix_origin(b,c,horizon,bound,time,i,k); let created=origin.0; let source=origin.1;
        assert(b[at].nodes[writer].term < b[created].nodes[source].term < bound);
        assert(prefix(h,b[created].nodes[source].log)); created_extends(b,c,created,source,k,candidate[k]);
        retention::transitive(h,b[created].nodes[source].log,b[created+1].nodes[source].log);
        assert(sub(candidate,1,candidate.len() as int) =~= candidate);
    }
}
} // verus!
