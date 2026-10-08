//! Reduce the remaining safety goals to unique leaders and completeness of
//! direct quorum decisions. Both hypotheses remain explicit and unproved here.
use vstd::prelude::*;
use super::hashicorp::{*,sub};
use super::hashicorp_config as configs;
use super::hashicorp_history::{self as history,step};
use super::hashicorp_election_trace as elections;
use super::hashicorp_election_reduction as matching;
use super::hashicorp_prefixes as prefixes;
use super::hashicorp_commits as commits;
use super::hashicorp_retention::{self as retention,decision,decided,complete_below,compatible};
use super::hashicorp_commit_trace as trace;
use super::temporal::Behavior;
verus! {
pub open spec fn bounded(b: Behavior<LState>,c: Constants,horizon: int,bound: nat) -> bool {
    forall |i: int| c.servers.contains(i) ==> (#[trigger] b[horizon].nodes[i]).term < bound
}
pub proof fn term_bound(b: Behavior<LState>,c: Constants,horizon: int) -> (bound: nat)
    requires configs::safety_spec(b,c),horizon >= 0
    ensures bounded(b,c,horizon,bound)
{
    broadcast use Set::lemma_map_contains;
    let terms=c.servers.map(|i: int| b[horizon].nodes[i].term as int);
    let i=c.servers.choose(); assert(terms.contains(b[horizon].nodes[i].term as int));
    commits::maximum_correct(terms); let bound=(maximum(terms)+1) as nat;
    assert forall |j: int| c.servers.contains(j) implies (#[trigger] b[horizon].nodes[j]).term < bound by {
        assert(terms.contains(b[horizon].nodes[j].term as int));
    }
    bound
}
pub proof fn commit_creation(s: LState,c: Constants,a: Action,e: Event)
    requires enabled(s,c,a),!s.commits.contains(e),apply(s,c,a).commits.contains(e)
    ensures c.servers.contains(e.server),apply(s,c,a).nodes[e.server].commit > s.nodes[e.server].commit,
        apply(s,c,a).nodes[e.server].term == e.term,e.entries == sub(apply(s,c,a).nodes[e.server].log,1,apply(s,c,a).nodes[e.server].commit as int)
{
    let u=apply(s,c,a); broadcast use Set::lemma_map_contains;
    let changed=c.servers.filter(|i: int| u.nodes[i].commit > s.nodes[i].commit);
    assert(changed.map(|i: int| Event { server: i,term: u.nodes[i].term,entries: sub(u.nodes[i].log,1,u.nodes[i].commit as int) }).contains(e));
    assert(changed.contains(e.server)); assert(e == (Event { server: e.server,term: u.nodes[e.server].term,entries: sub(u.nodes[e.server].log,1,u.nodes[e.server].commit as int) }));
}
pub proof fn commit_origin(b: Behavior<LState>,c: Constants,time: int,e: Event) -> (at: int)
    requires configs::safety_spec(b,c),time >= 0,b[time].commits.contains(e)
    ensures 0 <= at < time,c.servers.contains(e.server),b[at+1].nodes[e.server].commit > b[at].nodes[e.server].commit,
        b[at+1].nodes[e.server].term == e.term,e.entries == sub(b[at+1].nodes[e.server].log,1,b[at+1].nodes[e.server].commit as int)
    decreases time
{
    if time == 0 { assert(false); 0 }
    else {
        let p=time-1;
        if b[p].commits.contains(e) { commit_origin(b,c,p,e) }
        else { history::step_valid(b,c,p); commit_creation(b[p],c,step(b,c,p),e); p }
    }
}
pub proof fn commit_covered(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,e: Event) -> (origin: (int,int,int))
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),complete_below(b,c,horizon,bound),bounded(b,c,horizon,bound),
        horizon >= 0,b[horizon].commits.contains(e)
    ensures 0 <= origin.0 < horizon,0 <= origin.1 < origin.0+1,c.servers.contains(e.server),c.servers.contains(origin.2),
        b[origin.0+1].nodes[e.server].term == e.term,prefix(e.entries,b[origin.0+1].nodes[e.server].log),
        decision(b,c,origin.1,origin.2),b[origin.1].nodes[origin.2].term <= e.term < bound,
        prefix(e.entries,decided(b,origin.1,origin.2))
{
    let at=commit_origin(b,c,horizon,e); history::term_role_interval(b,c,e.server,at+1,horizon);
    let source=trace::coverage_at(b,c,horizon,bound,at+1,e.server); assert(trace::covered(b,c,at+1,e.server,source.0,source.1));
    (at,source.0,source.1)
}
pub proof fn leader_view(b: Behavior<LState>,c: Constants,horizon: int,e: Event) -> (at: int)
    requires configs::safety_spec(b,c),horizon >= 0,b[horizon].elections.contains(e)
    ensures 0 <= at < horizon,c.servers.contains(e.server),b[at+1].nodes[e.server].role == Role::Leader,
        b[at+1].nodes[e.server].term == e.term,b[at+1].nodes[e.server].log == e.entries
{
    let at=elections::election_origin(b,c,horizon,e); history::step_valid(b,c,at); reveal(protocol_apply); at
}
pub proof fn decisions_compatible(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,left: int,i: int,right: int,j: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),complete_below(b,c,horizon,bound),
        0 <= left < horizon,0 <= right < horizon,decision(b,c,left,i),decision(b,c,right,j),
        b[left].nodes[i].term < bound,b[right].nodes[j].term < bound
    ensures compatible(decided(b,left,i),decided(b,right,j))
{
    commits::decision_certificate(b,c,left,i); commits::decision_certificate(b,c,right,j);
    let a=decided(b,left,i); let d=decided(b,right,j); let x=b[left].nodes[i].log; let y=b[right].nodes[j].log;
    assert(prefix(a,x)); assert(prefix(d,y));
    if b[left].nodes[i].term < b[right].nodes[j].term {
        assert(prefix(a,y)); retention::prefixes_compatible(a,d,y);
    } else if b[right].nodes[j].term < b[left].nodes[i].term {
        assert(prefix(d,x)); retention::prefixes_compatible(a,d,x);
    } else {
        assert(i == j);
        if left <= right { history::continuous(b,c,i,left,right); retention::transitive(a,x,y); retention::prefixes_compatible(a,d,y); }
        else { history::continuous(b,c,i,right,left); retention::transitive(d,y,x); retention::prefixes_compatible(a,d,x); }
    }
}
pub proof fn preserved_event(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,e: Event)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),complete_below(b,c,horizon,bound),bounded(b,c,horizon,bound),
        horizon >= 0,b[horizon].commits.contains(e)
    ensures prefix(e.entries,b[horizon].nodes[e.server].log)
{
    let origin=commit_covered(b,c,horizon,bound,e); let h=decided(b,origin.1,origin.2);
    assert(sub(h,1,e.entries.len() as int) == e.entries);
    retention::interval(b,c,horizon,bound,origin.0+1,horizon,e.server,origin.1,origin.2,e.entries.len() as int);
}
pub proof fn complete_pair(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,committed: Event,elected: Event)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),complete_below(b,c,horizon,bound),bounded(b,c,horizon,bound),
        horizon >= 0,b[horizon].commits.contains(committed),b[horizon].elections.contains(elected),committed.term < elected.term
    ensures prefix(committed.entries,elected.entries)
{
    let origin=commit_covered(b,c,horizon,bound,committed); let at=leader_view(b,c,horizon,elected);
    history::term_role_interval(b,c,elected.server,at+1,horizon);
    let d=decided(b,origin.1,origin.2); assert(prefix(d,b[at+1].nodes[elected.server].log));
    retention::transitive(committed.entries,d,elected.entries);
}
pub proof fn agreement_pair(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,a: Event,d: Event)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),complete_below(b,c,horizon,bound),bounded(b,c,horizon,bound),
        horizon >= 0,b[horizon].commits.contains(a),b[horizon].commits.contains(d)
    ensures compatible(a.entries,d.entries)
{
    let x=commit_covered(b,c,horizon,bound,a); let y=commit_covered(b,c,horizon,bound,d);
    decisions_compatible(b,c,horizon,bound,x.1,x.2,y.1,y.2);
    let dx=decided(b,x.1,x.2); let dy=decided(b,y.1,y.2);
    retention::compatible_prefix(a.entries,dx,dy); retention::compatible_prefix(d.entries,dy,a.entries);
}
pub proof fn benchmark_reduction(b: Behavior<LState>,c: Constants,horizon: int,bound: nat)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),complete_below(b,c,horizon,bound),bounded(b,c,horizon,bound),horizon >= 0
    ensures election_safety(b[horizon]),log_matching(b[horizon],c),leader_completeness(b[horizon]),state_machine_safety(b[horizon]),committed_preserved(b[horizon])
{
    assert forall |a: Event,d: Event| #![trigger b[horizon].elections.contains(a), b[horizon].elections.contains(d)] b[horizon].elections.contains(a) && b[horizon].elections.contains(d) && a.term == d.term implies a.server == d.server by {
        let x=leader_view(b,c,horizon,a); let y=leader_view(b,c,horizon,d); history::term_role_interval(b,c,a.server,x+1,horizon);
        assert(b[x+1].nodes[a.server].term < bound);
    }
    matching::log_matching_from_election_safety(b,c,horizon);
    assert forall |a: Event| #![trigger b[horizon].commits.contains(a)] b[horizon].commits.contains(a) implies prefix(a.entries,b[horizon].nodes[a.server].log) by { preserved_event(b,c,horizon,bound,a); }
    assert forall |a: Event,d: Event| b[horizon].commits.contains(a) && b[horizon].commits.contains(d) implies prefix(a.entries,d.entries) || prefix(d.entries,a.entries) by {
        agreement_pair(b,c,horizon,bound,a,d);
    }
    assert forall |a: Event,e: Event| (#[trigger] b[horizon].commits.contains(a)) && (#[trigger] b[horizon].elections.contains(e)) && a.term < e.term
        implies prefix(a.entries,e.entries) by {
        complete_pair(b,c,horizon,bound,a,e);
    }
}
} // verus!
