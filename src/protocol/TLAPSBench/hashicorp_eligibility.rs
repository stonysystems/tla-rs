//! Election eligibility from shared voters, using earlier-term completeness
//! and completeness of same-term leaders observed before this election.
use vstd::prelude::*;
use super::hashicorp::*;
use super::hashicorp_config as configs;
use super::hashicorp_types as types;
use super::hashicorp_history::{self as history,step};
use super::hashicorp_replication as replication;
use super::hashicorp_prefixes as prefixes;
use super::hashicorp_commits as commits;
use super::hashicorp_retention::{self as retention,decision,decided,complete_below,compatible};
use super::hashicorp_candidates as candidates;
use super::hashicorp_election_trace as elections;
use super::hashicorp_election_reduction as leaders;
use super::hashicorp_vote_witness::{self as witness,trace};
use super::hashicorp_votes::Ballot;
use super::hashicorp_certificates as certificates;
use super::hashicorp_config_lineage as lineage;
use super::temporal::Behavior;
verus! {
pub open spec fn prior_complete(b: Behavior<LState>,c: Constants,horizon: int,term: nat,cut: int) -> bool {
    forall |at: int,i: int,time: int,j: int| 0 <= at < horizon && 0 <= time < cut
        && decision(b,c,at,i) && c.servers.contains(j) && (#[trigger] b[time].nodes[j]).role == Role::Leader
        && b[time].nodes[j].term == term && (#[trigger] b[at].nodes[i]).term < term
        ==> prefix(decided(b,at,i),b[time].nodes[j].log)
}
pub open spec fn eligible(b: Behavior<LState>,c: Constants,horizon: int,e: Event) -> bool {
    forall |at: int,i: int| 0 <= at < horizon && (#[trigger] decision(b,c,at,i)) && b[at].nodes[i].term < e.term
        && lineage::adjacent(b[at].nodes[i].latest_config,certificates::configuration(e,c))
        ==> prefix(decided(b,at,i),e.entries)
}
pub proof fn packet_compatible(b: Behavior<LState>,c: Constants,horizon: int,term: nat,cut: int,time: int,m: Message,at: int,i: int) -> (sent: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,term),complete_below(b,c,horizon,term),prior_complete(b,c,horizon,term,cut),
        0 <= time < cut <= horizon,0 <= at < horizon,decision(b,c,at,i),b[at].nodes[i].term < term,
        b[time].messages.count(m) > 0,m.body is AppendRequest,b[at].nodes[i].term <= m.term <= term
    ensures 0 <= sent < time,history::segment(m,b[sent].nodes[m.source].log),compatible(decided(b,at,i),b[sent].nodes[m.source].log)
{
    if m.term < term { retention::packet_compatible(b,c,horizon,term,time,m,at,i) }
    else {
        let sent=replication::request_bound(b,c,time,m); assert(prefix(decided(b,at,i),b[sent].nodes[m.source].log)); sent
    }
}
pub proof fn preserve(b: Behavior<LState>,c: Constants,horizon: int,term: nat,cut: int,time: int,j: int,at: int,i: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,term),complete_below(b,c,horizon,term),prior_complete(b,c,horizon,term,cut),
        0 <= time < cut <= horizon,0 <= at < horizon,decision(b,c,at,i),c.servers.contains(j),b[at].nodes[i].term < term,
        b[at].nodes[i].term <= b[time].nodes[j].term,b[time+1].nodes[j].term <= term,prefix(decided(b,at,i),b[time].nodes[j].log)
    ensures prefix(decided(b,at,i),b[time+1].nodes[j].log)
{
    history::step_valid(b,c,time); types::safety_at(b,c,time); let a=step(b,c,time); let h=decided(b,at,i);
    if let Action::Receive { m,how } = a {
        if m.dest == j && how == Receive::AcceptAppend {
            reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive); assert(types::message(m,c));
            let sent=packet_compatible(b,c,horizon,term,cut,time,m,at,i);
            retention::merge_retains(b[time].nodes[j].log,m,b[sent].nodes[m.source].log,h);
        }
    }
    retention::local_prefix(b[time],c,a,j,h);
}
pub proof fn interval(b: Behavior<LState>,c: Constants,horizon: int,term: nat,cut: int,lo: int,hi: int,j: int,at: int,i: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,term),complete_below(b,c,horizon,term),prior_complete(b,c,horizon,term,cut),
        0 <= lo <= hi < cut <= horizon,0 <= at < horizon,decision(b,c,at,i),c.servers.contains(j),b[at].nodes[i].term < term,
        b[at].nodes[i].term <= b[lo].nodes[j].term,b[hi].nodes[j].term <= term,prefix(decided(b,at,i),b[lo].nodes[j].log)
    ensures prefix(decided(b,at,i),b[hi].nodes[j].log)
    decreases hi-lo
{
    if lo < hi {
        let p=hi-1; history::term_role_interval(b,c,j,lo,p); history::term_role_interval(b,c,j,p,hi);
        interval(b,c,horizon,term,cut,lo,p,j,at,i); preserve(b,c,horizon,term,cut,p,j,at,i);
    }
}
pub proof fn shared_voter_contains(b: Behavior<LState>,c: Constants,horizon: int,cut: int,e: Event,at: int,i: int,j: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,e.term),complete_below(b,c,horizon,e.term),prior_complete(b,c,horizon,e.term,cut),
        0 <= cut <= horizon,0 <= at < horizon,decision(b,c,at,i),b[at].nodes[i].term < e.term,b[horizon].elections.contains(e),
        c.servers.contains(e.server),b[cut].nodes[e.server].log == e.entries,
        trace(b,c,cut).votes.contains(Ballot { voter: j,candidate: e.server,term: e.term }),
        commits::voters(b[at].nodes[i],c,i,b[at+1].nodes[i].commit as int).contains(j)
    ensures prefix(decided(b,at,i),e.entries)
{
    let checked=elections::voter_check(b,c,cut,horizon,e,j); let received=commits::decision_voter(b,c,horizon,e.term,at,i,j);
    if checked < received { history::term_role_interval(b,c,j,checked+1,received); assert(false); }
    interval(b,c,horizon,e.term,cut,received,checked,j,at,i);
    elections::election_log(b,c,horizon,e);
    candidates::from_comparison(b,c,horizon,e.term,cut,e.server,checked,j,at,i);
}
pub proof fn eligible_election(b: Behavior<LState>,c: Constants,horizon: int,cut: int,e: Event)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,e.term),complete_below(b,c,horizon,e.term),prior_complete(b,c,horizon,e.term,cut),
        0 <= cut < horizon,!b[cut].elections.contains(e),b[cut+1].elections.contains(e)
    ensures eligible(b,c,horizon,e)
{
    history::step_valid(b,c,cut); elections::election_creation(b[cut],c,step(b,c,cut),e);
    let at=elections::election_votes(b,c,cut+1,e);
    if at < cut { leaders::election_history(b,c,at+1,cut); assert(false); }
    assert(at == cut); leaders::election_history(b,c,cut+1,horizon); assert(b[horizon].elections.contains(e));
    let g=trace(b,c,cut); let eq=certificates::voters(g,c,e).intersect(certificates::configuration(e,c));
    assert forall |d: int,i: int| 0 <= d < horizon && (#[trigger] decision(b,c,d,i)) && b[d].nodes[i].term < e.term
        && lineage::adjacent(b[d].nodes[i].latest_config,certificates::configuration(e,c)) implies prefix(decided(b,d,i),e.entries) by {
        commits::decision_certificate(b,c,d,i); let dq=commits::voters(b[d].nodes[i],c,i,b[d+1].nodes[i].commit as int);
        let j=lineage::adjacent_quorums(dq,eq,b[d].nodes[i].latest_config,certificates::configuration(e,c));
        assert(g.votes.contains(Ballot { voter: j,candidate: e.server,term: e.term }));
        shared_voter_contains(b,c,horizon,cut,e,d,i,j);
    }
}
} // verus!
