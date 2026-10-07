//! Election logs are exactly the logs advertised when their candidates timed out.
//! Every vote in an election certificate includes an actual voter log comparison.
use vstd::prelude::*;
use super::hashicorp::*;
use super::hashicorp_config as configs;
use super::hashicorp_types as types;
use super::hashicorp_votes::{self as votes,Ballot};
use super::hashicorp_order as order;
use super::hashicorp_history::{self as history,step};
use super::hashicorp_vote_witness::{self as witness,trace};
use super::hashicorp_certificates as certificates;
use super::temporal::Behavior;
verus! {
pub proof fn candidate_step(s: LState,c: Constants,a: Action,i: int)
    requires enabled(s,c,a),c.servers.contains(i),s.nodes[i].role == Role::Candidate,
        apply(s,c,a).nodes[i].role != Role::Follower,s.nodes[i].term == apply(s,c,a).nodes[i].term
    ensures s.nodes[i].log == apply(s,c,a).nodes[i].log
{ reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive); }
pub proof fn candidate_origin(b: Behavior<LState>,c: Constants,time: int,i: int) -> (at: int)
    requires configs::safety_spec(b,c),time >= 0,c.servers.contains(i),b[time].nodes[i].role == Role::Candidate
    ensures 0 <= at < time,step(b,c,at) == Action::Timeout(i),b[at].nodes[i].term+1 == b[time].nodes[i].term,
        b[at+1].nodes[i].log == b[time].nodes[i].log
    decreases time
{
    if time == 0 { assert(false); 0 }
    else {
        let p=time-1; history::step_valid(b,c,p); let a=step(b,c,p);
        if b[p].nodes[i].role == Role::Candidate && b[p].nodes[i].term == b[time].nodes[i].term {
            candidate_step(b[p],c,a,i); candidate_origin(b,c,p,i)
        } else {
            reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive); p
        }
    }
}
pub proof fn timeout_unique(b: Behavior<LState>,c: Constants,i: int,left: int,right: int)
    requires configs::safety_spec(b,c),c.servers.contains(i),left >= 0,right >= 0,
        step(b,c,left) == Action::Timeout(i),step(b,c,right) == Action::Timeout(i),
        b[left].nodes[i].term == b[right].nodes[i].term
    ensures left == right
{
    history::step_valid(b,c,left); history::step_valid(b,c,right); reveal(protocol_apply);
    if left < right { history::term_role_interval(b,c,i,left+1,right); assert(false); }
    if right < left { history::term_role_interval(b,c,i,right+1,left); assert(false); }
}
pub proof fn election_creation(s: LState,c: Constants,a: Action,e: Event)
    requires enabled(s,c,a),!s.elections.contains(e),apply(s,c,a).elections.contains(e)
    ensures a == Action::BecomeLeader(e.server),c.servers.contains(e.server),s.nodes[e.server].role == Role::Candidate,
        s.nodes[e.server].term == e.term,s.nodes[e.server].log == e.entries
{
    let u=apply(s,c,a); broadcast use Set::lemma_map_contains;
    let elected=c.servers.filter(|i: int| s.nodes[i].role != Role::Leader && u.nodes[i].role == Role::Leader);
    assert(elected.map(|i: int| Event { server: i,term: u.nodes[i].term,entries: u.nodes[i].log }).contains(e));
    assert(elected.contains(e.server)); assert(e == (Event { server: e.server,term: u.nodes[e.server].term,entries: u.nodes[e.server].log }));
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
}
pub proof fn election_origin(b: Behavior<LState>,c: Constants,time: int,e: Event) -> (at: int)
    requires configs::safety_spec(b,c),time >= 0,b[time].elections.contains(e)
    ensures 0 <= at < time,step(b,c,at) == Action::BecomeLeader(e.server),c.servers.contains(e.server),
        b[at].nodes[e.server].role == Role::Candidate,b[at].nodes[e.server].term == e.term,b[at].nodes[e.server].log == e.entries,
        !b[at].elections.contains(e),b[at+1].elections.contains(e)
    decreases time
{
    if time == 0 { assert(false); 0 }
    else {
        let p=time-1;
        if b[p].elections.contains(e) { election_origin(b,c,p,e) }
        else { history::step_valid(b,c,p); election_creation(b[p],c,step(b,c,p),e); p }
    }
}
pub proof fn request_matches_election(b: Behavior<LState>,c: Constants,time: int,m: Message,horizon: int,e: Event)
    requires configs::safety_spec(b,c),time >= 0,horizon >= 0,b[time].messages.count(m) > 0,m.body is VoteRequest,
        b[horizon].elections.contains(e),m.source == e.server,m.term == e.term
    ensures m.body->VoteRequest_last_index == e.entries.len(),m.body->VoteRequest_last_term == log_term(e.entries,e.entries.len() as int)
{
    let sent=witness::request_origin(b,c,time,m); let elected=election_origin(b,c,horizon,e);
    let begin=candidate_origin(b,c,elected,e.server);
    history::step_valid(b,c,sent); reveal(protocol_apply);
    timeout_unique(b,c,e.server,sent,begin);
}
pub proof fn election_log(b: Behavior<LState>,c: Constants,horizon: int,e: Event)
    requires configs::safety_spec(b,c),horizon >= 0,b[horizon].elections.contains(e)
    ensures order::ordered(e.entries),order::bounded(e.entries,e.term),log_term(e.entries,e.entries.len() as int) < e.term,
        forall |k: int| 0 <= k < e.entries.len() ==> (#[trigger] e.entries[k]).term < e.term
{
    let elected=election_origin(b,c,horizon,e); let g=order::safety_at(b,c,elected); assert(order::node(g.state.nodes[e.server]));
    assert forall |k: int| 0 <= k < e.entries.len() implies (#[trigger] e.entries[k]).term < e.term by {
        assert(e.entries[k].term <= e.entries[e.entries.len()-1].term);
    }
}
pub proof fn election_votes(b: Behavior<LState>,c: Constants,horizon: int,e: Event) -> (at: int)
    requires configs::safety_spec(b,c),horizon >= 0,b[horizon].elections.contains(e)
    ensures 0 <= at < horizon,certificates::certificate(trace(b,c,at),c,e),
        step(b,c,at) == Action::BecomeLeader(e.server),b[at].nodes[e.server].log == e.entries,
        b[at].nodes[e.server].role == Role::Candidate,b[at].nodes[e.server].term == e.term,
        !b[at].elections.contains(e),b[at+1].elections.contains(e)
{
    let at=election_origin(b,c,horizon,e); witness::trace_valid(b,c,at); history::step_valid(b,c,at);
    certificates::new_certificate(trace(b,c,at),c,step(b,c,at),e);
    assert(votes::released(b[at],step(b,c,at)).is_empty());
    assert(votes::advance(trace(b,c,at),c,step(b,c,at)).votes =~= trace(b,c,at).votes);
    at
}
pub proof fn voter_comparison(b: Behavior<LState>,c: Constants,time: int,horizon: int,e: Event,i: int) -> (at: int)
    requires configs::safety_spec(b,c),time >= 0,horizon >= 0,b[horizon].elections.contains(e),
        trace(b,c,time).votes.contains(Ballot { voter: i,candidate: e.server,term: e.term })
    ensures 0 <= at < time,c.servers.contains(i),
        up_to_date(b[at].nodes[i].log,log_term(e.entries,e.entries.len() as int),e.entries.len()),
        log_term(b[at].nodes[i].log,b[at].nodes[i].log.len() as int) < e.term,
        votes::released(b[at],step(b,c,at)).contains(Ballot { voter: i,candidate: e.server,term: e.term })
{
    let v=Ballot { voter: i,candidate: e.server,term: e.term }; let w=witness::vote_origin(b,c,time,v);
    witness::trace_valid(b,c,time); assert(votes::history(b[time],c,v)); election_log(b,c,horizon,e);
    if let Some(m)=w.request {
        request_matches_election(b,c,w.check,m,horizon,e);
    } else {
        let elected=election_origin(b,c,horizon,e); let begin=candidate_origin(b,c,elected,e.server);
        timeout_unique(b,c,e.server,w.check,begin); history::step_valid(b,c,begin); reveal(protocol_apply);
        assert(b[w.check].nodes[i].log == e.entries);
    }
    w.release
}
pub proof fn voter_check(b: Behavior<LState>,c: Constants,time: int,horizon: int,e: Event,i: int) -> (at: int)
    requires configs::safety_spec(b,c),time >= 0,horizon >= 0,b[horizon].elections.contains(e),
        trace(b,c,time).votes.contains(Ballot { voter: i,candidate: e.server,term: e.term })
    ensures 0 <= at < time,c.servers.contains(i),b[at].nodes[i].term <= e.term,b[at+1].nodes[i].term == e.term,
        up_to_date(b[at].nodes[i].log,log_term(e.entries,e.entries.len() as int),e.entries.len()),
        log_term(b[at].nodes[i].log,b[at].nodes[i].log.len() as int) < e.term
{
    let v=Ballot { voter: i,candidate: e.server,term: e.term }; let w=witness::vote_origin(b,c,time,v);
    witness::trace_valid(b,c,time); assert(votes::history(b[time],c,v)); election_log(b,c,horizon,e);
    if let Some(m)=w.request { request_matches_election(b,c,w.check,m,horizon,e); }
    else {
        let elected=election_origin(b,c,horizon,e); let begin=candidate_origin(b,c,elected,e.server);
        timeout_unique(b,c,e.server,w.check,begin); history::step_valid(b,c,begin); reveal(protocol_apply);
        assert(b[w.check].nodes[i].log == e.entries);
    }
    history::step_valid(b,c,w.check); reveal(enabled); reveal(receive_enabled); reveal(protocol_apply); reveal(receive);
    w.check
}
} // verus!
