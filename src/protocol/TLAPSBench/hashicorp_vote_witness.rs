//! Vote certificates carry actual log comparisons from the recorded behavior.
//! Deferred votes retain the compared log until the response is released.
use vstd::prelude::*;
use super::hashicorp::*;
use super::hashicorp_config as configs;
use super::hashicorp_types as types;
use super::hashicorp_votes::{self as votes,ProofState,Ballot};
use super::hashicorp_order as order;
use super::hashicorp_certificates as certificates;
use super::hashicorp_history::{self as history,step};
use super::temporal::Behavior;
verus! {
pub open spec fn trace(b: Behavior<LState>,c: Constants,time: int) -> ProofState
    decreases time
{
    if time <= 0 { votes::initial_proof(c) }
    else { votes::advance(trace(b,c,time-1),c,step(b,c,time-1)) }
}
pub proof fn trace_valid(b: Behavior<LState>,c: Constants,time: int)
    requires configs::safety_spec(b,c),time >= 0
    ensures trace(b,c,time).state == b[time],order::inductive(trace(b,c,time),c),certificates::inductive(trace(b,c,time),c)
    decreases time
{
    if time == 0 { order::initial_inductive(c); certificates::initial_inductive(c); }
    else {
        let p=time-1; trace_valid(b,c,p); history::step_valid(b,c,p);
        order::preserve(trace(b,c,p),c,step(b,c,p)); certificates::preserve(trace(b,c,p),c,step(b,c,p));
    }
}
pub proof fn released_origin(b: Behavior<LState>,c: Constants,time: int,v: Ballot) -> (at: int)
    requires configs::safety_spec(b,c),time >= 0,trace(b,c,time).votes.contains(v)
    ensures 0 <= at < time,enabled(b[at],c,step(b,c,at)),votes::released(b[at],step(b,c,at)).contains(v)
    decreases time
{
    if time == 0 { assert(false); 0 }
    else {
        let p=time-1;
        if trace(b,c,p).votes.contains(v) { released_origin(b,c,p,v) }
        else { trace_valid(b,c,p); history::step_valid(b,c,p); p }
    }
}
pub proof fn pending_step(g: ProofState,c: Constants,a: Action,i: int)
    requires order::inductive(g,c),enabled(g.state,c,a),c.servers.contains(i),g.state.nodes[i].pending_vote is Some,
        apply(g.state,c,a).nodes[i].pending_vote is Some
    ensures apply(g.state,c,a).nodes[i].pending_vote == g.state.nodes[i].pending_vote,
        apply(g.state,c,a).nodes[i].log == g.state.nodes[i].log
{
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
    let s=g.state; assert(votes::node(s.nodes[i],i));
    if let Action::Receive { m,how } = a {
        assert(order::message(s,m));
        if m.dest == i && how == Receive::AcceptAppend { reveal(merge); }
    }
}
pub proof fn pending_origin(b: Behavior<LState>,c: Constants,time: int,i: int) -> (at: int)
    requires configs::safety_spec(b,c),time >= 0,c.servers.contains(i),b[time].nodes[i].pending_vote is Some
    ensures 0 <= at < time,step(b,c,at) is Receive,
        step(b,c,at)->Receive_how == Receive::DeferVote,
        step(b,c,at)->Receive_m.dest == i,
        step(b,c,at)->Receive_m.body is VoteRequest,
        step(b,c,at)->Receive_m.source == b[time].nodes[i].pending_vote.unwrap().candidate,
        step(b,c,at)->Receive_m.term == b[time].nodes[i].pending_vote.unwrap().term,
        b[at].nodes[i].log == b[time].nodes[i].log
    decreases time
{
    if time == 0 { assert(false); 0 }
    else {
        let p=time-1; history::step_valid(b,c,p); trace_valid(b,c,p); let a=step(b,c,p);
        if b[p].nodes[i].pending_vote is Some {
            pending_step(trace(b,c,p),c,a,i); pending_origin(b,c,p,i)
        } else {
            reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive); p
        }
    }
}
pub proof fn request_creation(s: LState,c: Constants,a: Action,m: Message)
    requires types::inductive(s,c),enabled(s,c,a),s.messages.count(m) == 0,apply(s,c,a).messages.count(m) > 0,m.body is VoteRequest
    ensures a == Action::Timeout(m.source),c.servers.contains(m.source),m.source != m.dest,
        m.term == s.nodes[m.source].term+1,
        m.body->VoteRequest_last_term == log_term(s.nodes[m.source].log,s.nodes[m.source].log.len() as int),
        m.body->VoteRequest_last_index == s.nodes[m.source].log.len(),
        apply(s,c,a).nodes[m.source].role == Role::Candidate,apply(s,c,a).nodes[m.source].term == m.term,
        apply(s,c,a).nodes[m.source].log == s.nodes[m.source].log
{
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    if let Action::Timeout(i) = a {
        let q=s.nodes[i].latest_config.remove(i).map(|j: int| Message { source: i,dest: j,term: s.nodes[i].term+1,body: Body::VoteRequest {
            last_term: log_term(s.nodes[i].log,s.nodes[i].log.len() as int),last_index: s.nodes[i].log.len() } });
        assert(q.contains(m));
    }
}
pub proof fn request_origin(b: Behavior<LState>,c: Constants,time: int,m: Message) -> (at: int)
    requires configs::safety_spec(b,c),time >= 0,b[time].messages.count(m) > 0,m.body is VoteRequest
    ensures 0 <= at < time,step(b,c,at) == Action::Timeout(m.source),c.servers.contains(m.source),m.source != m.dest,
        b[at+1].nodes[m.source].role == Role::Candidate,b[at+1].nodes[m.source].term == m.term,
        m.body->VoteRequest_last_term == log_term(b[at+1].nodes[m.source].log,b[at+1].nodes[m.source].log.len() as int),
        m.body->VoteRequest_last_index == b[at+1].nodes[m.source].log.len()
    decreases time
{
    if time == 0 { broadcast use vstd::multiset::group_multiset_axioms; assert(false); 0 }
    else {
        let p=time-1;
        if b[p].messages.count(m) > 0 { request_origin(b,c,p,m) }
        else { types::safety_at(b,c,p); history::step_valid(b,c,p); request_creation(b[p],c,step(b,c,p),m); p }
    }
}
pub struct Witness { pub release: int,pub check: int,pub request: Option<Message> }
pub open spec fn evidence(b: Behavior<LState>,c: Constants,v: Ballot,w: Witness) -> bool {
    0 <= w.check <= w.release
    && votes::released(b[w.release],step(b,c,w.release)).contains(v)
    && b[w.check].nodes[v.voter].log == b[w.release].nodes[v.voter].log
    && match w.request {
        None => w.check == w.release && step(b,c,w.check) == Action::Timeout(v.voter)
            && v.voter == v.candidate && v.term == b[w.check].nodes[v.voter].term+1,
        Some(m) => step(b,c,w.check) == Action::Receive { m,how: Receive::GrantVote }
            || step(b,c,w.check) == Action::Receive { m,how: Receive::DeferVote },
    }
    && match w.request {
        None => true,
        Some(m) => m.dest == v.voter && m.source == v.candidate && m.term == v.term && m.body is VoteRequest
            && b[w.check].messages.count(m) > 0 && b[w.check].nodes[v.voter].latest_config.contains(v.candidate)
            && up_to_date(b[w.check].nodes[v.voter].log,m.body->VoteRequest_last_term,m.body->VoteRequest_last_index),
    }
}
pub proof fn vote_origin(b: Behavior<LState>,c: Constants,time: int,v: Ballot) -> (w: Witness)
    requires configs::safety_spec(b,c),time >= 0,trace(b,c,time).votes.contains(v)
    ensures w.release < time,evidence(b,c,v,w)
{
    let release=released_origin(b,c,time,v); let a=step(b,c,release);
    reveal(enabled); reveal(receive_enabled);
    match a {
        Action::Timeout(i) => Witness { release,check: release,request: None },
        Action::Receive { m,how } => Witness { release,check: release,request: Some(m) },
        Action::CompleteVote(i) => {
            let check=pending_origin(b,c,release,i); history::step_valid(b,c,check); let m=step(b,c,check)->Receive_m;
            Witness { release,check,request: Some(m) }
        },
        _ => { assert(false); Witness { release,check: release,request: None } },
    }
}
} // verus!
