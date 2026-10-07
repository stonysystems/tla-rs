//! Released vote history, including self votes and deferred vote persistence.
//! The history is passive; neither the protocol nor its guards read it.
use vstd::prelude::*;
use super::hashicorp::*;
use super::hashicorp_config as configs;
use super::hashicorp_types as types;
use super::temporal::Behavior;
verus! {
pub struct Ballot { pub voter: int,pub candidate: int,pub term: nat }
pub struct ProofState { pub state: LState,pub votes: Set<Ballot> }
pub open spec fn positive(m: Message) -> bool { m.body == Body::VoteResponse { granted: true } }
pub open spec fn ballot(m: Message) -> Ballot { Ballot { voter: m.source,candidate: m.dest,term: m.term } }
pub open spec fn released(s: LState,a: Action) -> Set<Ballot> {
    match a {
        Action::Timeout(i) => set![Ballot { voter: i,candidate: i,term: s.nodes[i].term+1 }],
        Action::CompleteVote(i) => set![Ballot { voter: i,candidate: s.nodes[i].pending_vote.unwrap().candidate,term: s.nodes[i].pending_vote.unwrap().term }],
        Action::Receive { m,how: Receive::GrantVote } => set![Ballot { voter: m.dest,candidate: m.source,term: s.nodes[m.dest].term }],
        _ => Set::empty(),
    }
}
pub open spec fn initial_proof(c: Constants) -> ProofState { ProofState { state: initial(c),votes: Set::empty() } }
pub open spec fn advance(g: ProofState,c: Constants,a: Action) -> ProofState {
    ProofState { state: apply(g.state,c,a),votes: g.votes.union(released(g.state,a)) }
}
pub open spec fn node(n: LServer,i: int) -> bool {
    n.term == n.persisted_term && n.persisted_vote_term <= n.term
    && (n.persisted_vote_term == n.term && n.persisted_voted_for is Some ==> n.voted_for == n.persisted_voted_for)
    && (n.pending_vote is Some ==> {
        let v=n.pending_vote.unwrap(); n.persisted_vote_term < v.term <= n.term && n.role == Role::Follower
        && (v.term == n.term ==> n.voted_for == Some(v.candidate))
    })
    && (n.role != Role::Follower ==> n.term > 0 && n.pending_vote is None && n.voted_for == Some(i)
        && n.persisted_vote_term == n.term && n.persisted_voted_for == Some(i))
}
pub open spec fn history(s: LState,c: Constants,b: Ballot) -> bool {
    c.servers.contains(b.voter) && c.servers.contains(b.candidate)
    && b.term <= s.nodes[b.voter].persisted_vote_term
    && (b.term == s.nodes[b.voter].persisted_vote_term ==> s.nodes[b.voter].persisted_voted_for == Some(b.candidate))
}
pub open spec fn compatible(a: Ballot,b: Ballot) -> bool { a.voter == b.voter && a.term == b.term ==> a.candidate == b.candidate }
pub open spec fn granted(g: ProofState,i: int) -> bool {
    let n=g.state.nodes[i]; n.role != Role::Follower ==> forall |j: int| n.granted.contains(j) ==> #[trigger] g.votes.contains(Ballot { voter: j,candidate: i,term: n.term })
}
pub open spec fn inductive(g: ProofState,c: Constants) -> bool {
    types::inductive(g.state,c)
    && (forall |i: int| c.servers.contains(i) ==> #[trigger] node(g.state.nodes[i],i) && granted(g,i))
    && (forall |b: Ballot| g.votes.contains(b) ==> #[trigger] history(g.state,c,b))
    && (forall |a: Ballot,b: Ballot| g.votes.contains(a) && g.votes.contains(b) ==> #[trigger] compatible(a,b))
    && (forall |m: Message| #[trigger] g.state.messages.count(m) > 0 && positive(m) ==> g.votes.contains(ballot(m)))
}
pub proof fn initial_inductive(c: Constants)
    requires valid_constants(c)
    ensures inductive(initial_proof(c),c)
{ types::initial_inductive(c); broadcast use vstd::multiset::group_multiset_axioms; }
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires node(s.nodes[i],i),enabled(s,c,a),c.servers.contains(i)
    ensures node(apply(s,c,a).nodes[i],i)
{
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
    if let Action::Receive { m,how } = a {
        match how {
            Receive::DropStale => {}, Receive::FollowerRejectVote => {}, Receive::RefuseVote => {},
            Receive::GrantVote => {}, Receive::DeferVote => {}, Receive::VoteResponse => {},
            Receive::StaleAppend => {}, Receive::RejectAppend => {}, Receive::AcceptAppend => {},
            Receive::ReplicateResponse => {}, Receive::HeartbeatResponse => {},
        }
    }
}
pub proof fn preserve_history(g: ProofState,c: Constants,a: Action,b: Ballot)
    requires inductive(g,c),enabled(g.state,c,a),advance(g,c,a).votes.contains(b)
    ensures history(advance(g,c,a).state,c,b)
{
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
    let s=g.state;
    if g.votes.contains(b) { assert(history(s,c,b)); assert(node(s.nodes[b.voter],b.voter)); }
    if let Action::Receive { m,how } = a { assert(types::message(m,c)); assert(node(s.nodes[m.dest],m.dest)); }
    if let Action::CompleteVote(i) = a { assert(types::node(s.nodes[i],c)); }
}
pub proof fn released_compatible(g: ProofState,c: Constants,a: Action,b: Ballot,v: Ballot)
    requires inductive(g,c),enabled(g.state,c,a),g.votes.contains(b),released(g.state,a).contains(v)
    ensures compatible(b,v)
{
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
    let s=g.state; assert(history(s,c,b)); assert(node(s.nodes[b.voter],b.voter));
}
pub proof fn preserve_pair(g: ProofState,c: Constants,a: Action,b: Ballot,v: Ballot)
    requires inductive(g,c),enabled(g.state,c,a),advance(g,c,a).votes.contains(b),advance(g,c,a).votes.contains(v)
    ensures compatible(b,v)
{
    if g.votes.contains(b) && g.votes.contains(v) { assert(compatible(b,v)); }
    else if g.votes.contains(b) { released_compatible(g,c,a,b,v); }
    else if g.votes.contains(v) { released_compatible(g,c,a,v,b); }
    else { assert(b == v); }
}
pub proof fn preserve_message(g: ProofState,c: Constants,a: Action,m: Message)
    requires inductive(g,c),enabled(g.state,c,a),advance(g,c,a).state.messages.count(m) > 0,positive(m)
    ensures advance(g,c,a).votes.contains(ballot(m))
{
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    let s=g.state; let u=advance(g,c,a);
    if s.messages.count(m) > 0 { assert(g.votes.contains(ballot(m))); }
    else if let Action::Timeout(i) = a {
        let q=s.nodes[i].latest_config.remove(i).map(|j: int| Message { source: i,dest: j,term: s.nodes[i].term+1,body: Body::VoteRequest {
            last_term: log_term(s.nodes[i].log,s.nodes[i].log.len() as int),last_index: s.nodes[i].log.len() } });
        assert(q.contains(m)); assert(false);
    } else { assert(released(s,a).contains(ballot(m))); }
}
pub proof fn preserve_granted(g: ProofState,c: Constants,a: Action,i: int)
    requires inductive(g,c),enabled(g.state,c,a),c.servers.contains(i)
    ensures granted(advance(g,c,a),i)
{
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
    let s=g.state; let u=advance(g,c,a); let n=s.nodes[i]; let v=u.state.nodes[i]; assert(node(n,i)); assert(granted(g,i));
    assert forall |j: int| v.role != Role::Follower && v.granted.contains(j) implies #[trigger] u.votes.contains(Ballot { voter: j,candidate: i,term: v.term }) by {
        if a == Action::Timeout(i) { assert(released(s,a).contains(Ballot { voter: j,candidate: i,term: v.term })); }
        else if n.role != Role::Follower && n.granted.contains(j) && n.term == v.term {
            assert(g.votes.contains(Ballot { voter: j,candidate: i,term: v.term }));
        } else if let Action::Receive { m,how } = a {
            assert(positive(m)); assert(g.votes.contains(ballot(m)));
        }
    }
}
pub proof fn preserve(g: ProofState,c: Constants,a: Action)
    requires inductive(g,c),enabled(g.state,c,a)
    ensures inductive(advance(g,c,a),c)
{
    types::preserve(g.state,c,a); let u=advance(g,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u.state.nodes[i],i) && granted(u,i) by { preserve_node(g.state,c,a,i); preserve_granted(g,c,a,i); }
    assert forall |b: Ballot| u.votes.contains(b) implies #[trigger] history(u.state,c,b) by { preserve_history(g,c,a,b); }
    assert forall |b: Ballot,v: Ballot| u.votes.contains(b) && u.votes.contains(v) implies #[trigger] compatible(b,v) by { preserve_pair(g,c,a,b,v); }
    assert forall |m: Message| #[trigger] u.state.messages.count(m) > 0 && positive(m) implies u.votes.contains(ballot(m)) by { preserve_message(g,c,a,m); }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,time: int) -> (g: ProofState)
    requires configs::safety_spec(b,c),time >= 0
    ensures g.state == b[time],inductive(g,c)
    decreases time
{
    if time == 0 { initial_inductive(c); initial_proof(c) }
    else {
        let g=safety_at(b,c,time-1); let p=time-1; assert(next(b[p],b[p+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[time-1],c,a) && b[time] == apply(b[time-1],c,a);
        preserve(g,c,a); advance(g,c,a)
    }
}
} // verus!
