//! Recover the actual log comparison that supplied a candidate's released vote.
use vstd::prelude::*;
use super::etcd::*;
use super::etcd_election as election;
use super::etcd_origins as origins;
use super::etcd_candidates as candidates;
use super::etcd_transmissions as events;
use super::temporal::Behavior;
verus! {
pub proof fn candidate_predecessor(s: LState,c: Constants,a: Action,i: int,t: nat)
    requires election::inductive(s,c),enabled(s,c,a),c.servers.contains(i),s.nodes[i].term >= t,
        apply(s,c,a).nodes[i].role == Role::Candidate,apply(s,c,a).nodes[i].term == t
    ensures s.nodes[i].role == Role::Candidate,s.nodes[i].term == t,s.nodes[i].log == apply(s,c,a).nodes[i].log
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
}
pub proof fn candidate_interval(b: Behavior<LState>,c: Constants,i: int,t: nat,lo: int,hi: int)
    requires election::safety_spec(b,c),c.servers.contains(i),0 <= lo <= hi,
        b[hi].nodes[i].role == Role::Candidate,b[hi].nodes[i].term == t,
        forall |r: int| lo <= r < hi ==> (#[trigger] b[r].nodes[i]).term >= t
    ensures b[lo].nodes[i].role == Role::Candidate,b[lo].nodes[i].term == t,b[lo].nodes[i].log == b[hi].nodes[i].log
    decreases hi-lo
{
    if hi > lo {
        let r=hi-1; events::step_valid(b,c,r); election::safety_at(b,c,r);
        assert(b[r].nodes[i].term >= t); candidate_predecessor(b[r],c,events::step(b,c,r),i,t);
        candidate_interval(b,c,i,t,lo,r);
    }
}
pub proof fn persisted_candidate_interval(b: Behavior<LState>,c: Constants,i: int,t: nat,lo: int,hi: int)
    requires election::safety_spec(b,c),c.servers.contains(i),0 <= lo <= hi,t <= b[lo].nodes[i].disk.term,
        b[hi].nodes[i].role == Role::Candidate,b[hi].nodes[i].term == t
    ensures b[lo].nodes[i].role == Role::Candidate,b[lo].nodes[i].term == t,b[lo].nodes[i].log == b[hi].nodes[i].log
{
    assert forall |r: int| lo <= r < hi implies (#[trigger] b[r].nodes[i]).term >= t by {
        events::disk_term_interval(b,c,i,lo,r); election::safety_at(b,c,r); assert(election::node_inv(b[r],c,i));
    }
    candidate_interval(b,c,i,t,lo,hi);
}
pub proof fn positive_creation(s: LState,c: Constants,a: Action,m: Message)
    requires enabled(s,c,a),s.pending.count(m) == 0,apply(s,c,a).pending.count(m) > 0,positive(m)
    ensures a == (Action::RequestVote { i: m.source,j: m.source }) && m.source == m.dest && s.nodes[m.source].role == Role::Candidate
        || exists |packet: Message| #![trigger up_to_date(s.nodes[m.source],packet.body->VoteRequest_last_term,packet.body->VoteRequest_last_index)] a == (Action::Receive { m: packet,how: Receive::VoteRequest })
            && packet.body is VoteRequest && packet.source == m.dest && packet.dest == m.source && packet.term == m.term
            && up_to_date(s.nodes[m.source],packet.body->VoteRequest_last_term,packet.body->VoteRequest_last_index)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    if let Action::Receive { m: packet,how } = a {
        assert(packet.body is VoteRequest && packet.source == m.dest && packet.dest == m.source && packet.term == m.term
            && up_to_date(s.nodes[m.source],packet.body->VoteRequest_last_term,packet.body->VoteRequest_last_index));
    }
}
pub proof fn grant_comparison(b: Behavior<LState>,c: Constants,k: int,v: Ballot,j: int,r: int,m: Message)
    requires election::safety_spec(b,c),0 <= j < r < k,b[k].votes.contains(v),b[r+1].votes.contains(v),positive(m),ballot(m) == v,
        b[k].nodes[v.candidate].role == Role::Candidate,b[k].nodes[v.candidate].term == v.term,
        b[j].pending.count(m) == 0,b[j].nodes[m.source].term == m.term,
        forall |p: int| j < p <= r ==> #[trigger] b[p].pending.count(m) > 0,
        events::step(b,c,r) == Action::Ready(v.voter)
    ensures b[j].nodes[v.voter].term == v.term,
        up_to_date(b[j].nodes[v.voter],last_term(b[k].nodes[v.candidate].log),b[k].nodes[v.candidate].log.len())
{
    events::step_valid(b,c,j); events::step_valid(b,c,r); let a=events::step(b,c,j);
    assert(b[j+1].pending.count(m) > 0); positive_creation(b[j],c,a,m);
    election::safety_at(b,c,k); assert(election::history_inv(b[k],c,v));
    election::safety_at(b,c,r+1); assert(election::history_inv(b[r+1],c,v));
    origins::safety_at(b,c,r+1); assert(origins::ballot_persisted(b[r+1],v));
    persisted_candidate_interval(b,c,v.candidate,v.term,r+1,k);
    reveal(apply); assert(b[r].nodes[v.candidate].role == Role::Candidate);
    assert(b[r].nodes[v.candidate].term == v.term && b[r].nodes[v.candidate].log == b[k].nodes[v.candidate].log);
    if a == (Action::RequestVote { i: m.source,j: m.source }) && m.source == m.dest {
        assert forall |p: int| j <= p < r implies (#[trigger] b[p].nodes[v.candidate]).term >= v.term by {
            if p == j { assert(b[j].nodes[m.source].term == m.term); }
            else { assert(b[p].pending.count(m) > 0); origins::safety_at(b,c,p); assert(origins::pending_terms(b[p],m)); }
        }
        candidate_interval(b,c,v.candidate,v.term,j,r);
    } else {
        let packet=choose |packet: Message| #![trigger up_to_date(b[j].nodes[m.source],packet.body->VoteRequest_last_term,packet.body->VoteRequest_last_index)] a == (Action::Receive { m: packet,how: Receive::VoteRequest })
            && packet.body is VoteRequest && packet.source == m.dest && packet.dest == m.source && packet.term == m.term
            && up_to_date(b[j].nodes[m.source],packet.body->VoteRequest_last_term,packet.body->VoteRequest_last_index);
        reveal(enabled); reveal(receive_enabled); assert(b[j].messages.count(packet) > 0);
        origins::safety_at(b,c,j); assert(origins::message_terms(b[j],packet));
        persisted_candidate_interval(b,c,v.candidate,v.term,j,k);
        candidates::safety_at(b,c,j); assert(candidates::request(b[j],packet));
    }
}
pub proof fn comparison(b: Behavior<LState>,c: Constants,k: int,v: Ballot) -> (j: int)
    requires election::safety_spec(b,c),k >= 0,b[k].votes.contains(v),
        b[k].nodes[v.candidate].role == Role::Candidate,b[k].nodes[v.candidate].term == v.term
    ensures 0 <= j < k,b[j].nodes[v.voter].term == v.term,
        up_to_date(b[j].nodes[v.voter],last_term(b[k].nodes[v.candidate].log),b[k].nodes[v.candidate].log.len())
{
    let w=events::vote_origin(b,c,k,v); let j=events::pending_origin(b,c,w.0,w.1);
    grant_comparison(b,c,k,v,j,w.0,w.1); j
}
pub proof fn election_vote(b: Behavior<LState>,c: Constants,k: int,i: int,v: int) -> (j: int)
    requires election::safety_spec(b,c),k >= 0,c.servers.contains(i),b[k].nodes[i].role == Role::Candidate,b[k].nodes[i].granted.contains(v)
    ensures 0 <= j < k,b[j].nodes[v].term == b[k].nodes[i].term,
        up_to_date(b[j].nodes[v],last_term(b[k].nodes[i].log),b[k].nodes[i].log.len())
{
    election::safety_at(b,c,k); assert(election::node_inv(b[k],c,i));
    comparison(b,c,k,Ballot { voter: v,term: b[k].nodes[i].term,candidate: i })
}
} // verus!
