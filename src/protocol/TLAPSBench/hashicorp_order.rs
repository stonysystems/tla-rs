//! Ordered log terms and the candidate log advertised by each vote request.
use vstd::prelude::*;
use super::hashicorp::{*,sub};
use super::hashicorp_config as configs;
use super::hashicorp_types as types;
use super::hashicorp_votes::{self as votes,ProofState};
use super::temporal::Behavior;
verus! {
pub open spec fn ordered(h: Seq<Entry>) -> bool {
    forall |i: int,j: int| 0 <= i <= j < h.len() ==> (#[trigger] h[i]).term <= (#[trigger] h[j]).term
}
pub open spec fn bounded(h: Seq<Entry>,t: nat) -> bool {
    forall |k: int| 0 <= k < h.len() ==> 0 < (#[trigger] h[k]).term <= t
}
pub open spec fn node(n: LServer) -> bool {
    ordered(n.log) && bounded(n.log,n.term)
    && (n.role == Role::Candidate ==> log_term(n.log,n.log.len() as int) < n.term)
}
pub open spec fn message(s: LState,m: Message) -> bool {
    m.term <= s.nodes[m.source].term && match m.body {
        Body::AppendRequest { mode,prev,prev_term,entries,commit } => ordered(entries) && bounded(entries,m.term) && prev_term <= m.term
            && (mode == Mode::Heartbeat ==> prev == 0 && prev_term == 0 && entries.len() == 0 && commit == 0)
            && forall |k: int| 0 <= k < entries.len() ==> prev_term <= (#[trigger] entries[k]).term,
        Body::VoteRequest { last_term,.. } => last_term < m.term,
        _ => true,
    }
}
pub open spec fn advertisement(s: LState,m: Message) -> bool {
    m.body is VoteRequest && s.nodes[m.source].role == Role::Candidate && s.nodes[m.source].term == m.term ==>
        m.body->VoteRequest_last_term == log_term(s.nodes[m.source].log,s.nodes[m.source].log.len() as int)
        && m.body->VoteRequest_last_index == s.nodes[m.source].log.len()
}
pub open spec fn inductive(g: ProofState,c: Constants) -> bool {
    votes::inductive(g,c)
    && (forall |i: int| c.servers.contains(i) ==> #[trigger] node(g.state.nodes[i]))
    && (forall |m: Message| #[trigger] g.state.messages.count(m) > 0 ==> message(g.state,m) && advertisement(g.state,m))
}
pub proof fn merge_order(n: LServer,m: Message)
    requires node(n),m.body is AppendRequest,m.term >= n.term,m.body->AppendRequest_prev >= 0,
        ordered(m.body->AppendRequest_entries),bounded(m.body->AppendRequest_entries,m.term),
        forall |k: int| 0 <= k < m.body->AppendRequest_entries.len() ==> m.body->AppendRequest_prev_term <= (#[trigger] m.body->AppendRequest_entries[k]).term,
        log_ok(n,m.body->AppendRequest_prev,m.body->AppendRequest_prev_term)
    ensures ordered(merge(n.log,m.body->AppendRequest_prev,m.body->AppendRequest_entries)),
        bounded(merge(n.log,m.body->AppendRequest_prev,m.body->AppendRequest_entries),m.term)
{
    let old=n.log; let prev=m.body->AppendRequest_prev; let entries=m.body->AppendRequest_entries;
    types::first_mismatch(old,prev,entries,1); reveal(merge);
    let first=choose |k: int| 1 <= k <= entries.len()+1
        && (forall |j: int| 0 <= j < k-1 ==> prev+j < old.len() && old[prev+j].term == (#[trigger] entries[j]).term)
        && (k == entries.len()+1 || prev+k > old.len() || old[prev+k-1].term != (#[trigger] entries[k-1]).term);
    if entries.len() > 0 && first != entries.len()+1 {
        if first > 1 { assert(prev+first-2 < old.len() && old[prev+first-2].term == entries[first-2].term); }
        let out=merge(old,prev,entries); let cut=prev+first-1;
        assert forall |i: int,j: int| 0 <= i <= j < out.len() implies (#[trigger] out[i]).term <= (#[trigger] out[j]).term by {
            if j < cut { assert(old[i].term <= old[j].term); }
            else if i >= cut { assert(entries[i-prev].term <= entries[j-prev].term); }
            else if i < prev {
                assert(old[i].term <= old[prev-1].term); assert(m.body->AppendRequest_prev_term <= entries[j-prev].term);
            } else { assert(old[i].term == entries[i-prev].term); assert(entries[i-prev].term <= entries[j-prev].term); }
        }
        assert forall |k: int| 0 <= k < out.len() implies 0 < (#[trigger] out[k]).term <= m.term by {
            if k < cut { assert(0 < old[k].term <= n.term); }
            else { assert(0 < entries[k-prev].term <= m.term); }
        }
    }
}
pub proof fn initial_inductive(c: Constants)
    requires valid_constants(c)
    ensures inductive(votes::initial_proof(c),c)
{ votes::initial_inductive(c); broadcast use vstd::multiset::group_multiset_axioms; }
pub proof fn preserve_node(g: ProofState,c: Constants,a: Action,i: int)
    requires inductive(g,c),enabled(g.state,c,a),c.servers.contains(i)
    ensures node(votes::advance(g,c,a).state.nodes[i])
{
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
    let s=g.state; let n=s.nodes[i]; assert(node(n)); assert(votes::node(n,i));
    if let Action::Receive { m,how } = a {
        assert(message(s,m)); assert(types::message(m,c));
        if m.dest == i && how == Receive::AcceptAppend { merge_order(n,m); }
    }
}
pub proof fn preserve_message(g: ProofState,c: Constants,a: Action,m: Message)
    requires inductive(g,c),enabled(g.state,c,a),votes::advance(g,c,a).state.messages.count(m) > 0
    ensures message(votes::advance(g,c,a).state,m),advertisement(votes::advance(g,c,a).state,m)
{
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    let s=g.state; let u=votes::advance(g,c,a).state;
    if s.messages.count(m) > 0 {
        assert(message(s,m)); assert(advertisement(s,m)); assert(types::message(m,c)); assert(votes::node(s.nodes[m.source],m.source));
    } else {
        if let Action::Receive { m: old,how } = a { assert(message(s,old)); assert(types::message(old,c)); }
        match a {
            Action::Timeout(i) => {
                let n=s.nodes[i]; assert(node(n));
                let q=n.latest_config.remove(i).map(|j: int| Message { source: i,dest: j,term: n.term+1,body: Body::VoteRequest {
                    last_term: log_term(n.log,n.log.len() as int),last_index: n.log.len() } });
                assert(q.contains(m));
            },
            Action::Replicate { i,j } => { assert(node(s.nodes[i])); assert(types::node(s.nodes[i],c)); },
            Action::Heartbeat { i,j } => { assert(node(s.nodes[i])); },
            Action::CompleteVote(i) => { assert(votes::node(s.nodes[i],i)); },
            _ => {},
        }
    }
}
pub proof fn preserve(g: ProofState,c: Constants,a: Action)
    requires inductive(g,c),enabled(g.state,c,a)
    ensures inductive(votes::advance(g,c,a),c)
{
    votes::preserve(g,c,a); let u=votes::advance(g,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u.state.nodes[i]) by { preserve_node(g,c,a,i); }
    assert forall |m: Message| #[trigger] u.state.messages.count(m) > 0 implies message(u.state,m) && advertisement(u.state,m) by { preserve_message(g,c,a,m); }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,time: int) -> (g: ProofState)
    requires configs::safety_spec(b,c),time >= 0
    ensures g.state == b[time],inductive(g,c)
    decreases time
{
    if time == 0 { initial_inductive(c); votes::initial_proof(c) }
    else {
        let g=safety_at(b,c,time-1); let p=time-1; assert(next(b[p],b[p+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[p],c,a) && b[time] == apply(b[p],c,a);
        preserve(g,c,a); votes::advance(g,c,a)
    }
}
} // verus!
