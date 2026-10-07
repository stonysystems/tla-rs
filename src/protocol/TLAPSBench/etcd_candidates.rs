//! Campaigns advertise logs whose entries all precede the campaign term.
use vstd::prelude::*;
use super::etcd::*;
use super::etcd_election as election;
use super::etcd_origins as origins;
use super::etcd_order as order;
use super::temporal::Behavior;
verus! {
pub open spec fn candidate(n: LServer) -> bool {
    n.role == Role::Candidate ==> forall |k: int| 0 <= k < n.log.len() ==> #[trigger] n.log[k] < n.term
}
pub open spec fn request(s: LState,m: Message) -> bool {
    match m.body { Body::VoteRequest { last_term: term,last_index } => term < m.term
        && (s.nodes[m.source].role == Role::Candidate && s.nodes[m.source].term == m.term ==>
            last_term(s.nodes[m.source].log) == term && s.nodes[m.source].log.len() == last_index),_ => true }
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    order::inductive(s,c)
    && (forall |i: int| c.servers.contains(i) ==> #[trigger] candidate(s.nodes[i]))
    && (forall |m: Message| #[trigger] s.pending.count(m) > 0 ==> request(s,m))
    && (forall |m: Message| #[trigger] s.messages.count(m) > 0 ==> request(s,m))
}
pub proof fn initial_inductive(c: Constants)
    requires valid_constants(c)
    ensures inductive(initial(c),c)
{ order::initial_inductive(c); broadcast use vstd::multiset::group_multiset_axioms; }
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures candidate(apply(s,c,a).nodes[i])
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    assert(candidate(s.nodes[i])); assert(order::node_order(s.nodes[i]));
}
pub proof fn preserve_request(s: LState,c: Constants,a: Action,m: Message)
    requires inductive(s,c),enabled(s,c,a),apply(s,c,a).pending.count(m) > 0 || apply(s,c,a).messages.count(m) > 0
    ensures request(apply(s,c,a),m)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    if s.pending.count(m) > 0 || s.messages.count(m) > 0 {
        assert(request(s,m));
        if s.pending.count(m) > 0 { assert(origins::pending_terms(s,m)); }
        if s.messages.count(m) > 0 { assert(origins::message_terms(s,m)); assert(election::node_inv(s,c,m.source)); }
    } else if m.body is VoteRequest {
        assert(candidate(s.nodes[m.source])); assert(order::node_order(s.nodes[m.source]));
        if s.nodes[m.source].log.len() > 0 { assert(s.nodes[m.source].log[s.nodes[m.source].log.len()-1] < s.nodes[m.source].term); }
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    order::preserve_inductive(s,c,a); let u=apply(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] candidate(u.nodes[i]) by { preserve_node(s,c,a,i); }
    assert forall |m: Message| #[trigger] u.pending.count(m) > 0 implies request(u,m) by { preserve_request(s,c,a,m); }
    assert forall |m: Message| #[trigger] u.messages.count(m) > 0 implies request(u,m) by { preserve_request(s,c,a,m); }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,k: int)
    requires election::safety_spec(b,c),k >= 0
    ensures inductive(b[k],c)
    decreases k
{
    if k == 0 { initial_inductive(c); }
    else {
        safety_at(b,c,k-1); let i=k-1; assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        preserve(b[i],c,a);
    }
}
} // verus!
