//! Each log entry has an elected origin, retained across copies and restarts.
//! A leader's current-term entries can only have originated at that leader.
use vstd::prelude::*;
use super::etcd::*;
use super::etcd_election as election;
use super::temporal::Behavior;
verus! {
pub open spec fn voters(s: LState,c: Constants,t: nat,i: int) -> Set<int> {
    c.voters.filter(|v: int| s.votes.contains(Ballot { voter: v,term: t,candidate: i }))
}
pub open spec fn certificate(s: LState,c: Constants,t: nat,i: int) -> bool { quorum(voters(s,c,t,i),c) }
pub open spec fn pending_terms(s: LState,m: Message) -> bool {
    m.term <= s.nodes[m.source].term
    && (positive(m) && m.source != m.dest ==> m.term <= s.nodes[m.dest].disk.term)
}
pub open spec fn message_terms(s: LState,m: Message) -> bool {
    m.term <= s.nodes[m.source].disk.term
    && (positive(m) ==> m.term <= s.nodes[m.dest].disk.term)
}
pub open spec fn ballot_persisted(s: LState,b: Ballot) -> bool { b.term <= s.nodes[b.candidate].disk.term }
pub open spec fn durable_terms(s: LState,c: Constants) -> bool {
    (forall |m: Message| #[trigger] s.pending.count(m) > 0 ==> pending_terms(s,m))
    && (forall |m: Message| #[trigger] s.messages.count(m) > 0 ==> message_terms(s,m))
    && (forall |b: Ballot| s.votes.contains(b) ==> #[trigger] ballot_persisted(s,b))
}
pub open spec fn owner(s: LState,c: Constants,t: nat,k: int,i: int) -> bool {
    c.servers.contains(i) && certificate(s,c,t,i) && t <= s.nodes[i].disk.term && t <= s.nodes[i].term
    && (s.nodes[i].term == t ==> s.nodes[i].role != Role::Candidate)
    && (s.nodes[i].term == t && s.nodes[i].role == Role::Leader ==>
        1 <= k <= s.nodes[i].log.len() && s.nodes[i].log[k-1] == t)
}
pub open spec fn origin(s: LState,c: Constants,t: nat,k: int) -> bool {
    exists |i: int| #[trigger] owner(s,c,t,k,i)
}
pub open spec fn log_origins(s: LState,c: Constants,h: Seq<nat>,offset: int) -> bool {
    forall |k: int| 0 <= k < h.len() ==> origin(s,c,#[trigger] h[k],offset+k+1)
}
pub open spec fn message_origins(s: LState,c: Constants,m: Message) -> bool {
    match m.body { Body::AppendRequest { prev,entries,.. } => log_origins(s,c,entries,prev as int),_ => true }
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    valid_constants(c) && election::inductive(s,c) && durable_terms(s,c)
    && (forall |i: int| c.servers.contains(i) ==> #[trigger] log_origins(s,c,s.nodes[i].log,0))
    && (forall |i: int| c.servers.contains(i) ==> #[trigger] log_origins(s,c,s.nodes[i].disk.log,0))
    && (forall |m: Message| #[trigger] s.pending.count(m) > 0 ==> message_origins(s,c,m))
    && (forall |m: Message| #[trigger] s.messages.count(m) > 0 ==> message_origins(s,c,m))
}
pub proof fn initial_inductive(c: Constants)
    requires valid_constants(c)
    ensures inductive(initial(c),c)
{ election::initial_inductive(c); broadcast use vstd::multiset::group_multiset_axioms; }
pub proof fn certificate_monotone(s: LState,u: LState,c: Constants,t: nat,i: int)
    requires s.votes.subset_of(u.votes),certificate(s,c,t,i)
    ensures certificate(u,c,t,i)
{
    assert(voters(s,c,t,i).subset_of(voters(u,c,t,i)));
    vstd::set_lib::lemma_len_subset(voters(s,c,t,i),voters(u,c,t,i));
}
pub proof fn leader_persisted(s: LState,c: Constants,i: int)
    requires election::inductive(s,c),durable_terms(s,c),c.servers.contains(i),s.nodes[i].role == Role::Leader
    ensures certificate(s,c,s.nodes[i].term,i),s.nodes[i].disk.term == s.nodes[i].term
{
    election::unique_leader(s,c); assert(election::node_inv(s,c,i));
    let t=s.nodes[i].term;
    assert(s.nodes[i].granted.subset_of(voters(s,c,t,i))) by {
        assert forall |v: int| s.nodes[i].granted.contains(v) implies voters(s,c,t,i).contains(v) by {
            assert(s.votes.contains(Ballot { voter: v,term: t,candidate: i }));
        }
    }
    vstd::set_lib::lemma_len_subset(s.nodes[i].granted,voters(s,c,t,i));
    assert(!s.nodes[i].granted.is_empty());
    let v=choose |v: int| s.nodes[i].granted.contains(v);
    let b=Ballot { voter: v,term: t,candidate: i };
    assert(s.votes.contains(b)); assert(ballot_persisted(s,b));
}
pub proof fn preserve_pending_terms(s: LState,c: Constants,a: Action,m: Message)
    requires inductive(s,c),enabled(s,c,a),apply(s,c,a).pending.count(m) > 0
    ensures pending_terms(apply(s,c,a),m)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    election::preserve_pending(s,c,a,m);
    assert(election::node_inv(s,c,m.source)); assert(election::node_inv(s,c,m.dest));
    if s.pending.count(m) > 0 { assert(pending_terms(s,m)); }
    if let Action::Receive { m: old,how } = a { assert(message_terms(s,old)); }
}
pub proof fn preserve_message_terms(s: LState,c: Constants,a: Action,m: Message)
    requires inductive(s,c),enabled(s,c,a),apply(s,c,a).messages.count(m) > 0
    ensures message_terms(apply(s,c,a),m)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    election::preserve_message(s,c,a,m);
    assert(election::node_inv(s,c,m.source)); assert(election::node_inv(s,c,m.dest));
    if s.messages.count(m) > 0 { assert(message_terms(s,m)); }
    else { assert(pending_terms(s,m)); }
}
pub proof fn preserve_ballot(s: LState,c: Constants,a: Action,b: Ballot)
    requires inductive(s,c),enabled(s,c,a),apply(s,c,a).votes.contains(b)
    ensures ballot_persisted(apply(s,c,a),b)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    election::preserve_history(s,c,a,b);
    assert(election::node_inv(s,c,b.candidate));
    if s.votes.contains(b) { assert(ballot_persisted(s,b)); }
    else if let Action::Ready(i) = a {
        let m=election::released_origin(s,i,b);
        assert(pending_terms(s,m));
    }
}
pub proof fn preserve_owner(s: LState,c: Constants,a: Action,t: nat,k: int,i: int)
    requires inductive(s,c),enabled(s,c,a),owner(s,c,t,k,i)
    ensures owner(apply(s,c,a),c,t,k,i)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    let u=apply(s,c,a);
    assert(s.votes.subset_of(u.votes)); certificate_monotone(s,u,c,t,i);
    assert(election::node_inv(s,c,i));
}
pub proof fn preserve_origin(s: LState,c: Constants,a: Action,t: nat,k: int)
    requires inductive(s,c),enabled(s,c,a),origin(s,c,t,k)
    ensures origin(apply(s,c,a),c,t,k)
{
    let i=choose |i: int| #[trigger] owner(s,c,t,k,i);
    preserve_owner(s,c,a,t,k,i);
}
pub proof fn preserve_log(s: LState,c: Constants,a: Action,i: int,k: int,disk: bool)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i),
        0 <= k < if disk { apply(s,c,a).nodes[i].disk.log.len() } else { apply(s,c,a).nodes[i].log.len() }
    ensures origin(apply(s,c,a),c,if disk { apply(s,c,a).nodes[i].disk.log[k] } else { apply(s,c,a).nodes[i].log[k] },k+1)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    let u=apply(s,c,a); let h=if disk { u.nodes[i].disk.log } else { u.nodes[i].log };
    assert(log_origins(s,c,s.nodes[i].log,0)); assert(log_origins(s,c,s.nodes[i].disk.log,0));
    if !disk && a == Action::ClientRequest(i) && k == s.nodes[i].log.len() {
        leader_persisted(s,c,i);
        assert(u.votes == s.votes);
        certificate_monotone(s,u,c,s.nodes[i].term,i);
        assert(owner(u,c,h[k],k+1,i));
    } else {
        if let Action::Receive { m,how } = a {
            assert(message_origins(s,c,m));
            if let Body::AppendRequest { prev,entries,.. } = m.body {
                if !disk && m.dest == i && how == Receive::AppendExtend && k >= s.nodes[i].log.len() {
                    assert(origin(s,c,entries[k-prev],k+1));
                }
            }
        }
        assert(origin(s,c,h[k],k+1)); preserve_origin(s,c,a,h[k],k+1);
    }
}
pub proof fn preserve_message_origin(s: LState,c: Constants,a: Action,m: Message,k: int)
    requires inductive(s,c),enabled(s,c,a),
        apply(s,c,a).pending.count(m) > 0 || apply(s,c,a).messages.count(m) > 0,
        m.body is AppendRequest,0 <= k < m.body->AppendRequest_entries.len()
    ensures origin(apply(s,c,a),c,m.body->AppendRequest_entries[k],m.body->AppendRequest_prev+k+1)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    if s.pending.count(m) > 0 || s.messages.count(m) > 0 { assert(message_origins(s,c,m)); }
    else { assert(log_origins(s,c,s.nodes[m.source].log,0)); }
    let t=m.body->AppendRequest_entries[k]; let pos=m.body->AppendRequest_prev+k+1;
    assert(origin(s,c,t,pos)); preserve_origin(s,c,a,t,pos);
}
pub proof fn preserve_inductive(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    election::preserve_inductive(s,c,a); let u=apply(s,c,a);
    assert forall |m: Message| #[trigger] u.pending.count(m) > 0 implies pending_terms(u,m) by { preserve_pending_terms(s,c,a,m); }
    assert forall |m: Message| #[trigger] u.messages.count(m) > 0 implies message_terms(u,m) by { preserve_message_terms(s,c,a,m); }
    assert forall |b: Ballot| u.votes.contains(b) implies #[trigger] ballot_persisted(u,b) by { preserve_ballot(s,c,a,b); }
    assert forall |i: int| c.servers.contains(i) implies #[trigger] log_origins(u,c,u.nodes[i].log,0) by {
        assert forall |k: int| 0 <= k < u.nodes[i].log.len() implies #[trigger] origin(u,c,u.nodes[i].log[k],k+1) by { preserve_log(s,c,a,i,k,false); }
    }
    assert forall |i: int| c.servers.contains(i) implies #[trigger] log_origins(u,c,u.nodes[i].disk.log,0) by {
        assert forall |k: int| 0 <= k < u.nodes[i].disk.log.len() implies #[trigger] origin(u,c,u.nodes[i].disk.log[k],k+1) by { preserve_log(s,c,a,i,k,true); }
    }
    assert forall |m: Message| #[trigger] u.pending.count(m) > 0 implies message_origins(u,c,m) by {
        if let Body::AppendRequest { prev,entries,.. } = m.body {
            assert forall |k: int| 0 <= k < entries.len() implies #[trigger] origin(u,c,entries[k],prev+k+1) by { preserve_message_origin(s,c,a,m,k); }
        }
    }
    assert forall |m: Message| #[trigger] u.messages.count(m) > 0 implies message_origins(u,c,m) by {
        if let Body::AppendRequest { prev,entries,.. } = m.body {
            assert forall |k: int| 0 <= k < entries.len() implies #[trigger] origin(u,c,entries[k],prev+k+1) by { preserve_message_origin(s,c,a,m,k); }
        }
    }
}
pub proof fn unique_certificate(s: LState,c: Constants,t: nat,i: int,j: int)
    requires election::inductive(s,c),certificate(s,c,t,i),certificate(s,c,t,j)
    ensures i == j
{
    let v=election::majorities_intersect(voters(s,c,t,i),voters(s,c,t,j),c);
    let a=Ballot { voter: v,term: t,candidate: i }; let b=Ballot { voter: v,term: t,candidate: j };
    assert(s.votes.contains(a) && s.votes.contains(b)); assert(election::compatible(a,b));
}
pub proof fn leader_contains_term(s: LState,c: Constants,i: int,j: int,k: int)
    requires inductive(s,c),c.servers.contains(i),c.servers.contains(j),s.nodes[i].role == Role::Leader,
        0 <= k < s.nodes[j].log.len(),s.nodes[j].log[k] == s.nodes[i].term
    ensures k < s.nodes[i].log.len(),s.nodes[i].log[k] == s.nodes[i].term
{
    leader_persisted(s,c,i);
    assert(log_origins(s,c,s.nodes[j].log,0)); assert(origin(s,c,s.nodes[i].term,k+1));
    let o=choose |o: int| #[trigger] owner(s,c,s.nodes[i].term,k+1,o);
    unique_certificate(s,c,s.nodes[i].term,i,o);
}
pub proof fn maximum_correct(q: Set<int>)
    requires !q.is_empty()
    ensures q.contains(maximum(q)),forall |x: int| q.contains(x) ==> x <= maximum(q)
    decreases q.len()
{
    let x=q.choose(); let rest=q.remove(x);
    let m=if rest.is_empty() { x } else { maximum_correct(rest); if x > maximum(rest) { x } else { maximum(rest) } };
    assert(q.contains(m)); assert forall |y: int| q.contains(y) implies y <= m by { if y != x { assert(rest.contains(y)); } }
    assert(exists |z: int| q.contains(z) && forall |y: int| q.contains(y) ==> y <= z);
    reveal(maximum);
}
pub proof fn election_safety_from_inductive(s: LState,c: Constants)
    requires inductive(s,c)
    ensures election_safety(s,c)
{
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) && s.nodes[i].role == Role::Leader implies
        max_term_index(s.nodes[i],s.nodes[i].term) >= max_term_index(s.nodes[j],s.nodes[i].term) by {
        let t=s.nodes[i].term;
        let a=term_positions(s.nodes[i],t);
        let b=term_positions(s.nodes[j],t);
        assert(max_term_index(s.nodes[i],t) == if a.is_empty() { 0 } else { maximum(a) });
        assert(max_term_index(s.nodes[j],t) == if b.is_empty() { 0 } else { maximum(b) });
        if !a.is_empty() { maximum_correct(a); }
        if !b.is_empty() {
            maximum_correct(b); let k=maximum(b);
            leader_contains_term(s,c,i,j,k-1);
            assert(a.contains(k)); maximum_correct(a);
        }
    }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,k: int)
    requires election::safety_spec(b,c),k >= 0
    ensures inductive(b[k],c),election_safety(b[k],c)
    decreases k
{
    if k == 0 { initial_inductive(c); }
    else {
        safety_at(b,c,k-1); let i=k-1; assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        preserve_inductive(b[i],c,a);
    }
    election_safety_from_inductive(b[k],c);
}
pub proof fn election_safety_correct(b: Behavior<LState>,c: Constants)
    requires election::safety_spec(b,c)
    ensures forall |k: int| k >= 0 ==> #[trigger] election_safety(b[k],c)
{
    assert forall |k: int| k >= 0 implies #[trigger] election_safety(b[k],c) by { safety_at(b,c,k); }
}
} // verus!
