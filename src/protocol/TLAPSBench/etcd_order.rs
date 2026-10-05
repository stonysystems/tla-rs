//! Term order and persistence relationships used by the remaining Raft proofs.
use vstd::prelude::*;
use super::etcd::{*,sub};
use super::etcd_origins as origins;
use super::etcd_election as election;
use super::etcd_logs as logs;
use super::temporal::Behavior;
verus! {
pub open spec fn ordered(h: Seq<nat>) -> bool {
    forall |i: int,j: int| 0 <= i <= j < h.len() ==> #[trigger] h[i] <= #[trigger] h[j]
}
pub open spec fn bounded(h: Seq<nat>,t: nat) -> bool {
    forall |k: int| 0 <= k < h.len() ==> 0 < #[trigger] h[k] <= t
}
pub open spec fn node_order(n: LServer) -> bool {
    (n.role != Role::Follower ==> n.term > 0)
    && ordered(n.log) && bounded(n.log,n.term) && ordered(n.disk.log) && bounded(n.disk.log,n.disk.term)
    && (n.role == Role::Candidate && n.disk.term == n.term ==> n.log == n.disk.log)
    && (n.role == Role::Leader ==> logs::prefix_of(n.disk.log,n.log))
}
pub open spec fn message_order(m: Message) -> bool {
    match m.body {
        Body::AppendRequest { prev,prev_term,entries,.. } => ordered(entries) && bounded(entries,m.term)
            && prev_term <= m.term && (prev == 0 ==> prev_term == 0)
            && forall |k: int| 0 <= k < entries.len() ==> prev_term <= #[trigger] entries[k],
        Body::VoteRequest { last_term,.. } => last_term <= m.term,
        _ => true,
    }
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    origins::inductive(s,c)
    && (forall |i: int| c.servers.contains(i) ==> #[trigger] node_order(s.nodes[i]))
    && (forall |m: Message| #[trigger] s.pending.count(m) > 0 ==> message_order(m))
    && (forall |m: Message| #[trigger] s.messages.count(m) > 0 ==> message_order(m))
}
pub proof fn initial_inductive(c: Constants)
    requires valid_constants(c)
    ensures inductive(initial(c),c)
{ origins::initial_inductive(c); broadcast use vstd::multiset::group_multiset_axioms; }
pub proof fn candidate_persisted(s: LState,c: Constants,i: int)
    requires inductive(s,c),c.servers.contains(i),s.nodes[i].role == Role::Candidate,quorum(s.nodes[i].granted,c)
    ensures s.nodes[i].disk.term == s.nodes[i].term,s.nodes[i].log == s.nodes[i].disk.log
{
    assert(election::node_inv(s,c,i));
    assert(!s.nodes[i].granted.is_empty());
    let v=s.nodes[i].granted.choose();
    let b=Ballot { voter: v,term: s.nodes[i].term,candidate: i };
    assert(s.votes.contains(b)); assert(origins::ballot_persisted(s,b)); assert(node_order(s.nodes[i]));
}
pub proof fn extend_order(n: LServer,m: Message)
    requires node_order(n),message_order(m),m.body is AppendRequest,m.term == n.term,
        log_ok(n,m.body->AppendRequest_prev,m.body->AppendRequest_prev_term),
        no_conflict(n,m.body->AppendRequest_prev+1,m.body->AppendRequest_entries)
    ensures ordered(n.log + sub(m.body->AppendRequest_entries,n.log.len()-m.body->AppendRequest_prev+1,m.body->AppendRequest_entries.len() as int)),
        bounded(n.log + sub(m.body->AppendRequest_entries,n.log.len()-m.body->AppendRequest_prev+1,m.body->AppendRequest_entries.len() as int),n.term)
{
    let old=n.log; let prev=m.body->AppendRequest_prev; let entries=m.body->AppendRequest_entries;
    let h=old+sub(entries,old.len()-prev+1,entries.len() as int);
    assert(prev <= old.len());
    assert forall |i: int,j: int| 0 <= i <= j < h.len() implies #[trigger] h[i] <= #[trigger] h[j] by {
        if j < old.len() { assert(old[i] <= old[j]); }
        else if i >= old.len() { assert(entries[i-prev] <= entries[j-prev]); }
        else if i < prev {
            assert(prev > 0); assert(old[i] <= old[prev-1]); assert(m.body->AppendRequest_prev_term <= entries[j-prev]);
        } else {
            assert(old[i] == entries[i-prev]); assert(entries[i-prev] <= entries[j-prev]);
        }
    }
}
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures node_order(apply(s,c,a).nodes[i])
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    assert(node_order(s.nodes[i])); assert(election::node_inv(s,c,i));
    if let Action::BecomeLeader(j) = a { candidate_persisted(s,c,j); }
    if let Action::Receive { m,how } = a {
        assert(message_order(m)); assert(origins::message_terms(s,m));
        if how == Receive::AppendExtend && m.dest == i { extend_order(s.nodes[i],m); }
    }
}
pub proof fn preserve_message(s: LState,c: Constants,a: Action,m: Message)
    requires inductive(s,c),enabled(s,c,a),apply(s,c,a).pending.count(m) > 0 || apply(s,c,a).messages.count(m) > 0
    ensures message_order(m)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    if s.pending.count(m) > 0 || s.messages.count(m) > 0 { assert(message_order(m)); }
    else {
        assert(node_order(s.nodes[m.source]));
        match a {
            Action::Append { i,j,begin,end } => { assert(message_order(m)); },
            Action::Heartbeat { i,j } => { assert(message_order(m)); },
            Action::Snapshot { i,j,index } => { assert(message_order(m)); },
            _ => { assert(message_order(m)); },
        }
    }
}
pub proof fn preserve_inductive(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    origins::preserve_inductive(s,c,a); let u=apply(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node_order(u.nodes[i]) by { preserve_node(s,c,a,i); }
    assert forall |m: Message| #[trigger] u.pending.count(m) > 0 implies message_order(m) by { preserve_message(s,c,a,m); }
    assert forall |m: Message| #[trigger] u.messages.count(m) > 0 implies message_order(m) by { preserve_message(s,c,a,m); }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,k: int)
    requires election::safety_spec(b,c),k >= 0
    ensures inductive(b[k],c)
    decreases k
{
    if k == 0 { initial_inductive(c); }
    else {
        safety_at(b,c,k-1); let i=k-1; assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[k-1],c,a) && b[k] == apply(b[k-1],c,a);
        preserve_inductive(b[k-1],c,a);
    }
}
} // verus!
