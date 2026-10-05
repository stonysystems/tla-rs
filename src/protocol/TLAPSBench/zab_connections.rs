//! Reachable connection and channel structure for the full Zab state machine.
use vstd::prelude::*;
use super::zab::*;
use super::temporal::Behavior;
verus! {
pub proof fn channel_pair(c: Constants,i: int,j: int)
    ensures channels(c).contains((i,j)) == (c.servers.contains(i) && c.servers.contains(j))
{
    let rows=c.servers.map(|i: int| c.servers.map(|j: int| (i,j)));
    rows.lemma_flatten_contains((i,j));
    if c.servers.contains(i) && c.servers.contains(j) {
        let row=c.servers.map(|j: int| (i,j));
        assert(row.contains((i,j))); assert(rows.contains(row));
    }
}
pub open spec fn node(s: LState,c: Constants,i: int) -> bool {
    let n=s.nodes[i];
    n.learners.subset_of(c.servers)
    && (n.role == Role::Looking <==> n.phase == Phase::Election)
    && (n.role == Role::Leading ==> n.learners.contains(i) && n.leader == None)
    && (n.role != Role::Leading ==> n.learners.is_empty())
    && (n.leader is Some ==> n.role == Role::Following && c.servers.contains(n.leader.unwrap()) && n.leader.unwrap() != i)
    && (n.role == Role::Following && n.leader == None ==> n.phase == Phase::Discovery)
}
pub open spec fn link(s: LState,c: Constants,i: int,j: int) -> bool {
    (s.nodes[i].role == Role::Leading && s.nodes[i].learners.contains(j) && i != j ==>
        s.nodes[j].role == Role::Following && s.nodes[j].leader == Some(i))
    && (s.nodes[j].leader == Some(i) ==> s.nodes[i].role == Role::Leading && s.nodes[i].learners.contains(j))
}
pub open spec fn packet_link(s: LState,i: int,j: int) -> bool {
    i != j && (s.nodes[i].role == Role::Leading && s.nodes[i].learners.contains(j)
        || s.nodes[j].role == Role::Leading && s.nodes[j].learners.contains(i))
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    s.nodes.dom() == c.servers && s.msgs.dom() == channels(c)
    && (s.oracle is Some ==> c.servers.contains(s.oracle.unwrap()))
    && (forall |i: int| c.servers.contains(i) ==> #[trigger] node(s,c,i))
    && (forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) ==> #[trigger] link(s,c,i,j))
    && (forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) && (#[trigger] s.msgs[(i,j)]).len() > 0 ==> packet_link(s,i,j))
}
pub proof fn initial_invariant(c: Constants)
    ensures inductive(initial(c),c)
{
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) && (#[trigger] initial(c).msgs[(i,j)]).len() > 0 implies packet_link(initial(c),i,j) by { channel_pair(c,i,j); }
}
pub proof fn facts(s: LState,c: Constants,i: int,j: int)
    requires inductive(s,c),c.servers.contains(i),c.servers.contains(j)
    ensures node(s,c,i),node(s,c,j),link(s,c,i,j),link(s,c,j,i),
        s.msgs[(i,j)].len() > 0 ==> packet_link(s,i,j),
        s.msgs[(j,i)].len() > 0 ==> packet_link(s,j,i),
        i != j ==> c.servers.len() > 1
{
    if i != j { let pair=set![i,j]; assert(pair.subset_of(c.servers)); vstd::set_lib::lemma_len_subset(pair,c.servers); }
}
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures node(apply(s,c,a),c,i)
{
    reveal(enabled); reveal(apply);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            facts(s,c,i,x); facts(s,c,i,y); facts(s,c,x,y);
        },
        Action::Restart(x) => {
            facts(s,c,i,x);
            if let Some(y)=s.nodes[x].leader { facts(s,c,i,x); facts(s,c,i,y); facts(s,c,x,y); }
        },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { facts(s,c,i,x); },
        _ => {},
    }

    assert(node(s,c,i));
}
pub proof fn preserve_link(s: LState,c: Constants,a: Action,i: int,j: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j)
    ensures link(apply(s,c,a),c,i,j)
{
    reveal(enabled); reveal(apply);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            facts(s,c,i,j); facts(s,c,i,x); facts(s,c,i,y); facts(s,c,j,x); facts(s,c,j,y); facts(s,c,x,y);
        },
        Action::Restart(x) => {
            facts(s,c,i,j); facts(s,c,i,x); facts(s,c,j,x);
            if let Some(y)=s.nodes[x].leader { facts(s,c,i,j); facts(s,c,i,x); facts(s,c,i,y); facts(s,c,j,x); facts(s,c,j,y); facts(s,c,x,y); }
        },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { facts(s,c,i,j); facts(s,c,i,x); facts(s,c,j,x); },
        _ => {},
    }

    assert(node(s,c,i) && node(s,c,j) && link(s,c,i,j));
}
pub proof fn preserve_packet(s: LState,c: Constants,a: Action,i: int,j: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j)
    ensures apply(s,c,a).msgs[(i,j)].len() > 0 ==> packet_link(apply(s,c,a),i,j)
{
    reveal(enabled); reveal(apply);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            facts(s,c,i,j); facts(s,c,i,x); facts(s,c,i,y); facts(s,c,j,x); facts(s,c,j,y); facts(s,c,x,y);
        },
        Action::Restart(x) => {
            facts(s,c,i,j); facts(s,c,i,x); facts(s,c,j,x);
            if let Some(y)=s.nodes[x].leader { facts(s,c,i,j); facts(s,c,i,x); facts(s,c,i,y); facts(s,c,j,x); facts(s,c,j,y); facts(s,c,x,y); }
        },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { facts(s,c,i,j); facts(s,c,i,x); facts(s,c,j,x); },
        _ => {},
    }

    channel_pair(c,i,j);
    assert(node(s,c,i) && node(s,c,j) && link(s,c,i,j) && link(s,c,j,i));
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    let u=apply(s,c,a);
    reveal(enabled); reveal(apply);
    match a {
        Action::Timeout(i,j) | Action::Connect(i,j) | Action::CEpoch(i,j) | Action::NewEpoch(i,j) | Action::AckEpoch(i,j) | Action::NewLeader(i,j) | Action::AckLd(i,j) | Action::CommitLd(i,j) | Action::Propose(i,j) | Action::Ack(i,j) | Action::Commit(i,j) => { channel_pair(c,i,j); channel_pair(c,j,i); },
        Action::Restart(i) => { assert(node(s,c,i)); if let Some(j)=s.nodes[i].leader { channel_pair(c,i,j); channel_pair(c,j,i); } },
        _ => {},
    }
    assert(u.nodes.dom() =~= c.servers);
    assert(u.msgs.dom() =~= channels(c));
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u,c,i) by { preserve_node(s,c,a,i); }
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] link(u,c,i,j) by { preserve_link(s,c,a,i,j); }
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) && (#[trigger] u.msgs[(i,j)]).len() > 0 implies packet_link(u,i,j) by { preserve_packet(s,c,a,i,j); }

}
pub open spec fn safety_spec(b: Behavior<LState>,c: Constants) -> bool {
    valid_constants(c) && b[0] == initial(c)
    && (forall |k: int| k >= 0 ==> b.dom().contains(k))
    && (forall |k: int| k >= 0 ==> #[trigger] next(b[k],b[k+1],c))
}
pub proof fn at(b: Behavior<LState>,c: Constants,k: int)
    requires safety_spec(b,c),k >= 0
    ensures inductive(b[k],c)
    decreases k
{
    if k == 0 { initial_invariant(c); }
    else {
        at(b,c,k-1); let time=k-1; assert(next(b[time],b[time+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[k-1],c,a) && b[k] == apply(b[k-1],c,a);
        preserve(b[k-1],c,a);
    }
}
} // verus!
