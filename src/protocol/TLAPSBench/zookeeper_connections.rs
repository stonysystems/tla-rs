//! Protocol roles, election phases, and leader/follower links remain consistent.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{Role,Phase};
use super::zk_election as fle;
use super::zookeeper_support as support;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn node(s: LState,c: Constants,i: int) -> bool {
    let n=s.nodes[i]; let e=s.election.nodes[i];
    (e.role == Role::Looking <==> n.phase == Phase::Election)
    && (e.role == Role::Leading ==> n.learners.contains(i) && n.leader == None)
    && (e.role != Role::Leading ==> n.learners.is_empty())
    && (n.leader is Some ==> e.role == Role::Following && n.leader.unwrap() != i)
    && (e.role == Role::Following && n.leader == None ==> n.phase == Phase::Discovery)
}
pub open spec fn link(s: LState,c: Constants,i: int,j: int) -> bool {
    (s.election.nodes[i].role == Role::Leading && s.nodes[i].learners.contains(j) && i != j ==> s.election.nodes[j].role == Role::Following && s.nodes[j].leader == Some(i))
    && (s.nodes[j].leader == Some(i) ==> s.election.nodes[i].role == Role::Leading && s.nodes[i].learners.contains(j))
}
pub open spec fn safe(s: LState,c: Constants) -> bool {
    support::shape(s,c) && (forall |i: int| c.servers.contains(i) ==> #[trigger] node(s,c,i))
    && forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) ==> #[trigger] link(s,c,i,j)
}
pub proof fn facts(s: LState,c: Constants,i: int,j: int)
    requires safe(s,c),c.servers.contains(i),c.servers.contains(j)
    ensures node(s,c,i),node(s,c,j),link(s,c,i,j),link(s,c,j,i),support::node(s.nodes[i],c),support::node(s.nodes[j],c)
{}
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    support::initial_shape(c); let s=initial(c);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(s,c,i) by {}
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] link(s,c,i,j) by {}
}
pub proof fn preserve_node_election(s: LState,c: Constants,ea: fle::Action,i: int)
    requires safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i)
    ensures node(apply(s,c,Action::Election(ea)),c,i)
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let a=Action::Election(ea); let x=receiver(a); facts(s,c,i,x);
}
pub proof fn preserve_node_crash(s: LState,c: Constants,x: int,i: int)
    requires safe(s,c),enabled(s,c,Action::Crash(x)),c.servers.contains(i)
    ensures node(apply(s,c,Action::Crash(x)),c,i)
{
    reveal(enabled); reveal(apply); facts(s,c,i,x);
    if let Some(y)=s.nodes[x].leader { facts(s,c,i,y); facts(s,c,x,y); }
}
#[verifier::spinoff_prover]
pub proof fn preserve_node_protocol(s: LState,c: Constants,a: Action,i: int)
    requires safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),!(a is Crash)
    ensures node(apply(s,c,a),c,i)
{
    hide(floor_index);
    reveal(enabled); reveal(apply);
    let x=receiver(a); if a != Action::Stutter { facts(s,c,i,x); }
    match a {
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::Sync(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            facts(s,c,i,y); facts(s,c,x,y);
        },
        _ => {},
    }
    assert(node(s,c,i));
}
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires safe(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures node(apply(s,c,a),c,i)
{
    match a {
        Action::Election(ea) => { preserve_node_election(s,c,ea,i); },
        Action::Crash(x) => { preserve_node_crash(s,c,x,i); },
        _ => { preserve_node_protocol(s,c,a,i); },
    }
}
#[verifier::spinoff_prover]
pub proof fn preserve_link(s: LState,c: Constants,a: Action,i: int,j: int)
    requires safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j)
    ensures link(apply(s,c,a),c,i,j)
{
    support::preserve(s,c,a); reveal(enabled); reveal(apply); reveal(fle::apply);
    let x=receiver(a); facts(s,c,i,j); if a != Action::Stutter { facts(s,c,i,x); facts(s,c,j,x); }
    match a {
        Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { facts(s,c,i,y); facts(s,c,j,y); facts(s,c,x,y); } },
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::Sync(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            facts(s,c,i,y); facts(s,c,j,y); facts(s,c,x,y);
        },
        _ => {},
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    support::preserve(s,c,a); let u=apply(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u,c,i) by { preserve_node(s,c,a,i); }
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] link(u,c,i,j) by { preserve_link(s,c,a,i,j); }
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0
    ensures safe(b[tick],c)
    decreases tick
{
    if tick == 0 { initial_safe(c); }
    else { at(b,c,tick-1); let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a); }
}
} // verus!
