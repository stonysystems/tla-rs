//! Accepted and current epochs never decrease, including across election and recovery.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role};
use super::zk_election_types as election;
use super::zookeeper_support as support;
use super::zookeeper_connections as connections;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn node(s: LState,c: Constants,i: int) -> bool {
    let n=s.nodes[i]; let e=s.election.nodes[i];
    0 <= e.current <= n.accepted
    && (e.role == Role::Leading ==> n.accepted <= n.max_epoch && (!formed(c,i,z::al_ids(n.connecting)) ==> n.accepted < n.max_epoch))
}
pub open spec fn safe(s: LState,c: Constants) -> bool { forall |i: int| c.servers.contains(i) ==> #[trigger] node(s,c,i) }
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(initial(c),c,i) by {}
}
pub proof fn preserve_node_election(s: LState,c: Constants,ea: super::zk_election::Action,i: int)
    requires connections::safe(s,c),safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i)
    ensures node(apply(s,c,Action::Election(ea)),c,i),s.nodes[i].accepted <= apply(s,c,Action::Election(ea)).nodes[i].accepted,s.election.nodes[i].current <= apply(s,c,Action::Election(ea)).election.nodes[i].current
{
    reveal(enabled); reveal(apply); reveal(super::zk_election::apply); let x=receiver(Action::Election(ea));
    connections::facts(s,c,i,x); assert(node(s,c,i)); assert(node(s,c,x));
    let u=apply(s,c,Action::Election(ea));
    if i == x && (ea is Handle || ea is Wait) && u.election.nodes[i].role == Role::Leading { assert(u.nodes[i].max_epoch > u.nodes[i].accepted); }
}
pub proof fn preserve_node_crash(s: LState,c: Constants,x: int,i: int)
    requires connections::safe(s,c),safe(s,c),enabled(s,c,Action::Crash(x)),c.servers.contains(i)
    ensures node(apply(s,c,Action::Crash(x)),c,i),s.nodes[i].accepted <= apply(s,c,Action::Crash(x)).nodes[i].accepted,s.election.nodes[i].current <= apply(s,c,Action::Crash(x)).election.nodes[i].current
{
    reveal(enabled); reveal(apply); connections::facts(s,c,i,x); assert(node(s,c,i)); assert(node(s,c,x));
    if let Some(y)=s.nodes[x].leader {
        connections::facts(s,c,i,y); connections::facts(s,c,x,y); assert(node(s,c,y));
        super::zab_collections::disconnect_ids(Set::empty(),Set::empty(),s.nodes[y].connecting,x);
    }
}
pub proof fn preserve_node_follower_info(s: LState,c: Constants,x: int,y: int,i: int)
    requires connections::safe(s,c),safe(s,c),enabled(s,c,Action::FollowerInfo(x,y)),c.servers.contains(i)
    ensures node(apply(s,c,Action::FollowerInfo(x,y)),c,i),s.nodes[i].accepted <= apply(s,c,Action::FollowerInfo(x,y)).nodes[i].accepted,s.election.nodes[i].current <= apply(s,c,Action::FollowerInfo(x,y)).election.nodes[i].current
{
    reveal(enabled); reveal(apply); connections::facts(s,c,i,x); connections::facts(s,c,i,y); connections::facts(s,c,x,y);
    assert(node(s,c,i)); assert(node(s,c,x));
}
pub proof fn preserve_node_leader_info(s: LState,c: Constants,x: int,y: int,i: int)
    requires connections::safe(s,c),safe(s,c),enabled(s,c,Action::LeaderInfo(x,y)),c.servers.contains(i)
    ensures node(apply(s,c,Action::LeaderInfo(x,y)),c,i),s.nodes[i].accepted <= apply(s,c,Action::LeaderInfo(x,y)).nodes[i].accepted,s.election.nodes[i].current <= apply(s,c,Action::LeaderInfo(x,y)).election.nodes[i].current
{
    reveal(enabled); reveal(apply); connections::facts(s,c,i,x); connections::facts(s,c,i,y); connections::facts(s,c,x,y);
    assert(node(s,c,i)); assert(node(s,c,x)); assert(node(s,c,y));
    super::zab_collections::disconnect_ids(Set::empty(),Set::empty(),s.nodes[y].connecting,x);
}
pub proof fn preserve_node_protocol(s: LState,c: Constants,a: Action,i: int)
    requires connections::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),!(a is Crash),!(a is FollowerInfo),!(a is LeaderInfo)
    ensures node(apply(s,c,a),c,i),s.nodes[i].accepted <= apply(s,c,a).nodes[i].accepted,s.election.nodes[i].current <= apply(s,c,a).election.nodes[i].current
{
    let u=apply(s,c,a); reveal(enabled); reveal(apply); assert(node(s,c,i)); assert(connections::node(s,c,i));
    let x=receiver(a); if a != Action::Stutter { connections::facts(s,c,i,x); assert(node(s,c,x)); }
    match a {
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::Sync(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            connections::facts(s,c,i,y); connections::facts(s,c,x,y); assert(node(s,c,y));
            super::zab_collections::disconnect_ids(Set::empty(),Set::empty(),s.nodes[x].connecting,y); super::zab_collections::disconnect_ids(Set::empty(),Set::empty(),s.nodes[y].connecting,x);
        },
        _ => {},
    }
}
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires connections::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures node(apply(s,c,a),c,i),s.nodes[i].accepted <= apply(s,c,a).nodes[i].accepted,s.election.nodes[i].current <= apply(s,c,a).election.nodes[i].current
{
    match a {
        Action::Election(ea) => { preserve_node_election(s,c,ea,i); },
        Action::Crash(x) => { preserve_node_crash(s,c,x,i); },
        Action::FollowerInfo(x,y) => { preserve_node_follower_info(s,c,x,y,i); },
        Action::LeaderInfo(x,y) => { preserve_node_leader_info(s,c,x,y,i); },
        _ => { preserve_node_protocol(s,c,a,i); },
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires connections::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u,c,i) by { preserve_node(s,c,a,i); }
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0
    ensures safe(b[tick],c)
    decreases tick
{
    if tick == 0 { initial_safe(c); }
    else { at(b,c,tick-1); connections::at(b,c,tick-1); let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a); }
}
pub proof fn between(b: Behavior<LState>,c: Constants,first: int,last: int,i: int)
    requires support::safety_spec(b,c),0 <= first <= last,c.servers.contains(i)
    ensures b[first].nodes[i].accepted <= b[last].nodes[i].accepted,b[first].election.nodes[i].current <= b[last].election.nodes[i].current
    decreases last-first
{
    if first < last { between(b,c,first,last-1,i); at(b,c,last-1); connections::at(b,c,last-1); let a=support::step(b,c,last-1); preserve_node(b[last-1],c,a,i); }
}
} // verus!
