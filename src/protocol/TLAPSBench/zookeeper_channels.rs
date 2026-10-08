//! Protocol channels stay within current leader/follower connections.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{Role,Phase};
use super::zk_election as fle;
use super::zookeeper_connections as connections;
use super::zookeeper_support as support;
use super::zab_connections::channel_pair;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn node(s: LState,c: Constants,i: int) -> bool {
    let n=s.nodes[i];
    n.forwarding.subset_of(n.learners)
    && (s.election.nodes[i].role != Role::Leading ==> n.forwarding.is_empty())
    && (s.election.nodes[i].role == Role::Leading ==> forall |r: Electing| #![trigger n.electing.contains(r)] n.electing.contains(r) && r.sid == i ==> r.zxid == unset())
}
pub open spec fn linked(s: LState,i: int,j: int) -> bool {
    i != j && (s.election.nodes[i].role == Role::Leading && s.nodes[i].learners.contains(j) || s.election.nodes[j].role == Role::Leading && s.nodes[j].learners.contains(i))
}
pub open spec fn cell(s: LState,i: int,j: int) -> bool { s.msgs[(i,j)].len() > 0 ==> linked(s,i,j) }
pub open spec fn safe(s: LState,c: Constants) -> bool {
    connections::safe(s,c) && (forall |i: int| c.servers.contains(i) ==> #[trigger] node(s,c,i))
    && forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) ==> #[trigger] cell(s,i,j)
}
pub proof fn facts(s: LState,c: Constants,i: int,j: int)
    requires safe(s,c),c.servers.contains(i),c.servers.contains(j)
    ensures connections::node(s,c,i),connections::node(s,c,j),connections::link(s,c,i,j),connections::link(s,c,j,i),
        node(s,c,i),node(s,c,j),cell(s,i,j),cell(s,j,i),support::node(s.nodes[i],c),support::node(s.nodes[j],c)
{
    connections::facts(s,c,i,j);
}
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    connections::initial_safe(c); let s=initial(c);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(s,c,i) by {}
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(s,i,j) by { channel_pair(c,i,j); }
}
pub proof fn preserve_node_election(s: LState,c: Constants,ea: fle::Action,i: int)
    requires safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i)
    ensures node(apply(s,c,Action::Election(ea)),c,i)
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(Action::Election(ea)); facts(s,c,i,x);
}
pub proof fn preserve_node_crash(s: LState,c: Constants,x: int,i: int)
    requires safe(s,c),enabled(s,c,Action::Crash(x)),c.servers.contains(i)
    ensures node(apply(s,c,Action::Crash(x)),c,i)
{
    reveal(enabled); reveal(apply); facts(s,c,i,x);
    if let Some(y)=s.nodes[x].leader { facts(s,c,i,y); facts(s,c,x,y); }
}
pub proof fn preserve_node_sync(s: LState,c: Constants,x: int,y: int,i: int)
    requires safe(s,c),enabled(s,c,Action::Sync(x,y)),c.servers.contains(i)
    ensures node(apply(s,c,Action::Sync(x,y)),c,i)
{
    reveal(enabled); reveal(apply); facts(s,c,i,x); facts(s,c,i,y); facts(s,c,x,y);
    let r=choose |r: Electing| #![trigger s.nodes[x].electing.contains(r)] s.nodes[x].electing.contains(r) && r.sid == y && r.zxid != unset() && s.nodes[x].learners.contains(y);
    if x == y { assert(r.zxid == unset()); assert(false); }
}
pub proof fn preserve_node_ackepoch(s: LState,c: Constants,x: int,y: int,i: int)
    requires safe(s,c),enabled(s,c,Action::AckEpoch(x,y)),c.servers.contains(i)
    ensures node(apply(s,c,Action::AckEpoch(x,y)),c,i)
{
    reveal(enabled); reveal(apply); facts(s,c,i,x); facts(s,c,i,y); facts(s,c,x,y); assert(x != y);
}
pub proof fn preserve_node_protocol(s: LState,c: Constants,a: Action,i: int)
    requires safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),!(a is Crash),!(a is Sync),!(a is AckEpoch)
    ensures node(apply(s,c,a),c,i)
{
    reveal(enabled); reveal(apply); let x=receiver(a); assert(node(s,c,i)); if a != Action::Stutter { facts(s,c,i,x); }
    match a {
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::Sync(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            facts(s,c,i,y); facts(s,c,x,y);

        },
        _ => {},
    }
    let u=apply(s,c,a);
    assert(u.nodes[i].forwarding.subset_of(u.nodes[i].learners));
    assert(u.election.nodes[i].role != Role::Leading ==> u.nodes[i].forwarding.is_empty());
    if u.election.nodes[i].role == Role::Leading {
        assert(s.election.nodes[i].role == Role::Leading);
        assert forall |r: Electing| #![trigger u.nodes[i].electing.contains(r)] u.nodes[i].electing.contains(r) && r.sid == i implies r.zxid == unset() by {
            if s.nodes[i].electing.contains(r) { assert(r.zxid == unset()); }
            else { assert(r.zxid == unset()); }
        }
    }

}
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires safe(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures node(apply(s,c,a),c,i)
{
    match a { Action::Election(ea) => { preserve_node_election(s,c,ea,i); },Action::Crash(x) => { preserve_node_crash(s,c,x,i); },Action::Sync(x,y) => { preserve_node_sync(s,c,x,y,i); },Action::AckEpoch(x,y) => { preserve_node_ackepoch(s,c,x,y,i); },_ => { preserve_node_protocol(s,c,a,i); } }
}
pub proof fn preserve_election(s: LState,c: Constants,ea: fle::Action,i: int,j: int)
    requires safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i),c.servers.contains(j)
    ensures cell(apply(s,c,Action::Election(ea)),i,j)
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(Action::Election(ea)); facts(s,c,i,j); facts(s,c,i,x); facts(s,c,j,x);
}
pub proof fn preserve_environment(s: LState,c: Constants,a: Action,i: int,j: int)
    requires safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),a is Crash || a is Partition || a is Recover || a is Start || a is Stutter
    ensures cell(apply(s,c,a),i,j)
{
    reveal(enabled); reveal(apply); let x=receiver(a); channel_pair(c,i,j); facts(s,c,i,j); if a != Action::Stutter { facts(s,c,i,x); facts(s,c,j,x); }
    if let Action::Crash(_)=a { if let Some(y)=s.nodes[x].leader { facts(s,c,i,y); facts(s,c,j,y); facts(s,c,x,y); } }
    if let Action::Partition(_,y)=a { facts(s,c,i,y); facts(s,c,j,y); facts(s,c,x,y); }
}
pub proof fn preserve_sync(s: LState,c: Constants,x: int,y: int,i: int,j: int)
    requires safe(s,c),enabled(s,c,Action::Sync(x,y)),c.servers.contains(i),c.servers.contains(j)
    ensures cell(apply(s,c,Action::Sync(x,y)),i,j)
{
    reveal(enabled); reveal(apply); channel_pair(c,i,j); facts(s,c,i,j); facts(s,c,i,x); facts(s,c,j,x); facts(s,c,i,y); facts(s,c,j,y); facts(s,c,x,y);
    let r=choose |r: Electing| #![trigger s.nodes[x].electing.contains(r)] s.nodes[x].electing.contains(r) && r.sid == y && r.zxid != unset() && s.nodes[x].learners.contains(y);
    if x == y { assert(r.zxid == unset()); assert(false); }
}
pub proof fn preserve_protocol(s: LState,c: Constants,a: Action,i: int,j: int)
    requires safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),!(a is Election),!(a is Crash),!(a is Partition),!(a is Recover),!(a is Start),!(a is Sync)
    ensures cell(apply(s,c,a),i,j)
{
    reveal(enabled); reveal(apply); let x=receiver(a); channel_pair(c,i,j); facts(s,c,i,j); if a != Action::Stutter { facts(s,c,i,x); facts(s,c,j,x); }
    match a {
        Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::Sync(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            facts(s,c,i,y); facts(s,c,j,y); facts(s,c,x,y);
            if a is Sync {
                let r=choose |r: Electing| #![trigger s.nodes[x].electing.contains(r)] s.nodes[x].electing.contains(r) && r.sid == y && r.zxid != unset() && s.nodes[x].learners.contains(y);
                if x == y { assert(r.zxid == unset()); assert(false); }
            }
        },
        _ => {},
    }
    channel_pair(c,i,j);
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    connections::preserve(s,c,a); let u=apply(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u,c,i) by { preserve_node(s,c,a,i); }
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(u,i,j) by {
        match a {
            Action::Election(ea) => { preserve_election(s,c,ea,i,j); },
            Action::Sync(x,y) => { preserve_sync(s,c,x,y,i,j); },
            Action::Crash(_) | Action::Partition(_,_) | Action::Recover(_,_) | Action::Start(_) | Action::Stutter => { preserve_environment(s,c,a,i,j); },
            _ => { preserve_protocol(s,c,a,i,j); },
        }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0
    ensures safe(b[tick],c)
    decreases tick
{
    if tick == 0 { initial_safe(c); }
    else { at(b,c,tick-1); let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a); }
}
pub proof fn disconnected_empty(s: LState,c: Constants,i: int,j: int)
    requires safe(s,c),c.servers.contains(i),c.servers.contains(j),s.election.nodes[i].role == Role::Following,s.nodes[i].leader == None
    ensures s.msgs[(i,j)].len() == 0,s.msgs[(j,i)].len() == 0
{
    channel_pair(c,i,j); channel_pair(c,j,i); facts(s,c,i,j);
}
} // verus!
