//! Reachable map domains and configured-server references for low-level ZooKeeper.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role};
use super::zk_election as fle;
use super::zk_election_types as election;
use super::zab_connections::channel_pair;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn node(n: LServer,c: Constants) -> bool {
    n.learners.subset_of(c.servers) && (n.leader is Some ==> c.servers.contains(n.leader.unwrap()))
}
pub open spec fn shape(s: LState,c: Constants) -> bool {
    s.nodes.dom() == c.servers && s.msgs.dom() == z::channels(c) && s.partition.dom() == z::channels(c)
    && s.epoch_leader.dom() == Set::range(1,c.max_epoch+1) && election::safe(s.election,c)
    && forall |i: int| c.servers.contains(i) ==> #[trigger] node(s.nodes[i],c)
}
pub proof fn initial_shape(c: Constants)
    ensures shape(initial(c),c)
{
    let s=initial(c); election::initial_safe(c); assert(s.nodes.dom() =~= c.servers); assert(s.msgs.dom() =~= z::channels(c)); assert(s.partition.dom() =~= z::channels(c));
    assert(s.epoch_leader.dom() =~= Set::range(1,c.max_epoch+1));
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(s.nodes[i],c) by {}
}
pub proof fn shut_follower_shape(s: LState,c: Constants,i: int)
    requires shape(s,c),c.servers.contains(i)
    ensures shape(shut_follower(s,c,i),c)
{
    election::timeout_ok(s.election,c,i); let u=shut_follower(s,c,i); assert(u.nodes.dom() =~= c.servers);
    assert forall |j: int| c.servers.contains(j) implies #[trigger] node(u.nodes[j],c) by { assert(node(s.nodes[j],c)); }
}
pub proof fn shut_leader_shape(s: LState,c: Constants,i: int)
    requires shape(s,c),c.servers.contains(i)
    ensures shape(shut_leader(s,c,i),c)
{
    let u=shut_leader(s,c,i); election::same_messages(s.election,u.election,c); assert(u.nodes.dom() =~= c.servers); assert(u.msgs.dom() =~= z::channels(c)); assert(u.election.nodes.dom() =~= c.servers);
    assert forall |j: int| c.servers.contains(j) implies #[trigger] node(u.nodes[j],c) by { assert(node(s.nodes[j],c)); }
    assert forall |j: int| c.servers.contains(j) implies #[trigger] election::node(u.election.nodes[j],c,j) by {
        assert(election::node(s.election.nodes[j],c,j)); if s.nodes[i].learners.insert(i).contains(j) { election::reset_ok(s.election.nodes[j],c,j,true); }
    }
}
pub proof fn remove_shape(s: LState,c: Constants,i: int,j: int)
    requires shape(s,c),c.servers.contains(i)
    ensures shape(remove_learner(s,i,j),c)
{
    let u=remove_learner(s,i,j); assert(u.nodes.dom() =~= c.servers);
    assert forall |k: int| c.servers.contains(k) implies #[trigger] node(u.nodes[k],c) by { assert(node(s.nodes[k],c)); }
}
pub proof fn clean_shape(s: LState,c: Constants,i: int,j: int)
    requires shape(s,c),c.servers.contains(i),c.servers.contains(j)
    ensures shape(clean(s,i,j),c)
{
    channel_pair(c,i,j); channel_pair(c,j,i); assert(clean(s,i,j).msgs.dom() =~= z::channels(c));
}
pub proof fn lose_shape(s: LState,c: Constants,i: int,j: int)
    requires shape(s,c),c.servers.contains(i),c.servers.contains(j)
    ensures shape(lose_follower(s,c,i,j),c)
{
    if z::quorum(s.nodes[i].learners.remove(j),c) {
        remove_shape(s,c,i,j); shut_follower_shape(remove_learner(s,i,j),c,j); clean_shape(shut_follower(remove_learner(s,i,j),c,j),c,i,j);
    } else { shut_leader_shape(s,c,i); }
}
#[verifier::spinoff_prover]
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires shape(s,c),enabled(s,c,a)
    ensures shape(apply(s,c,a),c)
{
    hide(floor_index);
    let u=apply(s,c,a); let i=receiver(a); reveal(enabled); reveal(apply);
    if a != Action::Stutter { assert(node(s.nodes[i],c)); assert(election::node(s.election.nodes[i],c,i)); }
    match a {
        Action::Election(ea) => { election::preserve(s.election,c,ea); },
        Action::Crash(_) => { match s.election.nodes[i].role {
            Role::Looking => {},Role::Leading => { shut_leader_shape(s,c,i); },Role::Following => { match s.nodes[i].leader {
                Some(j) => { lose_shape(s,c,j,i); },None => { shut_follower_shape(s,c,i); },
            } },
        } },
        Action::Partition(_,j) => { channel_pair(c,i,j); channel_pair(c,j,i); if s.election.nodes[i].role == Role::Leading { lose_shape(s,c,i,j); } },
        Action::Recover(_,j) => { channel_pair(c,i,j); channel_pair(c,j,i); },
        Action::Connect(_,j) | Action::FollowerInfo(_,j) | Action::LeaderInfo(_,j) | Action::AckEpoch(_,j) | Action::Sync(_,j) | Action::SyncMessage(_,j) | Action::ProposalSync(_,j) | Action::CommitSync(_,j) | Action::NewLeader(_,j) | Action::AckLd(_,j) | Action::UpToDate(_,j) | Action::Proposal(_,j) | Action::Ack(_,j) | Action::Commit(_,j) => {
            channel_pair(c,i,j); channel_pair(c,j,i); assert(node(s.nodes[j],c));
            if let Action::LeaderInfo(_,_) = a { shut_follower_shape(s,c,i); remove_shape(shut_follower(s,c,i),c,j,i); clean_shape(remove_learner(shut_follower(s,c,i),j,i),c,i,j); }
            if a is AckEpoch { shut_leader_shape(s,c,i); }
        },
        _ => {},
    }
    assert(u.nodes.dom() =~= c.servers); assert(u.msgs.dom() =~= z::channels(c)); assert(u.partition.dom() =~= z::channels(c));
    assert(u.epoch_leader.dom() =~= Set::range(1,c.max_epoch+1));
    assert forall |j: int| c.servers.contains(j) implies #[trigger] node(u.nodes[j],c) by {
        assert(node(s.nodes[j],c));
        if let Action::Election(ea)=a { assert(election::node(u.election.nodes[j],c,j)); }
    }
    assert(u.election.nodes.dom() =~= c.servers);
    assert forall |j: int| c.servers.contains(j) implies #[trigger] election::node(u.election.nodes[j],c,j) by {
        assert(election::node(s.election.nodes[j],c,j));
        if let Action::Election(ea)=a { assert(election::safe(fle::apply(s.election,c,ea),c)); }
    }
    if u.election.msgs == s.election.msgs { election::same_messages(s.election,u.election,c); }
    assert(election::safe(u.election,c));
}
pub open spec fn safety_spec(b: Behavior<LState>,c: Constants) -> bool {
    valid_constants(c) && b[0] == initial(c) && (forall |tick: int| tick >= 0 ==> b.dom().contains(tick))
    && forall |tick: int| tick >= 0 ==> #[trigger] next(b[tick],b[tick+1],c)
}
pub proof fn step(b: Behavior<LState>,c: Constants,tick: int) -> (a: Action)
    requires safety_spec(b,c),tick >= 0
    ensures enabled(b[tick],c,a),b[tick+1] == apply(b[tick],c,a)
{
    assert(next(b[tick],b[tick+1],c)); reveal(next); choose |a: Action| #[trigger] enabled(b[tick],c,a) && b[tick+1] == apply(b[tick],c,a)
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires safety_spec(b,c),tick >= 0
    ensures shape(b[tick],c)
    decreases tick
{
    if tick == 0 { initial_shape(c); }
    else { at(b,c,tick-1); let a=step(b,c,tick-1); preserve(b[tick-1],c,a); }
}
} // verus!
