//! A continuing follower keeps its leader and cannot undo epoch acceptance or phase progress.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{Role,Phase};
use super::zk_election as fle;
use super::zookeeper_channels as channels;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn syncing(n: LServer) -> bool { n.phase == Phase::Synchronization || n.phase == Phase::Broadcast }
pub open spec fn follower(s: LState,u: LState,i: int) -> bool {
    (s.nodes[i].leader is Some ==> u.nodes[i].leader == s.nodes[i].leader)
    && (syncing(s.nodes[i]) ==> syncing(u.nodes[i]) && u.nodes[i].accepted == s.nodes[i].accepted)
    && (s.nodes[i].phase == Phase::Broadcast ==> u.nodes[i].phase == Phase::Broadcast)
    && (s.nodes[i].received_leader ==> u.nodes[i].received_leader)
}
pub proof fn election_follower(s: LState,c: Constants,ea: fle::Action,i: int)
    requires channels::safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i),s.election.nodes[i].role == Role::Following,
        apply(s,c,Action::Election(ea)).election.nodes[i].role == Role::Following
    ensures follower(s,apply(s,c,Action::Election(ea)),i)
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(Action::Election(ea)); channels::facts(s,c,i,x);
}
pub proof fn environment_follower(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),enabled(s,c,a),c.servers.contains(i),s.election.nodes[i].role == Role::Following,
        apply(s,c,a).election.nodes[i].role == Role::Following,a is Crash || a is Partition || a is Recover || a is Start || a is Stutter
    ensures follower(s,apply(s,c,a),i)
{
    reveal(enabled); reveal(apply); let x=receiver(a); if a != Action::Stutter { channels::facts(s,c,i,x); }
    if a is Crash { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,x,y); } }
    if let Action::Partition(_,y)=a { channels::facts(s,c,i,y); channels::facts(s,c,x,y); }
}
pub proof fn protocol_follower(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),enabled(s,c,a),c.servers.contains(i),s.election.nodes[i].role == Role::Following,
        apply(s,c,a).election.nodes[i].role == Role::Following,!(a is Election),!(a is Crash),!(a is Partition),!(a is Recover),!(a is Start)
    ensures follower(s,apply(s,c,a),i)
{
    reveal(enabled); reveal(apply); let x=receiver(a); if a != Action::Stutter { channels::facts(s,c,i,x); }
    match a {
        Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::Sync(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,x,y);
        },_ => {},
    }
}
pub proof fn follower_step(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),enabled(s,c,a),c.servers.contains(i),s.election.nodes[i].role == Role::Following,
        apply(s,c,a).election.nodes[i].role == Role::Following
    ensures follower(s,apply(s,c,a),i)
{
    match a {
        Action::Election(ea) => { election_follower(s,c,ea,i); },
        Action::Crash(_) | Action::Partition(_,_) | Action::Recover(_,_) | Action::Start(_) => { environment_follower(s,c,a,i); },
        _ => { protocol_follower(s,c,a,i); },
    }
}
} // verus!
