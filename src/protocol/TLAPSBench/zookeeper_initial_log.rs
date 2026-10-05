//! Before its mode header, a follower retains the history captured when election ended.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{Role,Phase};
use super::zk_election as fle;
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::zookeeper_ready as ready;
use super::zookeeper_forwarding as forwarding;
use super::zookeeper_mode_fifo as fifo;
use super::zookeeper_pending_mode as pending;
use super::temporal::Behavior;
verus! {
pub open spec fn node(s: LState,i: int) -> bool {
    s.election.nodes[i].role == Role::Following && (s.nodes[i].phase == Phase::Discovery || s.nodes[i].phase == Phase::Synchronization)
        && s.nodes[i].mode == Mode::None && !s.nodes[i].received_leader ==> s.nodes[i].initial == s.election.nodes[i].history
}
pub open spec fn safe(s: LState,c: Constants) -> bool { forall |i: int| c.servers.contains(i) ==> #[trigger] node(s,i) }
pub open spec fn context(s: LState,c: Constants) -> bool { channels::safe(s,c) && ready::safe(s,c) && forwarding::safe(s,c) && fifo::safe(s,c) && pending::safe(s,c) }
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(initial(c),i) by {}
}
pub proof fn election_node(s: LState,c: Constants,ea: fle::Action,i: int)
    requires channels::safe(s,c),safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i)
    ensures node(apply(s,c,Action::Election(ea)),i)
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(Action::Election(ea)); channels::facts(s,c,i,x); assert(node(s,i));
}
pub proof fn protocol_node(s: LState,c: Constants,a: Action,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election)
    ensures node(apply(s,c,a),i)
{
    reveal(enabled); reveal(apply); let x=receiver(a); assert(node(s,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,x)); }
    match a {
        Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,x,y); } },
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::Sync(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,x,y);
            if a is CommitSync { pending::receive_data(s,c,x,y); }
        },_ => {},
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires context(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u,i) by {
        if let Action::Election(ea)=a { election_node(s,c,ea,i); } else { protocol_node(s,c,a,i); }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0
    ensures safe(b[tick],c)
    decreases tick
{
    if tick == 0 { initial_safe(c); }
    else {
        at(b,c,tick-1); channels::at(b,c,tick-1); ready::at(b,c,tick-1); forwarding::at(b,c,tick-1); fifo::at(b,c,tick-1); pending::at(b,c,tick-1);
        let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a);
    }
}
} // verus!
