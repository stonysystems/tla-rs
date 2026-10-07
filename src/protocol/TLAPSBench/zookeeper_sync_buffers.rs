//! TRUNC/SNAP commit processing drains actual pending transactions into the retained history.
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
use super::zookeeper_buffer_origin as buffers;
use super::zookeeper_online as online;
use super::zookeeper_initial_log as initial_log;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn node(s: LState,i: int) -> bool {
    let n=s.nodes[i]; let h=s.election.nodes[i].history;
    s.election.nodes[i].role == Role::Following && n.phase == Phase::Synchronization && !n.received_leader && (n.mode == Mode::Trunc || n.mode == Mode::Snap) ==>
        n.commits.len() == 0 && n.initial.len() <= h.len() && (n.initial.len() < h.len() ==> n.committed == fle::latest(h))
}
pub open spec fn safe(s: LState,c: Constants) -> bool { forall |i: int| c.servers.contains(i) ==> #[trigger] node(s,i) }
pub open spec fn context(s: LState,c: Constants) -> bool {
    channels::safe(s,c) && ready::safe(s,c) && buffers::safe(s,c) && fifo::safe(s,c) && initial_log::safe(s,c) && online::safe(s,c)
}
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(initial(c),i) by {}
}
pub proof fn last_committed_shape(s: LState,i: int)
    requires node(s,i),s.election.nodes[i].role == Role::Following,s.nodes[i].phase == Phase::Synchronization,!s.nodes[i].received_leader,
        s.nodes[i].mode == Mode::Trunc || s.nodes[i].mode == Mode::Snap
    ensures last_committed(s,i) == fle::latest(s.election.nodes[i].history)
{}
pub proof fn election_node(s: LState,c: Constants,ea: fle::Action,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i)
    ensures node(apply(s,c,Action::Election(ea)),i)
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(Action::Election(ea)); channels::facts(s,c,i,x); assert(node(s,i));
}
pub proof fn other_node(s: LState,c: Constants,a: Action,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),!(a is SyncMessage),!(a is CommitSync)
    ensures node(apply(s,c,a),i)
{
    reveal(enabled); reveal(apply); let x=receiver(a); assert(node(s,i)); assert(online::node(s,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,x)); assert(online::node(s,x)); }
    match a {
        Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,x,y); } },
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::Sync(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,x,y);
            if a is LeaderInfo && s.nodes[x].phase == Phase::Discovery { buffers::discovery_clean(s,c,x); }
        },_ => {},
    }
}
pub proof fn mode_node(s: LState,c: Constants,x: int,y: int,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,Action::SyncMessage(x,y)),c.servers.contains(i)
    ensures node(apply(s,c,Action::SyncMessage(x,y)),i)
{
    reveal(enabled); reveal(apply); channels::facts(s,c,i,x); channels::facts(s,c,i,y); channels::facts(s,c,x,y);
    assert(node(s,i)); assert(node(s,x)); fifo::receive_clean(s,c,x,y); assert(initial_log::node(s,x));
}
pub proof fn commit_node(s: LState,c: Constants,x: int,y: int,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,Action::CommitSync(x,y)),c.servers.contains(i)
    ensures node(apply(s,c,Action::CommitSync(x,y)),i)
{
    reveal(enabled); reveal(apply); channels::facts(s,c,i,x); channels::facts(s,c,i,y); channels::facts(s,c,x,y);
    assert(node(s,i)); assert(node(s,x));
    if !s.nodes[x].received_leader && (s.nodes[x].mode == Mode::Trunc || s.nodes[x].mode == Mode::Snap) { last_committed_shape(s,x); }
}
pub proof fn protocol_node(s: LState,c: Constants,a: Action,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election)
    ensures node(apply(s,c,a),i)
{
    match a {
        Action::SyncMessage(x,y) => { mode_node(s,c,x,y,i); },
        Action::CommitSync(x,y) => { commit_node(s,c,x,y,i); },
        _ => { other_node(s,c,a,i); },
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
        at(b,c,tick-1); channels::at(b,c,tick-1); ready::at(b,c,tick-1); buffers::at(b,c,tick-1); fifo::at(b,c,tick-1); initial_log::at(b,c,tick-1); online::at(b,c,tick-1);
        let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a);
    }
}
pub proof fn flush_has_pending(s: LState,c: Constants,i: int,j: int)
    requires channels::safe(s,c),ready::safe(s,c),forwarding::safe(s,c),fifo::safe(s,c),pending::safe(s,c),safe(s,c),enabled(s,c,Action::CommitSync(i,j)),
        s.nodes[i].mode != Mode::Diff,!s.nodes[i].received_leader,last_committed(s,i).index+1 <= last_queued(s,i).index
    ensures s.nodes[i].pending.len() > 0,last_committed(s,i).index == s.election.nodes[i].history.len()
{
    reveal(enabled); pending::receive_data(s,c,i,j); assert(node(s,i)); last_committed_shape(s,i);
}
} // verus!
