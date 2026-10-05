//! Committed indices and buffered commit references stay within retained transactions.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role,Phase,Txn,Zxid};
use super::zk_election as fle;
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::zookeeper_ready as ready;
use super::zookeeper_buffer_origin as origin;
use super::zookeeper_mode_fifo as fifo;
use super::zookeeper_sync_buffers as buffers;
use super::zookeeper_forwarding as forwarding;
use super::zookeeper_pending_mode as pending;
use super::zookeeper_initial_log as initial_log;
use super::zookeeper_log_order as order;
use super::zookeeper_log_math as logs;
use super::zookeeper_leader_logs as leaders;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn found(h: Seq<Txn>,zxid: Zxid) -> bool { exists |k: int| 0 <= k < h.len() && (#[trigger] h[k]).zxid == zxid }
pub open spec fn node(s: LState,i: int) -> bool {
    let n=s.nodes[i]; let e=s.election.nodes[i];
    0 <= n.committed.index <= e.history.len()
    && 0 <= n.snapshot.index <= e.history.len()
    && (e.role == Role::Following && n.phase == Phase::Synchronization ==>
        n.initial.len() <= e.history.len() && (n.commits.len() > 0 ==> found(complete_history(s,i),n.commits.last())))
}
pub open spec fn safe(s: LState,c: Constants) -> bool { forall |i: int| c.servers.contains(i) ==> #[trigger] node(s,i) }
pub open spec fn context(s: LState,c: Constants) -> bool {
    channels::safe(s,c) && ready::safe(s,c) && origin::safe(s,c) && fifo::safe(s,c)
    && buffers::safe(s,c) && initial_log::safe(s,c) && order::safe(s,c) && forwarding::safe(s,c) && pending::safe(s,c)
}
pub proof fn index_found(h: Seq<Txn>,zxid: Zxid)
    requires logs::shape(h),found(h,zxid)
    ensures 0 <= z::index(h,zxid) <= h.len()
{
    let k=choose |k: int| 0 <= k < h.len() && h[k].zxid == zxid;
    let q=Set::range(1,h.len() as int+1).filter(|p: int| h[p-1].zxid == zxid);
    assert(q =~= set![k+1]) by {
        assert forall |p: int| q.contains(p) implies p == k+1 by {
            if p-1 < k { logs::ordered(h,p-1,k); } else { logs::ordered(h,k,p-1); }
        }
    }
    assert(q.contains(k+1));
    if zxid != z::zero() { assert(q.contains(z::index(h,zxid))); }
}
pub proof fn extend_found(h: Seq<Txn>,q: Seq<Txn>,zxid: Zxid)
    requires found(h,zxid),h.len() <= q.len(),forall |k: int| 0 <= k < h.len() ==> #[trigger] z::equal(h[k],q[k])
    ensures found(q,zxid)
{
    let k=choose |k: int| 0 <= k < h.len() && h[k].zxid == zxid;
    assert(z::equal(h[k],q[k])); assert(q[k].zxid == zxid);
}
pub proof fn last_bound(s: LState,i: int)
    requires node(s,i),order::node(s,i),s.election.nodes[i].role == Role::Following,s.nodes[i].phase == Phase::Synchronization || s.nodes[i].phase == Phase::Broadcast
    ensures 0 <= last_committed(s,i).index <= complete_history(s,i).len()
{
    if s.nodes[i].phase == Phase::Synchronization && s.nodes[i].commits.len() > 0 { index_found(complete_history(s,i),s.nodes[i].commits.last()); }
}
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(initial(c),i) by {}
}
pub proof fn election_node(s: LState,c: Constants,ea: fle::Action,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i)
    ensures node(apply(s,c,Action::Election(ea)),i)
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(Action::Election(ea)); channels::facts(s,c,i,x); assert(node(s,i));
}
pub proof fn sync_node(s: LState,c: Constants,x: int,y: int,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,Action::Sync(x,y)),c.servers.contains(i)
    ensures node(apply(s,c,Action::Sync(x,y)),i)
{
    reveal(enabled); reveal(apply); channels::facts(s,c,i,x); channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(node(s,i));
    leaders::sync_step(s,c,x,y,i);
    let u=apply(s,c,Action::Sync(x,y));
    assert(s.election.nodes[i].history.len() == u.election.nodes[i].history.len());
}
pub proof fn mode_node(s: LState,c: Constants,x: int,y: int,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,Action::SyncMessage(x,y)),c.servers.contains(i)
    ensures node(apply(s,c,Action::SyncMessage(x,y)),i)
{
    reveal(enabled); reveal(apply); channels::facts(s,c,i,x); channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(node(s,i)); assert(node(s,x));
    fifo::receive_clean(s,c,x,y);
}
pub proof fn proposal_node(s: LState,c: Constants,a: Action,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),a is ProposalSync || a is Proposal
    ensures node(apply(s,c,a),i)
{
    reveal(enabled); reveal(apply); let x=receiver(a); let y=if let Action::ProposalSync(_,y)=a { y } else { a->Proposal_1 };
    channels::facts(s,c,i,x); channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(node(s,i)); assert(node(s,x));
    let u=apply(s,c,a);
    if s.election.nodes[i].role == Role::Following && s.nodes[i].phase == Phase::Synchronization && s.nodes[i].commits.len() > 0 {
        assert forall |p: int| 0 <= p < complete_history(s,i).len() implies #[trigger] z::equal(complete_history(s,i)[p],complete_history(u,i)[p]) by {}
        extend_found(complete_history(s,i),complete_history(u,i),s.nodes[i].commits.last());
    }
}
pub proof fn commit_sync_node(s: LState,c: Constants,x: int,y: int,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,Action::CommitSync(x,y)),c.servers.contains(i)
    ensures node(apply(s,c,Action::CommitSync(x,y)),i)
{
    reveal(enabled); reveal(apply); channels::facts(s,c,i,x); channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(node(s,i)); assert(node(s,x)); assert(order::node(s,x));
    let u=apply(s,c,Action::CommitSync(x,y)); let k=last_committed(s,x).index+1;
    last_bound(s,x);
    pending::receive_data(s,c,x,y);
    if let Message::Commit(zxid)=s.msgs[(y,x)][0] {
        if k <= last_queued(s,x).index && z::next_zxid(last_committed(s,x).zxid,zxid) && zxid == transaction(s,x,k).zxid {
            assert(0 <= k-1 < complete_history(s,x).len()); assert(complete_history(s,x)[k-1].zxid == zxid);
            if s.nodes[x].mode == Mode::Diff || s.nodes[x].received_leader { assert(found(complete_history(u,x),zxid)); }
            else {
                // In this branch old buffered commits are empty and history grows by one.
                buffers::flush_has_pending(s,c,x,y);
                assert(buffers::node(s,x));
            }
        }
    }
}
pub proof fn finish_node(s: LState,c: Constants,a: Action,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),a is NewLeader || a is UpToDate
    ensures node(apply(s,c,a),i)
{
    reveal(enabled); reveal(apply); let x=receiver(a); let y=if let Action::NewLeader(_,y)=a { y } else { a->UpToDate_1 };
    channels::facts(s,c,i,x); channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(node(s,i)); assert(node(s,x)); assert(order::node(s,x)); ready::head(s,c,y,x);
    last_bound(s,x); let u=apply(s,c,a);
    if a is NewLeader { assert(complete_history(u,x) =~= complete_history(s,x)); }
}
pub proof fn other_node(s: LState,c: Constants,a: Action,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        !(a is Election),!(a is Sync),!(a is SyncMessage),!(a is ProposalSync),!(a is Proposal),!(a is CommitSync),!(a is NewLeader),!(a is UpToDate)
    ensures node(apply(s,c,a),i)
{
    reveal(enabled); reveal(apply); let x=receiver(a); let u=apply(s,c,a); assert(node(s,i));
    if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,x)); }
    match a {
        Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,x,y); } },
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::AckLd(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,x,y);
            if a is LeaderInfo && s.nodes[x].phase == Phase::Discovery { origin::discovery_clean(s,c,x); assert(initial_log::node(s,x)); }
        },_ => {},
    }
    assert(0 <= u.nodes[i].committed.index <= u.election.nodes[i].history.len());
    if u.election.nodes[i].role == Role::Following && u.nodes[i].phase == Phase::Synchronization {
        assert(u.nodes[i].initial.len() <= u.election.nodes[i].history.len());
        if u.nodes[i].commits.len() > 0 { assert(found(complete_history(u,i),u.nodes[i].commits.last())); }
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires context(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(apply(s,c,a),i) by {
        match a {
            Action::Election(ea) => { election_node(s,c,ea,i); },Action::Sync(x,y) => { sync_node(s,c,x,y,i); },
            Action::SyncMessage(x,y) => { mode_node(s,c,x,y,i); },Action::ProposalSync(_,_) | Action::Proposal(_,_) => { proposal_node(s,c,a,i); },
            Action::CommitSync(x,y) => { commit_sync_node(s,c,x,y,i); },Action::NewLeader(_,_) | Action::UpToDate(_,_) => { finish_node(s,c,a,i); },
            _ => { other_node(s,c,a,i); },
        }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0
    ensures safe(b[tick],c)
    decreases tick
{
    if tick == 0 { initial_safe(c); }
    else {
        at(b,c,tick-1); channels::at(b,c,tick-1); ready::at(b,c,tick-1); origin::at(b,c,tick-1); fifo::at(b,c,tick-1);
        buffers::at(b,c,tick-1); initial_log::at(b,c,tick-1); order::at(b,c,tick-1); forwarding::at(b,c,tick-1); pending::at(b,c,tick-1);
        let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a);
    }
}
} // verus!
