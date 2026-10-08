//! DIFF/TRUNC/SNAP precedes every data packet in a connection's sole synchronization batch.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Phase};
use super::zk_election as fle;
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::zookeeper_ready as ready;
use super::zookeeper_forwarding as forwarding;
use super::zookeeper_single_sync as single;
use super::zookeeper_buffer_origin as buffers;
use super::zookeeper_message_frames as frames;
use super::zab_connections::channel_pair;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn mode(m: Message) -> bool { m is Diff || m is Trunc || m is Snap }
pub open spec fn handshake(m: Message) -> bool { m is FollowerInfo || m is LeaderInfo }
pub open spec fn cell(s: LState,i: int,j: int,k: int) -> bool {
    0 <= k < s.msgs[(i,j)].len() && mode(s.msgs[(i,j)][k]) ==>
        buffers::clean(s.nodes[j]) && s.nodes[j].phase == Phase::Synchronization
        && forall |p: int| 0 <= p < k ==> #[trigger] handshake(s.msgs[(i,j)][p])
}
pub open spec fn safe(s: LState,c: Constants) -> bool {
    forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) ==> #[trigger] cell(s,i,j,k)
}
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    assert forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(initial(c),i,j,k) by { channel_pair(c,i,j); }
}
pub proof fn facts(s: LState,c: Constants,i: int,j: int,k: int)
    requires ready::safe(s,c),forwarding::safe(s,c),safe(s,c),c.servers.contains(i),c.servers.contains(j),0 <= k < s.msgs[(i,j)].len(),mode(s.msgs[(i,j)][k])
    ensures cell(s,i,j,k),ready::ready(s,c,i,j),s.nodes[i].forwarding.contains(j)
{
    let m=s.msgs[(i,j)][k]; assert(s.msgs[(i,j)].contains(m)); assert(ready::cell(s,c,i,j,m)); assert(forwarding::cell(s,i,j,m));
}
pub proof fn before_sync(s: LState,c: Constants,i: int,j: int)
    requires channels::safe(s,c),ready::safe(s,c),forwarding::safe(s,c),single::safe(s,c),enabled(s,c,Action::Sync(i,j))
    ensures forall |p: int| 0 <= p < s.msgs[(i,j)].len() ==> #[trigger] handshake(s.msgs[(i,j)][p])
{
    reveal(enabled); single::before_sync(s,c,i,j); channels::facts(s,c,i,j);
    assert forall |p: int| 0 <= p < s.msgs[(i,j)].len() implies #[trigger] handshake(s.msgs[(i,j)][p]) by {
        let m=s.msgs[(i,j)][p]; assert(s.msgs[(i,j)].contains(m)); assert(forwarding::cell(s,i,j,m)); assert(ready::cell(s,c,i,j,m));
    }
}
pub proof fn send_cell(s: LState,x: int,y: int,zxid: z::Zxid,at: int,how: Mode,i: int,j: int,k: int)
    requires cell(s,i,j,k),buffers::clean(s.nodes[y]),s.nodes[y].phase == Phase::Synchronization,
        forall |p: int| 0 <= p < s.msgs[(x,y)].len() ==> #[trigger] handshake(s.msgs[(x,y)][p])
    ensures cell(sync_send(s,x,y,zxid,at,how),i,j,k)
{
    let n=s.nodes[x]; let e=s.election.nodes[x]; let end=e.history.len() as int;
    let committed=if n.phase == Phase::Broadcast { n.committed.index } else { end };
    let ps=packets(e.history,at+1,end,committed); frames::sync_packets(e.history,at+1,end,committed);
    let u=sync_send(s,x,y,zxid,at,how);
    if 0 <= k < u.msgs[(i,j)].len() && mode(u.msgs[(i,j)][k]) && i == x && j == y {
        if k < s.msgs[(x,y)].len() { assert(handshake(s.msgs[(x,y)][k])); assert(false); }
        if k != s.msgs[(x,y)].len() { assert(ps.contains(u.msgs[(i,j)][k])); assert(false); }
        assert forall |p: int| 0 <= p < k implies #[trigger] handshake(u.msgs[(i,j)][p]) by { assert(handshake(s.msgs[(x,y)][p])); }
    }
}
pub proof fn follow_cell(s: LState,x: int,y: int,peer: z::Zxid,i: int,j: int,k: int)
    requires cell(s,i,j,k),buffers::clean(s.nodes[y]),s.nodes[y].phase == Phase::Synchronization,
        forall |p: int| 0 <= p < s.msgs[(x,y)].len() ==> #[trigger] handshake(s.msgs[(x,y)][p])
    ensures cell(sync_follower(s,x,y,peer),i,j,k)
{
    let n=s.nodes[x]; let e=s.election.nodes[x]; let min=n.snapshot.index+1;
    let max=if n.phase == Phase::Broadcast { n.committed.index } else { e.history.len() as int };
    let lo=if min > max { e.processed.zxid } else { e.history[min-1].zxid };
    let hi=if min > max { e.processed.zxid } else if max == 0 { z::zero() } else { e.history[max-1].zxid };
    if peer == e.processed.zxid { send_cell(s,x,y,peer,e.processed.index,Mode::Diff,i,j,k); }
    else if z::newer(peer,hi) { send_cell(s,x,y,hi,max,Mode::Trunc,i,j,k); }
    else if !z::newer(lo,peer) {
        let at=z::index(e.history,peer);
        if min <= at <= e.history.len() { send_cell(s,x,y,peer,at,Mode::Diff,i,j,k); }
        else { let at=floor_index(e.history,peer); send_cell(s,x,y,if at == 0 { z::zero() } else { e.history[at-1].zxid },at,Mode::Trunc,i,j,k); }
    } else { send_cell(s,x,y,e.processed.zxid,max,Mode::Snap,i,j,k); }
}
pub proof fn sync_cell(s: LState,c: Constants,x: int,y: int,i: int,j: int,k: int)
    requires channels::safe(s,c),ready::safe(s,c),forwarding::safe(s,c),single::safe(s,c),buffers::safe(s,c),safe(s,c),enabled(s,c,Action::Sync(x,y)),c.servers.contains(i),c.servers.contains(j)
    ensures cell(apply(s,c,Action::Sync(x,y)),i,j,k)
{
    reveal(enabled); reveal(apply); assert(cell(s,i,j,k)); before_sync(s,c,x,y); buffers::before_sync(s,c,x,y);
    let r=choose |r: Electing| #![trigger s.nodes[x].electing.contains(r)] s.nodes[x].electing.contains(r) && r.sid == y && r.zxid != unset() && s.nodes[x].learners.contains(y);
    follow_cell(s,x,y,r.zxid,i,j,k);
}
pub proof fn other_cell(s: LState,c: Constants,a: Action,i: int,j: int,k: int)
    requires channels::safe(s,c),ready::safe(s,c),forwarding::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),!(a is Sync)
    ensures cell(apply(s,c,a),i,j,k)
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(a); channel_pair(c,i,j); channels::facts(s,c,i,j);
    if a != Action::Stutter { channels::facts(s,c,i,x); channels::facts(s,c,j,x); }
    match a {
        Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y); } },
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y);
        },_ => {},
    }
    let q=s.msgs[(i,j)]; let u=apply(s,c,a); let r=u.msgs[(i,j)];
    if 0 <= k < r.len() && mode(r[k]) {
        if 0 <= k < q.len() && mode(q[k]) { facts(s,c,i,j,k); if k > 0 { assert(handshake(q[0])); } }
        if 0 <= k+1 < q.len() && mode(q[k+1]) { facts(s,c,i,j,k+1); assert(handshake(q[0])); }
        assert(0 <= k < q.len() && mode(q[k]) || 0 <= k+1 < q.len() && mode(q[k+1]));
        assert(buffers::clean(u.nodes[j])); assert(u.nodes[j].phase == Phase::Synchronization);
        assert forall |p: int| 0 <= p < k implies #[trigger] handshake(r[p]) by {
            if 0 <= k < q.len() && mode(q[k]) { assert(handshake(q[p])); }
            if 0 <= k+1 < q.len() && mode(q[k+1]) { assert(handshake(q[p+1])); }
        }
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires channels::safe(s,c),ready::safe(s,c),forwarding::safe(s,c),single::safe(s,c),buffers::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a);
    assert forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(u,i,j,k) by {
        if let Action::Sync(x,y)=a { sync_cell(s,c,x,y,i,j,k); } else { other_cell(s,c,a,i,j,k); }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0
    ensures safe(b[tick],c)
    decreases tick
{
    if tick == 0 { initial_safe(c); }
    else {
        at(b,c,tick-1); channels::at(b,c,tick-1); ready::at(b,c,tick-1); forwarding::at(b,c,tick-1); single::at(b,c,tick-1); buffers::at(b,c,tick-1);
        let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a);
    }
}
pub proof fn receive_clean(s: LState,c: Constants,i: int,j: int)
    requires safe(s,c),enabled(s,c,Action::SyncMessage(i,j))
    ensures buffers::clean(s.nodes[i]),s.nodes[i].phase == Phase::Synchronization
{
    reveal(enabled); assert(cell(s,j,i,0));
}
} // verus!
