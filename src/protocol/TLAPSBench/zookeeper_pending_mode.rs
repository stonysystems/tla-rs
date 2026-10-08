//! A forwarding connection has queued its mode header until the follower processes it.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role,Phase};
use super::zk_election as fle;
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::zookeeper_ready as ready;
use super::zookeeper_forwarding as forwarding;
use super::zookeeper_mode_fifo as fifo;
use super::zab_connections::channel_pair;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn pending(q: Seq<Message>) -> bool { exists |k: int| 0 <= k < q.len() && #[trigger] fifo::mode(q[k]) }
pub open spec fn pair(s: LState,i: int,j: int) -> bool {
    s.election.nodes[i].role == Role::Leading && i != j && s.nodes[i].forwarding.contains(j) && s.nodes[j].mode == Mode::None && !s.nodes[j].received_leader ==> pending(s.msgs[(i,j)])
}
pub open spec fn safe(s: LState,c: Constants) -> bool {
    forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) ==> #[trigger] pair(s,i,j)
}
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] pair(initial(c),i,j) by {}
}
pub proof fn send_pair(s: LState,x: int,y: int,zxid: z::Zxid,at: int,how: Mode,i: int,j: int)
    requires pair(s,i,j)
    ensures pair(sync_send(s,x,y,zxid,at,how),i,j)
{
    let u=sync_send(s,x,y,zxid,at,how);
    if u.election.nodes[i].role == Role::Leading && i != j && u.nodes[i].forwarding.contains(j) && u.nodes[j].mode == Mode::None && !u.nodes[j].received_leader {
        if i == x && j == y { let k=s.msgs[(x,y)].len() as int; assert(fifo::mode(u.msgs[(i,j)][k])); }
        else { let k=choose |k: int| #![trigger s.msgs[(i,j)][k]] 0 <= k < s.msgs[(i,j)].len() && fifo::mode(s.msgs[(i,j)][k]); assert(fifo::mode(u.msgs[(i,j)][k])); }
    }
}
pub proof fn follow_pair(s: LState,x: int,y: int,peer: z::Zxid,i: int,j: int)
    requires pair(s,i,j)
    ensures pair(sync_follower(s,x,y,peer),i,j)
{
    let n=s.nodes[x]; let e=s.election.nodes[x]; let min=n.snapshot.index+1;
    let max=if n.phase == Phase::Broadcast { n.committed.index } else { e.history.len() as int };
    let lo=if min > max { e.processed.zxid } else { e.history[min-1].zxid };
    let hi=if min > max { e.processed.zxid } else if max == 0 { z::zero() } else { e.history[max-1].zxid };
    if peer == e.processed.zxid { send_pair(s,x,y,peer,e.processed.index,Mode::Diff,i,j); }
    else if z::newer(peer,hi) { send_pair(s,x,y,hi,max,Mode::Trunc,i,j); }
    else if !z::newer(lo,peer) {
        let at=z::index(e.history,peer);
        if min <= at <= e.history.len() { send_pair(s,x,y,peer,at,Mode::Diff,i,j); }
        else { let at=floor_index(e.history,peer); send_pair(s,x,y,if at == 0 { z::zero() } else { e.history[at-1].zxid },at,Mode::Trunc,i,j); }
    } else { send_pair(s,x,y,e.processed.zxid,max,Mode::Snap,i,j); }
}
pub proof fn sync_pair(s: LState,c: Constants,x: int,y: int,i: int,j: int)
    requires safe(s,c),c.servers.contains(i),c.servers.contains(j)
    ensures pair(apply(s,c,Action::Sync(x,y)),i,j)
{
    reveal(apply); assert(pair(s,i,j));
    let r=choose |r: Electing| #![trigger s.nodes[x].electing.contains(r)] s.nodes[x].electing.contains(r) && r.sid == y && r.zxid != unset() && s.nodes[x].learners.contains(y);
    follow_pair(s,x,y,r.zxid,i,j);
}
pub proof fn other_pair(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),ready::safe(s,c),forwarding::safe(s,c),fifo::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),!(a is Sync)
    ensures pair(apply(s,c,a),i,j)
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(a); channel_pair(c,i,j); channels::facts(s,c,i,j); assert(pair(s,i,j)); assert(ready::pair(s,c,i,j));
    if a != Action::Stutter { channels::facts(s,c,i,x); channels::facts(s,c,j,x); }
    match a {
        Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y); } },
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y);
        },_ => {},
    }
    let u=apply(s,c,a);
    if u.election.nodes[i].role == Role::Leading && i != j && u.nodes[i].forwarding.contains(j) && u.nodes[j].mode == Mode::None && !u.nodes[j].received_leader {
        assert(pending(s.msgs[(i,j)]));
        let k=choose |k: int| #![trigger s.msgs[(i,j)][k]] 0 <= k < s.msgs[(i,j)].len() && fifo::mode(s.msgs[(i,j)][k]); fifo::facts(s,c,i,j,k);
        if k > 0 { assert(fifo::handshake(s.msgs[(i,j)][0])); }
        assert(0 <= k < u.msgs[(i,j)].len() && fifo::mode(u.msgs[(i,j)][k]) || 0 <= k-1 < u.msgs[(i,j)].len() && fifo::mode(u.msgs[(i,j)][k-1]));
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires channels::safe(s,c),ready::safe(s,c),forwarding::safe(s,c),fifo::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a);
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] pair(u,i,j) by {
        if let Action::Sync(x,y)=a { sync_pair(s,c,x,y,i,j); } else { other_pair(s,c,a,i,j); }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0
    ensures safe(b[tick],c)
    decreases tick
{
    if tick == 0 { initial_safe(c); }
    else { at(b,c,tick-1); channels::at(b,c,tick-1); ready::at(b,c,tick-1); forwarding::at(b,c,tick-1); fifo::at(b,c,tick-1); let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a); }
}
pub proof fn receive_data(s: LState,c: Constants,i: int,j: int)
    requires channels::safe(s,c),ready::safe(s,c),forwarding::safe(s,c),fifo::safe(s,c),safe(s,c),enabled(s,c,Action::ProposalSync(i,j)) || enabled(s,c,Action::CommitSync(i,j))
    ensures s.nodes[i].mode != Mode::None || s.nodes[i].received_leader
{
    reveal(enabled); ready::head(s,c,j,i); forwarding::head(s,c,j,i); assert(pair(s,j,i));
    if s.nodes[i].mode == Mode::None && !s.nodes[i].received_leader {
        let k=choose |k: int| #![trigger s.msgs[(j,i)][k]] 0 <= k < s.msgs[(j,i)].len() && fifo::mode(s.msgs[(j,i)][k]); assert(fifo::cell(s,j,i,k));
        if k > 0 { assert(fifo::handshake(s.msgs[(j,i)][0])); }
        assert(false);
    }
}
} // verus!
