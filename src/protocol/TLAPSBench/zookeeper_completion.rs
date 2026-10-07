//! Synchronization and broadcast require a completed discovery election.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role,Phase};
use super::zk_election as fle;
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::zookeeper_receipts as receipts;
use super::zookeeper_message_frames as frames;
use super::zookeeper_quorum_receipts as quorum;
use super::zab_connections::channel_pair;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn packet(s: LState,c: Constants,i: int,j: int,m: Message) -> bool {
    match m {
        Message::NewLeader(_) => s.election.nodes[i].role == Role::Leading && election_finished(s,c,i),
        Message::AckLd(_) => s.election.nodes[j].role == Role::Leading && election_finished(s,c,j),
        _ => true,
    }
}
pub open spec fn cell(s: LState,c: Constants,i: int,j: int,m: Message) -> bool { s.msgs[(i,j)].contains(m) ==> packet(s,c,i,j,m) }
pub open spec fn node(s: LState,c: Constants,i: int) -> bool {
    s.election.nodes[i].role == Role::Leading && (s.nodes[i].phase == Phase::Synchronization || s.nodes[i].phase == Phase::Broadcast) ==> election_finished(s,c,i)
}
pub open spec fn safe(s: LState,c: Constants) -> bool {
    (forall |i: int| c.servers.contains(i) ==> #[trigger] node(s,c,i))
    && forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) ==> #[trigger] cell(s,c,i,j,m)
}
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    let s=initial(c);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(s,c,i) by {}
    assert forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(s,c,i,j,m) by { channel_pair(c,i,j); }
}
pub proof fn head(s: LState,c: Constants,i: int,j: int)
    requires safe(s,c),c.servers.contains(i),c.servers.contains(j),s.msgs[(i,j)].len() > 0
    ensures packet(s,c,i,j,s.msgs[(i,j)][0])
{
    assert(s.msgs[(i,j)].contains(s.msgs[(i,j)][0])); assert(cell(s,c,i,j,s.msgs[(i,j)][0]));
}
pub proof fn send_origin(s: LState,x: int,y: int,zxid: z::Zxid,k: int,mode: Mode,i: int,j: int,m: Message)
    requires m is NewLeader || m is AckLd,sync_send(s,x,y,zxid,k,mode).msgs[(i,j)].contains(m),!s.msgs[(i,j)].contains(m)
    ensures i == x,j == y,m is NewLeader
{
    let n=s.nodes[x]; let e=s.election.nodes[x]; let end=e.history.len() as int;
    let committed=if n.phase == Phase::Broadcast { n.committed.index } else { end };
    frames::sync_packets(e.history,k+1,end,committed);
    let u=sync_send(s,x,y,zxid,k,mode);
    let p=choose |p: int| 0 <= p < u.msgs[(i,j)].len() && u.msgs[(i,j)][p] == m;
    if p < s.msgs[(i,j)].len() { assert(s.msgs[(i,j)].contains(m)); assert(false); }
    if !(m is NewLeader) { assert(packets(e.history,k+1,end,committed).contains(m)); assert(false); }
}
pub proof fn sync_origin(s: LState,c: Constants,x: int,y: int,i: int,j: int,m: Message)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,Action::Sync(x,y)),c.servers.contains(i),c.servers.contains(j),m is NewLeader || m is AckLd,
        apply(s,c,Action::Sync(x,y)).msgs[(i,j)].contains(m),!s.msgs[(i,j)].contains(m)
    ensures packet(apply(s,c,Action::Sync(x,y)),c,i,j,m)
{
    reveal(enabled); reveal(apply);
    let r=choose |r: Electing| s.nodes[x].electing.contains(r) && r.sid == y && r.zxid != unset() && s.nodes[x].learners.contains(y);
    let n=s.nodes[x]; let e=s.election.nodes[x]; let min=n.snapshot.index+1;
    let max=if n.phase == Phase::Broadcast { n.committed.index } else { e.history.len() as int };
    let lo=if min > max { e.processed.zxid } else { e.history[min-1].zxid };
    let hi=if min > max { e.processed.zxid } else if max == 0 { z::zero() } else { e.history[max-1].zxid };
    if r.zxid == e.processed.zxid { send_origin(s,x,y,r.zxid,e.processed.index,Mode::Diff,i,j,m); }
    else if z::newer(r.zxid,hi) { send_origin(s,x,y,hi,max,Mode::Trunc,i,j,m); }
    else if !z::newer(lo,r.zxid) {
        let k=z::index(e.history,r.zxid);
        if min <= k <= e.history.len() { send_origin(s,x,y,r.zxid,k,Mode::Diff,i,j,m); }
        else { let k=floor_index(e.history,r.zxid); send_origin(s,x,y,if k == 0 { z::zero() } else { e.history[k-1].zxid },k,Mode::Trunc,i,j,m); }
    } else { send_origin(s,x,y,e.processed.zxid,max,Mode::Snap,i,j,m); }
    quorum::finished_retained(s,c,Action::Sync(x,y),x);
}
pub proof fn other_origin(s: LState,c: Constants,a: Action,i: int,j: int,m: Message)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),m is NewLeader || m is AckLd,!(a is Sync),
        apply(s,c,a).msgs[(i,j)].contains(m),!s.msgs[(i,j)].contains(m)
    ensures packet(apply(s,c,a),c,i,j,m)
{
    reveal(enabled); reveal(apply); let x=receiver(a); channel_pair(c,i,j); channels::facts(s,c,i,j);
    if a != Action::Stutter { channels::facts(s,c,i,x); channels::facts(s,c,j,x); }
    match a {
        Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y); } },
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y);
        },_ => {},
    }
    let u=apply(s,c,a); let k=choose |k: int| 0 <= k < u.msgs[(i,j)].len() && u.msgs[(i,j)][k] == m;
    assert forall |p: int| 0 <= p < s.msgs[(i,j)].len() implies s.msgs[(i,j)][p] != m by {}
    assert(a == Action::NewLeader(i,j)); assert(m is AckLd);
    head(s,c,j,i); quorum::finished_retained(s,c,a,j);
}
pub proof fn preserve_packet(s: LState,c: Constants,a: Action,i: int,j: int,m: Message)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),apply(s,c,a).msgs[(i,j)].contains(m)
    ensures packet(apply(s,c,a),c,i,j,m)
{
    if m is NewLeader || m is AckLd {
        if s.msgs[(i,j)].contains(m) {
            assert(cell(s,c,i,j,m)); frames::step_roles(s,c,a,i,j);
            if m is NewLeader { quorum::finished_retained(s,c,a,i); } else { quorum::finished_retained(s,c,a,j); }
        } else if let Action::Sync(x,y)=a { sync_origin(s,c,x,y,i,j,m); }
        else { other_origin(s,c,a,i,j,m); }
    }
}
pub proof fn phase_origin(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures node(apply(s,c,a),c,i)
{
    let u=apply(s,c,a);
    if u.election.nodes[i].role == Role::Leading && (u.nodes[i].phase == Phase::Synchronization || u.nodes[i].phase == Phase::Broadcast) {
        if s.election.nodes[i].role == Role::Leading && (s.nodes[i].phase == Phase::Synchronization || s.nodes[i].phase == Phase::Broadcast) {
            assert(node(s,c,i)); quorum::finished_retained(s,c,a,i);
        } else {
            reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(a); if a != Action::Stutter { channels::facts(s,c,i,x); }
            if let Action::AckLd(x,y)=a { channels::facts(s,c,x,y); head(s,c,y,x); quorum::finished_retained(s,c,a,x); }
        }
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u,c,i) by { phase_origin(s,c,a,i); }
    assert forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(u,c,i,j,m) by {
        if u.msgs[(i,j)].contains(m) { preserve_packet(s,c,a,i,j,m); }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0
    ensures safe(b[tick],c)
    decreases tick
{
    if tick == 0 { initial_safe(c); }
    else { at(b,c,tick-1); channels::at(b,c,tick-1); receipts::at(b,c,tick-1); let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a); }
}
} // verus!
