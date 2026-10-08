//! Retained histories, pending transactions, and SNAP payloads have recorded proposals.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role,Phase,Txn,Proposal};
use super::zk_election as fle;
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::zookeeper_proposal_records as records;
use super::zookeeper_leader_bounds as bounds;
use super::zookeeper_leader_logs as leaders;
use super::zookeeper_ready as ready;
use super::zookeeper_forwarding as forwarding;
use super::zookeeper_mode_fifo as fifo;
use super::zookeeper_pending_mode as pending;
use super::zookeeper_sync_buffers as buffers;
use super::zab_connections::channel_pair;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn sequence(s: LState,h: Seq<Txn>) -> bool {
    forall |k: int| 0 <= k < h.len() ==> #[trigger] records::recorded(s,h[k].zxid,h[k].value)
}
pub open spec fn node(s: LState,i: int) -> bool { sequence(s,s.election.nodes[i].history) && sequence(s,s.nodes[i].pending) }
pub open spec fn packet(s: LState,m: Message) -> bool { match m { Message::Snap(_,h) => sequence(s,h),_ => true } }
pub open spec fn cell(s: LState,i: int,j: int,m: Message) -> bool { s.msgs[(i,j)].contains(m) ==> packet(s,m) }
pub open spec fn safe(s: LState,c: Constants) -> bool {
    (forall |i: int| c.servers.contains(i) ==> #[trigger] node(s,i))
    && forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) ==> #[trigger] cell(s,i,j,m)
}
pub open spec fn context(s: LState,c: Constants) -> bool {
    channels::safe(s,c) && records::safe(s,c) && bounds::safe(s,c) && ready::safe(s,c) && forwarding::safe(s,c) && fifo::safe(s,c) && pending::safe(s,c) && buffers::safe(s,c)
}
pub proof fn retained(s: LState,u: LState,h: Seq<Txn>)
    requires s.proposals.subset_of(u.proposals),sequence(s,h)
    ensures sequence(u,h)
{
    assert forall |k: int| 0 <= k < h.len() implies #[trigger] records::recorded(u,h[k].zxid,h[k].value) by { records::retained(s,u,h[k].zxid,h[k].value); }
}
pub proof fn same_contents(s: LState,h: Seq<Txn>,k: Seq<Txn>)
    requires sequence(s,h),super::zab_log_math::same(h,k)
    ensures sequence(s,k)
{
    assert forall |p: int| 0 <= p < k.len() implies #[trigger] records::recorded(s,k[p].zxid,k[p].value) by { assert(z::equal(h[p],k[p])); }
}
pub proof fn sub_sequence(s: LState,h: Seq<Txn>,end: int)
    requires sequence(s,h),end <= h.len()
    ensures sequence(s,super::zookeeper::sub(h,1,end))
{
    let q=super::zookeeper::sub(h,1,end);
    assert forall |k: int| 0 <= k < q.len() implies #[trigger] records::recorded(s,q[k].zxid,q[k].value) by {}
}
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    let s=initial(c);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(s,i) by { records::bootstrap(c,i); }
    assert forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(s,i,j,m) by { channel_pair(c,i,j); }
}
pub proof fn election_node(s: LState,c: Constants,ea: fle::Action,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i)
    ensures node(apply(s,c,Action::Election(ea)),i)
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let u=apply(s,c,Action::Election(ea)); let x=receiver(Action::Election(ea)); channels::facts(s,c,i,x); assert(node(s,i));
    super::zk_election_types::history_frame(s.election,c,ea,i);
    same_contents(s,s.election.nodes[i].history,u.election.nodes[i].history);
    records::monotonic(s,c,Action::Election(ea)); retained(s,u,u.election.nodes[i].history);
    assert(sequence(s,u.nodes[i].pending)); retained(s,u,u.nodes[i].pending);
}
pub proof fn sync_node(s: LState,c: Constants,x: int,y: int,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,Action::Sync(x,y)),c.servers.contains(i)
    ensures node(apply(s,c,Action::Sync(x,y)),i)
{
    reveal(enabled); reveal(apply); let a=Action::Sync(x,y); let u=apply(s,c,a); channels::facts(s,c,i,x); channels::facts(s,c,x,y); assert(node(s,i));
    records::monotonic(s,c,a); retained(s,u,s.election.nodes[i].history); retained(s,u,s.nodes[i].pending);
    leaders::sync_step(s,c,x,y,i);
    assert(s.election.nodes[i].history.len() == u.election.nodes[i].history.len());
    same_contents(u,s.election.nodes[i].history,u.election.nodes[i].history);
}
pub proof fn protocol_node(s: LState,c: Constants,a: Action,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),!(a is Sync)
    ensures node(apply(s,c,a),i)
{
    reveal(enabled); reveal(apply); let x=receiver(a); let u=apply(s,c,a); assert(node(s,i)); records::monotonic(s,c,a);
    retained(s,u,s.election.nodes[i].history); retained(s,u,s.nodes[i].pending);
    if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,x)); retained(s,u,s.election.nodes[x].history); retained(s,u,s.nodes[x].pending); }
    match a {
        Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,x,y); } },
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,x,y);
            if s.msgs[(y,x)].len() > 0 {
                let m=s.msgs[(y,x)][0]; assert(s.msgs[(y,x)].contains(m)); assert(cell(s,y,x,m)); assert(records::cell(s,y,x,m));
                if let Message::Snap(_,h)=m { retained(s,u,h); }
                if let Message::Proposal(zxid,value)=m { records::retained(s,u,zxid,value); }
            }
            if a is CommitSync && s.nodes[x].mode != Mode::Diff && !s.nodes[x].received_leader && last_committed(s,x).index+1 <= last_queued(s,x).index {
                buffers::flush_has_pending(s,c,x,y);
            }
        },
        Action::Request(_) => {
            let h=u.election.nodes[x].history; let t=h[h.len()-1]; let p=Proposal { source: x,epoch: s.nodes[x].accepted,zxid: t.zxid,value: t.value }; assert(u.proposals.contains(p)); assert(records::recorded(u,t.zxid,t.value));
        },_ => {},
    }
    let h=u.election.nodes[i].history; let q=u.nodes[i].pending;
    assert forall |k: int| 0 <= k < h.len() implies #[trigger] records::recorded(u,h[k].zxid,h[k].value) by {}
    assert forall |k: int| 0 <= k < q.len() implies #[trigger] records::recorded(u,q[k].zxid,q[k].value) by {}
}
pub proof fn sync_send_packet(s: LState,x: int,y: int,peer: z::Zxid,k: int,mode: Mode,i: int,j: int,m: Message)
    requires sequence(s,s.election.nodes[x].history),mode != Mode::None,mode == Mode::Snap ==> k <= s.election.nodes[x].history.len(),
        sync_send(s,x,y,peer,k,mode).msgs[(i,j)].contains(m),!s.msgs[(i,j)].contains(m)
    ensures packet(sync_send(s,x,y,peer,k,mode),m)
{
    let u=sync_send(s,x,y,peer,k,mode);
    if let Message::Snap(_,h)=m {
        let pos=choose |pos: int| 0 <= pos < u.msgs[(i,j)].len() && u.msgs[(i,j)][pos] == m;
        if pos < s.msgs[(i,j)].len() { assert(s.msgs[(i,j)].contains(m)); assert(false); }
        // Transaction packets contain only proposals and commits.
        no_snap(s.election.nodes[x].history,k+1,s.election.nodes[x].history.len() as int,if s.nodes[x].phase == Phase::Broadcast { s.nodes[x].committed.index } else { s.election.nodes[x].history.len() as int },m);
        assert(mode == Mode::Snap); sub_sequence(s,s.election.nodes[x].history,k); retained(s,u,h);
    }
}
pub proof fn no_snap(h: Seq<Txn>,first: int,end: int,committed: int,m: Message)
    requires m is Snap
    ensures !packets(h,first,end,committed).contains(m)
    decreases if end >= first { end-first+1 } else { 0 }
{
    reveal(packets);
    if end >= first {
        no_snap(h,first,end-1,committed,m);
        let q=packets(h,first,end,committed);
        assert forall |p: int| 0 <= p < q.len() implies q[p] != m by {}
    }
}
pub proof fn sync_packet(s: LState,c: Constants,x: int,y: int,i: int,j: int,m: Message)
    requires context(s,c),safe(s,c),enabled(s,c,Action::Sync(x,y)),c.servers.contains(i),c.servers.contains(j),
        apply(s,c,Action::Sync(x,y)).msgs[(i,j)].contains(m),!s.msgs[(i,j)].contains(m)
    ensures packet(apply(s,c,Action::Sync(x,y)),m)
{
    reveal(enabled); reveal(apply); assert(node(s,x)); assert(bounds::node(s,x));
    let r=choose |r: Electing| #![trigger s.nodes[x].electing.contains(r)] s.nodes[x].electing.contains(r) && r.sid == y && r.zxid != unset() && s.nodes[x].learners.contains(y);
    let n=s.nodes[x]; let e=s.election.nodes[x]; let min=n.snapshot.index+1;
    let max=if n.phase == Phase::Broadcast { n.committed.index } else { e.history.len() as int };
    let lo=if min > max { e.processed.zxid } else { e.history[min-1].zxid };
    let hi=if min > max { e.processed.zxid } else if max == 0 { z::zero() } else { e.history[max-1].zxid };
    if r.zxid == e.processed.zxid { sync_send_packet(s,x,y,r.zxid,e.processed.index,Mode::Diff,i,j,m); }
    else if z::newer(r.zxid,hi) { sync_send_packet(s,x,y,hi,max,Mode::Trunc,i,j,m); }
    else if !z::newer(lo,r.zxid) {
        let k=z::index(e.history,r.zxid);
        if min <= k <= e.history.len() { sync_send_packet(s,x,y,r.zxid,k,Mode::Diff,i,j,m); }
        else { let k=floor_index(e.history,r.zxid); sync_send_packet(s,x,y,if k == 0 { z::zero() } else { e.history[k-1].zxid },k,Mode::Trunc,i,j,m); }
    } else { sync_send_packet(s,x,y,e.processed.zxid,max,Mode::Snap,i,j,m); }
    let mid=sync_follower(s,x,y,r.zxid); assert(packet(mid,m)); if let Message::Snap(_,h)=m { retained(mid,apply(s,c,Action::Sync(x,y)),h); }
}
pub proof fn other_packet(s: LState,c: Constants,a: Action,i: int,j: int,m: Message)
    requires channels::safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),!(a is Sync),
        apply(s,c,a).msgs[(i,j)].contains(m),!s.msgs[(i,j)].contains(m)
    ensures !(m is Snap)
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
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires context(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a); records::monotonic(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u,i) by {
        match a { Action::Election(ea) => { election_node(s,c,ea,i); },Action::Sync(x,y) => { sync_node(s,c,x,y,i); },_ => { protocol_node(s,c,a,i); } }
    }
    assert forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(u,i,j,m) by {
        if u.msgs[(i,j)].contains(m) {
            if s.msgs[(i,j)].contains(m) { assert(cell(s,i,j,m)); if let Message::Snap(_,h)=m { retained(s,u,h); } }
            else if let Action::Sync(x,y)=a { sync_packet(s,c,x,y,i,j,m); }
            else { other_packet(s,c,a,i,j,m); }
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
        at(b,c,tick-1); channels::at(b,c,tick-1); records::at(b,c,tick-1); bounds::at(b,c,tick-1); ready::at(b,c,tick-1); forwarding::at(b,c,tick-1); fifo::at(b,c,tick-1); pending::at(b,c,tick-1); buffers::at(b,c,tick-1);
        let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a);
    }
}
} // verus!
