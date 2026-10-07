//! Transaction order and epoch bounds through ZooKeeper synchronization.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role,Phase,Txn};
use super::zk_election as fle;
use super::zookeeper_log_math as logs;
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::zookeeper_epochs as epochs;
use super::zookeeper_ready as ready;
use super::zookeeper_forwarding as forwarding;
use super::zookeeper_buffer_origin as origin;
use super::zookeeper_mode_fifo as fifo;
use super::zookeeper_pending_mode as pending;
use super::zookeeper_sync_buffers as buffers;
use super::zookeeper_leader_bounds as bounds;
use super::zookeeper_leader_logs as leaders;
use super::zookeeper_active_epoch as active;
use super::zookeeper_completion as completion;
use super::zookeeper_small_cluster as small;
use super::zab_connections::channel_pair;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn sequence(h: Seq<Txn>,e: int) -> bool { logs::shape(h) && logs::bounded(h,e) }
pub open spec fn node(s: LState,i: int) -> bool {
    let n=s.nodes[i]; let e=s.election.nodes[i];
    sequence(e.history,n.accepted) && 0 <= n.committed.index && 0 <= n.snapshot.index && 0 <= e.processed.index
    && (e.role == Role::Following && n.phase == Phase::Synchronization ==> sequence(complete_history(s,i),n.accepted))
    && (e.role == Role::Following && n.phase == Phase::Broadcast ==> n.pending.len() == 0)
}
pub open spec fn payload(m: Message,e: int) -> bool {
    match m { Message::Proposal(zxid,_) => 0 <= zxid.epoch <= e && zxid.counter > 0,Message::Snap(_,h) => sequence(h,e),_ => true }
}
pub open spec fn cell(s: LState,i: int,j: int,m: Message) -> bool { s.msgs[(i,j)].contains(m) ==> payload(m,s.nodes[j].accepted) }
pub open spec fn safe(s: LState,c: Constants) -> bool {
    (forall |i: int| c.servers.contains(i) ==> #[trigger] node(s,i))
    && forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) ==> #[trigger] cell(s,i,j,m)
}
pub open spec fn context(s: LState,c: Constants) -> bool {
    channels::safe(s,c) && epochs::safe(s,c) && ready::safe(s,c) && forwarding::safe(s,c) && origin::safe(s,c) && fifo::safe(s,c)
    && pending::safe(s,c) && buffers::safe(s,c) && bounds::safe(s,c) && active::safe(s,c) && completion::safe(s,c)
}
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    let s=initial(c);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(s,i) by {}
    assert forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(s,i,j,m) by { channel_pair(c,i,j); }
}
pub proof fn payload_loosen(m: Message,a: int,b: int)
    requires payload(m,a),a <= b
    ensures payload(m,b)
{
    if let Message::Snap(_,h)=m { logs::loosen(h,a,b); }
}
pub proof fn last_committed_nonnegative(s: LState,i: int)
    requires node(s,i),s.election.nodes[i].role == Role::Following,s.nodes[i].phase == Phase::Synchronization || s.nodes[i].phase == Phase::Broadcast
    ensures last_committed(s,i).index >= 0
{
    if s.nodes[i].phase == Phase::Synchronization && s.nodes[i].commits.len() > 0 { logs::index_bounds(complete_history(s,i),s.nodes[i].commits.last()); }
}
pub proof fn appended_prefix(h: Seq<Txn>,p: Seq<Txn>,e: int)
    requires p.len() > 0,sequence(h+p,e)
    ensures sequence(h.push(p[0]),e),sequence(h.push(p[0])+p.drop_first(),e)
{
    let all=h+p; logs::prefix(all,h.len() as int+1,e);
    assert(h.push(p[0]) =~= super::zookeeper::sub(all,1,h.len() as int+1));
    assert(h.push(p[0])+p.drop_first() =~= all);
}
pub proof fn election_node(s: LState,c: Constants,ea: fle::Action,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i)
    ensures node(apply(s,c,Action::Election(ea)),i)
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let u=apply(s,c,Action::Election(ea)); let x=receiver(Action::Election(ea)); channels::facts(s,c,i,x); assert(node(s,i));
    super::zk_election_types::history_frame(s.election,c,ea,i);
    logs::transfer(s.election.nodes[i].history,u.election.nodes[i].history,s.nodes[i].accepted);
}
pub proof fn sync_node(s: LState,c: Constants,x: int,y: int,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,Action::Sync(x,y)),c.servers.contains(i)
    ensures node(apply(s,c,Action::Sync(x,y)),i)
{
    reveal(enabled); reveal(apply); let u=apply(s,c,Action::Sync(x,y)); channels::facts(s,c,i,x); channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(node(s,i));
    leaders::sync_step(s,c,x,y,i); assert(s.election.nodes[i].history.len() == u.election.nodes[i].history.len());
    logs::transfer(s.election.nodes[i].history,u.election.nodes[i].history,s.nodes[i].accepted);
}
pub proof fn mode_node(s: LState,c: Constants,x: int,y: int,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,Action::SyncMessage(x,y)),c.servers.contains(i)
    ensures node(apply(s,c,Action::SyncMessage(x,y)),i)
{
    reveal(enabled); reveal(apply); channels::facts(s,c,i,x); channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(node(s,i)); assert(node(s,x));
    fifo::receive_clean(s,c,x,y); let m=s.msgs[(y,x)][0]; assert(s.msgs[(y,x)].contains(m)); assert(cell(s,y,x,m));
    if let Message::Trunc(zxid)=m { logs::index_bounds(s.election.nodes[x].history,zxid); if z::index(s.election.nodes[x].history,zxid) <= s.election.nodes[x].history.len() { logs::prefix(s.election.nodes[x].history,z::index(s.election.nodes[x].history,zxid),s.nodes[x].accepted); } }
}
pub proof fn proposal_node(s: LState,c: Constants,a: Action,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),a is ProposalSync || a is Proposal
    ensures node(apply(s,c,a),i)
{
    reveal(enabled); reveal(apply); let x=receiver(a); let y=if let Action::ProposalSync(_,y)=a { y } else { a->Proposal_1 };
    channels::facts(s,c,i,x); channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(node(s,i)); assert(node(s,x));
    let m=s.msgs[(y,x)][0]; assert(s.msgs[(y,x)].contains(m)); assert(cell(s,y,x,m));
    if let Message::Proposal(zxid,value)=m {
        if z::next_zxid(last_queued(s,x).zxid,zxid) {
            let t=Txn { zxid,value,ack: Set::empty(),epoch: s.nodes[x].accepted };
            if a is ProposalSync {
                logs::append(complete_history(s,x),t,s.nodes[x].accepted);
                assert(complete_history(apply(s,c,a),x) =~= complete_history(s,x).push(t));
            } else { logs::append(s.election.nodes[x].history,t,s.nodes[x].accepted); }
        }
    }
}
pub proof fn commit_sync_node(s: LState,c: Constants,x: int,y: int,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,Action::CommitSync(x,y)),c.servers.contains(i)
    ensures node(apply(s,c,Action::CommitSync(x,y)),i)
{
    reveal(enabled); reveal(apply); channels::facts(s,c,i,x); channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(node(s,i)); assert(node(s,x));
    if s.nodes[x].mode != Mode::Diff && !s.nodes[x].received_leader && last_committed(s,x).index+1 <= last_queued(s,x).index {
        buffers::flush_has_pending(s,c,x,y); appended_prefix(s.election.nodes[x].history,s.nodes[x].pending,s.nodes[x].accepted);
    }
}
pub proof fn finish_node(s: LState,c: Constants,a: Action,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),a is NewLeader || a is UpToDate
    ensures node(apply(s,c,a),i)
{
    reveal(enabled); reveal(apply); let x=receiver(a); let y=if let Action::NewLeader(_,y)=a { y } else { a->UpToDate_1 };
    channels::facts(s,c,i,x); channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(node(s,i)); assert(node(s,x)); ready::head(s,c,y,x);
    last_committed_nonnegative(s,x);
    if s.nodes[x].phase == Phase::Broadcast { assert(complete_history(s,x) =~= s.election.nodes[x].history); }
    assert(sequence(complete_history(s,x),s.nodes[x].accepted));
}
pub proof fn request_node(s: LState,c: Constants,x: int,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,Action::Request(x)),c.servers.contains(i),c.servers.len() > 1
    ensures node(apply(s,c,Action::Request(x)),i)
{
    reveal(enabled); reveal(apply); channels::facts(s,c,i,x); assert(node(s,i)); assert(node(s,x)); assert(epochs::node(s,c,x)); assert(active::node(s,c,x)); assert(completion::node(s,c,x));
    let u=apply(s,c,Action::Request(x)); let h=u.election.nodes[x].history; let t=h[h.len()-1]; logs::request(s.election.nodes[x].history,s.nodes[x].accepted,t);
}
pub proof fn ack_node(s: LState,c: Constants,x: int,y: int,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,Action::Ack(x,y)),c.servers.contains(i)
    ensures node(apply(s,c,Action::Ack(x,y)),i)
{
    reveal(enabled); reveal(apply); channels::facts(s,c,i,x); channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(node(s,i)); assert(node(s,x));
    let u=apply(s,c,Action::Ack(x,y)); let h=s.election.nodes[i].history; let q=u.election.nodes[i].history;
    assert(super::zab_log_math::same(h,q)) by { assert forall |k: int| 0 <= k < h.len() implies #[trigger] z::equal(h[k],q[k]) by {} }
    logs::transfer(h,q,s.nodes[i].accepted);
}
pub proof fn other_node(s: LState,c: Constants,a: Action,i: int)
    requires context(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        !(a is Election),!(a is Sync),!(a is SyncMessage),!(a is ProposalSync),!(a is Proposal),!(a is CommitSync),!(a is NewLeader),!(a is UpToDate),!(a is Request),!(a is Ack)
    ensures node(apply(s,c,a),i)
{
    reveal(enabled); reveal(apply); let x=receiver(a); let u=apply(s,c,a); assert(node(s,i)); epochs::preserve_node(s,c,a,i);
    logs::loosen(s.election.nodes[i].history,s.nodes[i].accepted,u.nodes[i].accepted);
    if s.election.nodes[i].role == Role::Following && s.nodes[i].phase == Phase::Synchronization { logs::loosen(complete_history(s,i),s.nodes[i].accepted,u.nodes[i].accepted); }
    if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,x)); }
    match a {
        Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,x,y); } },
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::AckLd(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,x,y);
            if a is LeaderInfo && s.nodes[x].phase == Phase::Discovery { origin::discovery_clean(s,c,x); }
        },_ => {},
    }
}
pub proof fn sync_send_payload(s: LState,x: int,y: int,peer: z::Zxid,k: int,mode: Mode,i: int,j: int,m: Message)
    requires sequence(s.election.nodes[x].history,s.nodes[x].accepted),0 <= k,mode != Mode::None,
        mode == Mode::Snap ==> k <= s.election.nodes[x].history.len(),m is Proposal || m is Snap,
        sync_send(s,x,y,peer,k,mode).msgs[(i,j)].contains(m),!s.msgs[(i,j)].contains(m)
    ensures payload(m,s.nodes[x].accepted),i == x,j == y
{
    let h=s.election.nodes[x].history; let u=sync_send(s,x,y,peer,k,mode); let end=h.len() as int;
    let committed=if s.nodes[x].phase == Phase::Broadcast { s.nodes[x].committed.index } else { end };
    let pos=choose |pos: int| 0 <= pos < u.msgs[(i,j)].len() && u.msgs[(i,j)][pos] == m;
    if pos < s.msgs[(i,j)].len() { assert(s.msgs[(i,j)].contains(m)); assert(false); }
    match m {
        Message::Proposal(zxid,value) => {
            assert(packets(h,k+1,end,committed).contains(m)); let at=super::zookeeper_proposal_records::packet_origin(h,k+1,end,committed,zxid,value);
            assert(0 <= h[at-1].zxid.epoch <= s.nodes[x].accepted && h[at-1].zxid.counter > 0);
        },
        Message::Snap(_,_) => {
            super::zookeeper_log_records::no_snap(h,k+1,end,committed,m); assert(mode == Mode::Snap); logs::prefix(h,k,s.nodes[x].accepted);
        },_ => {},
    }
}
pub proof fn sync_payload(s: LState,c: Constants,x: int,y: int,i: int,j: int,m: Message)
    requires context(s,c),safe(s,c),enabled(s,c,Action::Sync(x,y)),m is Proposal || m is Snap,
        apply(s,c,Action::Sync(x,y)).msgs[(i,j)].contains(m),!s.msgs[(i,j)].contains(m)
    ensures payload(m,apply(s,c,Action::Sync(x,y)).nodes[i].accepted),i == x,j == y
{
    reveal(enabled); reveal(apply); assert(node(s,x)); assert(bounds::node(s,x));
    let r=choose |r: Electing| s.nodes[x].electing.contains(r) && r.sid == y && r.zxid != unset() && s.nodes[x].learners.contains(y);
    let n=s.nodes[x]; let e=s.election.nodes[x]; let min=n.snapshot.index+1;
    let max=if n.phase == Phase::Broadcast { n.committed.index } else { e.history.len() as int };
    let lo=if min > max { e.processed.zxid } else { e.history[min-1].zxid };
    let hi=if min > max { e.processed.zxid } else if max == 0 { z::zero() } else { e.history[max-1].zxid };
    if r.zxid == e.processed.zxid { sync_send_payload(s,x,y,r.zxid,e.processed.index,Mode::Diff,i,j,m); }
    else if z::newer(r.zxid,hi) { sync_send_payload(s,x,y,hi,max,Mode::Trunc,i,j,m); }
    else if !z::newer(lo,r.zxid) {
        let k=z::index(e.history,r.zxid);
        if min <= k <= e.history.len() { sync_send_payload(s,x,y,r.zxid,k,Mode::Diff,i,j,m); }
        else { logs::floor_bounds(e.history,r.zxid); let k=floor_index(e.history,r.zxid); sync_send_payload(s,x,y,if k == 0 { z::zero() } else { e.history[k-1].zxid },k,Mode::Trunc,i,j,m); }
    } else { sync_send_payload(s,x,y,e.processed.zxid,max,Mode::Snap,i,j,m); }
}
pub proof fn other_payload(s: LState,c: Constants,a: Action,i: int,j: int,m: Message)
    requires context(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),!(a is Sync),m is Proposal || m is Snap,
        apply(s,c,a).msgs[(i,j)].contains(m),!s.msgs[(i,j)].contains(m)
    ensures payload(m,apply(s,c,a).nodes[i].accepted)
{
    reveal(enabled); reveal(apply); let x=receiver(a); channel_pair(c,i,j); channels::facts(s,c,i,j); assert(epochs::node(s,c,i));
    if a != Action::Stutter { channels::facts(s,c,i,x); channels::facts(s,c,j,x); }
    match a {
        Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y); } },
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y);
        },_ => {},
    }
    let u=apply(s,c,a); let k=choose |k: int| 0 <= k < u.msgs[(i,j)].len() && u.msgs[(i,j)][k] == m;
    assert forall |p: int| 0 <= p < s.msgs[(i,j)].len() implies s.msgs[(i,j)][p] != m by {}
    assert(a == Action::Request(i)); assert(node(s,i));
    if s.election.nodes[i].history.len() > 0 { assert(s.election.nodes[i].history.last().zxid.counter > 0); }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires context(s,c),safe(s,c),enabled(s,c,a),ready::safe(apply(s,c,a),c),c.servers.len() > 1 || small::safe(s,c)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u,i) by {
        match a {
            Action::Election(ea) => { election_node(s,c,ea,i); },Action::Sync(x,y) => { sync_node(s,c,x,y,i); },Action::SyncMessage(x,y) => { mode_node(s,c,x,y,i); },
            Action::ProposalSync(_,_) | Action::Proposal(_,_) => { proposal_node(s,c,a,i); },Action::CommitSync(x,y) => { commit_sync_node(s,c,x,y,i); },
            Action::NewLeader(_,_) | Action::UpToDate(_,_) => { finish_node(s,c,a,i); },Action::Request(x) => { if c.servers.len() > 1 { request_node(s,c,x,i); } else { small::no_request(s,c,x); } },Action::Ack(x,y) => { ack_node(s,c,x,y,i); },
            _ => { other_node(s,c,a,i); },
        }
    }
    assert forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(u,i,j,m) by {
        if u.msgs[(i,j)].contains(m) && (m is Proposal || m is Snap) {
            if s.msgs[(i,j)].contains(m) { assert(cell(s,i,j,m)); epochs::preserve_node(s,c,a,j); payload_loosen(m,s.nodes[j].accepted,u.nodes[j].accepted); }
            else {
                if let Action::Sync(x,y)=a { sync_payload(s,c,x,y,i,j,m); } else { other_payload(s,c,a,i,j,m); }
                assert(ready::cell(u,c,i,j,m));
            }
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
        at(b,c,tick-1); channels::at(b,c,tick-1); epochs::at(b,c,tick-1); ready::at(b,c,tick-1); forwarding::at(b,c,tick-1); origin::at(b,c,tick-1);
        fifo::at(b,c,tick-1); pending::at(b,c,tick-1); buffers::at(b,c,tick-1); bounds::at(b,c,tick-1); active::at(b,c,tick-1); completion::at(b,c,tick-1); ready::at(b,c,tick);
        if c.servers.len() <= 1 { small::at(b,c,tick-1); }
        let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a);
    }
}
} // verus!
