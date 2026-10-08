//! Protocol messages retain their connected endpoints and identify their discovery send steps.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role,Phase,Txn};
use super::zk_election as fle;
use super::zookeeper_channels as channels;
use super::zab_connections::channel_pair;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn roles(s: LState,u: LState,i: int,j: int) -> bool {
    s.msgs[(i,j)].len() > 0 && u.msgs[(i,j)].len() > 0 ==>
        s.election.nodes[i].role == u.election.nodes[i].role && s.election.nodes[j].role == u.election.nodes[j].role
}
pub proof fn election_roles(s: LState,c: Constants,ea: fle::Action,i: int,j: int)
    requires channels::safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i),c.servers.contains(j)
    ensures roles(s,apply(s,c,Action::Election(ea)),i,j)
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(Action::Election(ea));
    channels::facts(s,c,i,j); channels::facts(s,c,i,x); channels::facts(s,c,j,x);
}
pub proof fn environment_roles(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),a is Crash || a is Partition || a is Recover || a is Start || a is Stutter
    ensures roles(s,apply(s,c,a),i,j)
{
    reveal(enabled); reveal(apply); let x=receiver(a); channel_pair(c,i,j); channels::facts(s,c,i,j);
    if a != Action::Stutter { channels::facts(s,c,i,x); channels::facts(s,c,j,x); }
    if a is Crash { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y); } }
    if let Action::Partition(_,y)=a { channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y); }
}
pub proof fn protocol_roles(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),!(a is Election),!(a is Crash),!(a is Partition),!(a is Recover),!(a is Start)
    ensures roles(s,apply(s,c,a),i,j)
{
    reveal(enabled); reveal(apply); let x=receiver(a); channel_pair(c,i,j); channels::facts(s,c,i,j);
    if a != Action::Stutter { channels::facts(s,c,i,x); channels::facts(s,c,j,x); }
    match a {
        Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::Sync(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y);
        },_ => {},
    }
}
pub proof fn step_roles(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j)
    ensures roles(s,apply(s,c,a),i,j)
{
    match a {
        Action::Election(ea) => { election_roles(s,c,ea,i,j); },
        Action::Crash(_) | Action::Partition(_,_) | Action::Recover(_,_) | Action::Start(_) => { environment_roles(s,c,a,i,j); },
        _ => { protocol_roles(s,c,a,i,j); },
    }
}
pub open spec fn epoch_message(m: Message) -> bool { m is LeaderInfo || m is AckEpoch }
pub proof fn sync_packets(h: Seq<Txn>,cur: int,end: int,committed: int)
    ensures forall |m: Message| #[trigger] packets(h,cur,end,committed).contains(m) ==> m is Proposal || m is Commit
    decreases if end >= cur { end-cur+1 } else { 0 }
{
    reveal(packets);
    if cur <= end {
        sync_packets(h,cur,end-1,committed);
        assert forall |m: Message| #[trigger] packets(h,cur,end,committed).contains(m) implies m is Proposal || m is Commit by {
            let k=choose |k: int| 0 <= k < packets(h,cur,end,committed).len() && packets(h,cur,end,committed)[k] == m;
            if k < packets(h,cur,end-1,committed).len() { assert(packets(h,cur,end-1,committed).contains(m)); }
        }
    }
}
pub open spec fn fresh_epoch(s: LState,c: Constants,a: Action,i: int,j: int,m: Message) -> bool {
    match (a,m) {
        (Action::FollowerInfo(x,_),Message::LeaderInfo(zxid)) => i == x && apply(s,c,a).election.nodes[i].role == Role::Leading
            && formed(c,i,z::al_ids(apply(s,c,a).nodes[i].connecting)) && zxid.epoch == apply(s,c,a).nodes[i].accepted,
        (Action::LeaderInfo(x,y),Message::AckEpoch(zxid,report)) => i == x && j == y && s.msgs[(j,i)][0] is LeaderInfo
            && s.nodes[i].phase == Phase::Discovery && s.msgs[(j,i)][0]->LeaderInfo_0.epoch >= s.nodes[i].accepted
            && apply(s,c,a).nodes[i].accepted == s.msgs[(j,i)][0]->LeaderInfo_0.epoch
            && report == if apply(s,c,a).nodes[i].accepted > s.nodes[i].accepted { s.election.nodes[i].current } else { -1 },
        _ => false,
    }
}
pub proof fn sync_send_origin(s: LState,x: int,y: int,zxid: z::Zxid,k: int,mode: Mode,i: int,j: int,m: Message)
    requires epoch_message(m),sync_send(s,x,y,zxid,k,mode).msgs[(i,j)].contains(m)
    ensures s.msgs[(i,j)].contains(m)
{
    let n=s.nodes[x]; let e=s.election.nodes[x]; let end=e.history.len() as int;
    let committed=if n.phase == Phase::Broadcast { n.committed.index } else { end };
    sync_packets(e.history,k+1,end,committed);
    let u=sync_send(s,x,y,zxid,k,mode);
    let p=choose |p: int| 0 <= p < u.msgs[(i,j)].len() && u.msgs[(i,j)][p] == m;
    if p < s.msgs[(i,j)].len() { assert(s.msgs[(i,j)].contains(m)); }
    else { assert(packets(e.history,k+1,end,committed).contains(m)); assert(false); }
}
pub proof fn sync_origin(s: LState,c: Constants,x: int,y: int,i: int,j: int,m: Message)
    requires channels::safe(s,c),enabled(s,c,Action::Sync(x,y)),c.servers.contains(i),c.servers.contains(j),epoch_message(m),
        apply(s,c,Action::Sync(x,y)).msgs[(i,j)].contains(m)
    ensures s.msgs[(i,j)].contains(m)
{
    reveal(enabled); reveal(apply);
    let r=choose |r: Electing| #![trigger s.nodes[x].electing.contains(r)] s.nodes[x].electing.contains(r) && r.sid == y && r.zxid != unset() && s.nodes[x].learners.contains(y);
    let n=s.nodes[x]; let e=s.election.nodes[x]; let min=n.snapshot.index+1;
    let max=if n.phase == Phase::Broadcast { n.committed.index } else { e.history.len() as int };
    let lo=if min > max { e.processed.zxid } else { e.history[min-1].zxid };
    let hi=if min > max { e.processed.zxid } else if max == 0 { z::zero() } else { e.history[max-1].zxid };
    if r.zxid == e.processed.zxid { sync_send_origin(s,x,y,r.zxid,e.processed.index,Mode::Diff,i,j,m); }
    else if z::newer(r.zxid,hi) { sync_send_origin(s,x,y,hi,max,Mode::Trunc,i,j,m); }
    else if !z::newer(lo,r.zxid) {
        let k=z::index(e.history,r.zxid);
        if min <= k <= e.history.len() { sync_send_origin(s,x,y,r.zxid,k,Mode::Diff,i,j,m); }
        else { let k=floor_index(e.history,r.zxid); sync_send_origin(s,x,y,if k == 0 { z::zero() } else { e.history[k-1].zxid },k,Mode::Trunc,i,j,m); }
    } else { sync_send_origin(s,x,y,e.processed.zxid,max,Mode::Snap,i,j,m); }
}
pub proof fn epoch_origin(s: LState,c: Constants,a: Action,i: int,j: int,m: Message)
    requires channels::safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),epoch_message(m),apply(s,c,a).msgs[(i,j)].contains(m)
    ensures s.msgs[(i,j)].contains(m) || fresh_epoch(s,c,a,i,j,m)
{
    if let Action::Sync(x,y)=a { sync_origin(s,c,x,y,i,j,m); }
    else {
        reveal(enabled); reveal(apply); let x=receiver(a); channel_pair(c,i,j); channels::facts(s,c,i,j);
        if a != Action::Stutter { channels::facts(s,c,i,x); channels::facts(s,c,j,x); }
        match a {
            Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y); } },
            Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::Sync(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
                channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y);
            },_ => {},
        }
        let u=apply(s,c,a); let k=choose |k: int| 0 <= k < u.msgs[(i,j)].len() && u.msgs[(i,j)][k] == m;
        if !s.msgs[(i,j)].contains(m) {
            assert forall |p: int| 0 <= p < s.msgs[(i,j)].len() implies s.msgs[(i,j)][p] != m by {}
            assert(fresh_epoch(s,c,a,i,j,m));
        }
    }
}
} // verus!
