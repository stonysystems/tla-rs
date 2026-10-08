//! Every transmitted proposal has an entry in the benchmark's passive proposal history.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Phase,Txn,Proposal,Zxid};
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::zab_connections::channel_pair;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn recorded(s: LState,zxid: Zxid,value: int) -> bool {
    exists |p: Proposal| #![trigger s.proposals.contains(p)] s.proposals.contains(p) && p.zxid == zxid && p.value == value
}
pub open spec fn packet(s: LState,m: Message) -> bool { match m { Message::Proposal(zxid,value) => recorded(s,zxid,value),_ => true } }
pub open spec fn cell(s: LState,i: int,j: int,m: Message) -> bool { s.msgs[(i,j)].contains(m) ==> packet(s,m) }
pub open spec fn safe(s: LState,c: Constants) -> bool {
    forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) ==> #[trigger] cell(s,i,j,m)
}
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    let s=initial(c);
    assert forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(s,i,j,m) by { channel_pair(c,i,j); }
}
pub proof fn bootstrap(c: Constants,i: int)
    requires c.servers.contains(i)
    ensures recorded(initial(c),z::boot(),0)
{
    let p=Proposal { source: i,epoch: 0,zxid: z::boot(),value: 0 }; assert(initial(c).proposals.contains(p));
}
#[verifier::spinoff_prover]
pub proof fn monotonic(s: LState,c: Constants,a: Action)
    ensures s.proposals.subset_of(apply(s,c,a).proposals)
{
    reveal(apply);
}
pub proof fn retained(s: LState,u: LState,zxid: Zxid,value: int)
    requires s.proposals.subset_of(u.proposals),recorded(s,zxid,value)
    ensures recorded(u,zxid,value)
{
    let p=choose |p: Proposal| #![trigger s.proposals.contains(p)] s.proposals.contains(p) && p.zxid == zxid && p.value == value; assert(u.proposals.contains(p));
}
pub proof fn packet_origin(h: Seq<Txn>,first: int,end: int,committed: int,zxid: Zxid,value: int) -> (k: int)
    requires packets(h,first,end,committed).contains(Message::Proposal(zxid,value))
    ensures first <= k <= end,h[k-1].zxid == zxid,h[k-1].value == value
    decreases if end >= first { end-first+1 } else { 0 }
{
    reveal(packets); let q=packets(h,first,end,committed); let m=Message::Proposal(zxid,value);
    let p=choose |p: int| 0 <= p < q.len() && q[p] == m;
    if p < packets(h,first,end-1,committed).len() {
        assert(packets(h,first,end-1,committed).contains(m)); packet_origin(h,first,end-1,committed,zxid,value)
    } else { end }
}
pub proof fn sync_send_record(s: LState,x: int,y: int,peer: Zxid,k: int,mode: Mode,i: int,j: int,zxid: Zxid,value: int)
    requires sync_send(s,x,y,peer,k,mode).msgs[(i,j)].contains(Message::Proposal(zxid,value)),!s.msgs[(i,j)].contains(Message::Proposal(zxid,value))
    ensures recorded(sync_send(s,x,y,peer,k,mode),zxid,value)
{
    let n=s.nodes[x]; let e=s.election.nodes[x]; let end=e.history.len() as int;
    let committed=if n.phase == Phase::Broadcast { n.committed.index } else { end };
    let u=sync_send(s,x,y,peer,k,mode); let m=Message::Proposal(zxid,value);
    let pos=choose |pos: int| 0 <= pos < u.msgs[(i,j)].len() && u.msgs[(i,j)][pos] == m;
    if pos < s.msgs[(i,j)].len() { assert(s.msgs[(i,j)].contains(m)); assert(false); }
    assert(packets(e.history,k+1,end,committed).contains(m));
    let at=packet_origin(e.history,k+1,end,committed,zxid,value);
    let p=Proposal { source: x,epoch: n.accepted,zxid,value }; let range=Set::range(k+1,end+1);
    assert(range.contains(at)); range.lemma_map_contains(|at: int| Proposal { source: x,epoch: n.accepted,zxid: e.history[at-1].zxid,value: e.history[at-1].value },p);
    assert(u.proposals.contains(p));
}
pub proof fn sync_record(s: LState,c: Constants,x: int,y: int,i: int,j: int,zxid: Zxid,value: int)
    requires apply(s,c,Action::Sync(x,y)).msgs[(i,j)].contains(Message::Proposal(zxid,value)),!s.msgs[(i,j)].contains(Message::Proposal(zxid,value))
    ensures recorded(apply(s,c,Action::Sync(x,y)),zxid,value)
{
    reveal(apply);
    let r=choose |r: Electing| #![trigger s.nodes[x].electing.contains(r)] s.nodes[x].electing.contains(r) && r.sid == y && r.zxid != unset() && s.nodes[x].learners.contains(y);
    let n=s.nodes[x]; let e=s.election.nodes[x]; let min=n.snapshot.index+1;
    let max=if n.phase == Phase::Broadcast { n.committed.index } else { e.history.len() as int };
    let lo=if min > max { e.processed.zxid } else { e.history[min-1].zxid };
    let hi=if min > max { e.processed.zxid } else if max == 0 { z::zero() } else { e.history[max-1].zxid };
    if r.zxid == e.processed.zxid { sync_send_record(s,x,y,r.zxid,e.processed.index,Mode::Diff,i,j,zxid,value); }
    else if z::newer(r.zxid,hi) { sync_send_record(s,x,y,hi,max,Mode::Trunc,i,j,zxid,value); }
    else if !z::newer(lo,r.zxid) {
        let k=z::index(e.history,r.zxid);
        if min <= k <= e.history.len() { sync_send_record(s,x,y,r.zxid,k,Mode::Diff,i,j,zxid,value); }
        else { let k=floor_index(e.history,r.zxid); sync_send_record(s,x,y,if k == 0 { z::zero() } else { e.history[k-1].zxid },k,Mode::Trunc,i,j,zxid,value); }
    } else { sync_send_record(s,x,y,e.processed.zxid,max,Mode::Snap,i,j,zxid,value); }
    let mid=sync_follower(s,x,y,r.zxid); assert(recorded(mid,zxid,value)); retained(mid,apply(s,c,Action::Sync(x,y)),zxid,value);
}
pub proof fn fresh_protocol(s: LState,c: Constants,a: Action,i: int,j: int,zxid: Zxid,value: int)
    requires channels::safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),!(a is Sync),
        apply(s,c,a).msgs[(i,j)].contains(Message::Proposal(zxid,value)),!s.msgs[(i,j)].contains(Message::Proposal(zxid,value))
    ensures recorded(apply(s,c,a),zxid,value)
{
    reveal(enabled); reveal(apply); let x=receiver(a); channel_pair(c,i,j); channels::facts(s,c,i,j);
    if a != Action::Stutter { channels::facts(s,c,i,x); channels::facts(s,c,j,x); }
    match a {
        Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y); } },
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y);
        },_ => {},
    }
    let u=apply(s,c,a); let m=Message::Proposal(zxid,value); let k=choose |k: int| 0 <= k < u.msgs[(i,j)].len() && u.msgs[(i,j)][k] == m;
    assert forall |p: int| 0 <= p < s.msgs[(i,j)].len() implies s.msgs[(i,j)][p] != m by {}
    assert(a == Action::Request(i)); let p=Proposal { source: i,epoch: s.nodes[i].accepted,zxid,value }; assert(u.proposals.contains(p));
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires channels::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a); monotonic(s,c,a);
    assert forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(u,i,j,m) by {
        if u.msgs[(i,j)].contains(m) {
            if let Message::Proposal(zxid,value)=m {
                if s.msgs[(i,j)].contains(m) { assert(cell(s,i,j,m)); retained(s,u,zxid,value); }
                else if let Action::Sync(x,y)=a { sync_record(s,c,x,y,i,j,zxid,value); }
                else { fresh_protocol(s,c,a,i,j,zxid,value); }
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
    else { at(b,c,tick-1); channels::at(b,c,tick-1); let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a); }
}
} // verus!
