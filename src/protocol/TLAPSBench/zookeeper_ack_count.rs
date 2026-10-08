//! Counting epoch acknowledgments in FIFO channels, including synchronization batches.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Phase};
use super::zookeeper_message_frames as frames;
use super::zookeeper_channels as channels;
use super::zab_connections::channel_pair;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn is_ack(m: Message) -> bool { m is AckEpoch }
pub open spec fn predicate() -> spec_fn(Message) -> bool { |m: Message| is_ack(m) }
pub open spec fn count(q: Seq<Message>) -> nat { q.filter(predicate()).len() }
pub open spec fn bit(b: bool) -> nat { if b { 1 } else { 0 } }
pub proof fn empty()
    ensures count(Seq::empty()) == 0
{
    reveal(Seq::filter);
}
pub proof fn concat(q: Seq<Message>,r: Seq<Message>)
    ensures count(q+r) == count(q)+count(r)
{
    Seq::filter_distributes_over_add(q,r,predicate());
}
pub proof fn single(m: Message)
    ensures count(seq![m]) == bit(is_ack(m))
{
    empty(); Seq::empty().lemma_filter_len_push(predicate(),m); assert(seq![m] =~= Seq::empty().push(m));
}
pub proof fn facts(q: Seq<Message>)
    ensures q.len() == 0 ==> count(q) == 0,
        q.len() > 0 ==> count(q) == count(q.drop_first())+bit(is_ack(q[0])),
        forall |m: Message| #[trigger] count(q.push(m)) == count(q)+bit(is_ack(m))
{
    if q.len() == 0 { assert(q =~= Seq::empty()); empty(); }
    else { q.drop_first().lemma_filter_prepend(q[0],predicate()); single(q[0]); assert(q =~= seq![q[0]]+q.drop_first()); }
    assert forall |m: Message| #[trigger] count(q.push(m)) == count(q)+bit(is_ack(m)) by { q.lemma_filter_len_push(predicate(),m); }
}
pub proof fn absent(q: Seq<Message>)
    requires forall |m: Message| #![trigger is_ack(m)] q.contains(m) ==> !is_ack(m)
    ensures count(q) == 0
{
    assert(q.all(|m: Message| !is_ack(m))) by {
        assert forall |k: int| #![trigger q[k]] 0 <= k < q.len() implies !is_ack(q[k]) by { assert(q.contains(q[k])); }
    }
    q.lemma_all_neg_filter_empty(predicate());
}
pub proof fn ack_batch(h: Seq<z::Txn>)
    ensures count(ack_messages(h)) == 0
{
    let q=ack_messages(h);
    assert forall |m: Message| #![trigger is_ack(m)] q.contains(m) implies !is_ack(m) by { let k=choose |k: int| 0 <= k < q.len() && q[k] == m; }
    absent(q);
}
pub proof fn sync_send_count(s: LState,x: int,y: int,zxid: z::Zxid,k: int,mode: Mode,i: int,j: int)
    ensures count(sync_send(s,x,y,zxid,k,mode).msgs[(i,j)]) == count(s.msgs[(i,j)])
{
    let n=s.nodes[x]; let e=s.election.nodes[x]; let end=e.history.len() as int;
    let committed=if n.phase == Phase::Broadcast { n.committed.index } else { end };
    let first=match mode { Mode::Diff => Message::Diff(zxid),Mode::Trunc => Message::Trunc(zxid),_ => Message::Snap(zxid,super::zookeeper::sub(e.history,1,k)) };
    let ps=packets(e.history,k+1,end,committed); frames::sync_packets(e.history,k+1,end,committed); absent(ps);
    let last=Message::NewLeader(z::Zxid { epoch: n.accepted,counter: 0 }); single(first); single(last); concat(seq![first],ps); concat(seq![first]+ps,seq![last]);
    concat(s.msgs[(x,y)],seq![first]+ps+seq![last]);
}
pub proof fn sync_count(s: LState,c: Constants,x: int,y: int,i: int,j: int)
    ensures count(apply(s,c,Action::Sync(x,y)).msgs[(i,j)]) == count(s.msgs[(i,j)])
{
    reveal(apply);
    let r=choose |r: Electing| #![trigger s.nodes[x].electing.contains(r)] s.nodes[x].electing.contains(r) && r.sid == y && r.zxid != unset() && s.nodes[x].learners.contains(y);
    let n=s.nodes[x]; let e=s.election.nodes[x]; let min=n.snapshot.index+1;
    let max=if n.phase == Phase::Broadcast { n.committed.index } else { e.history.len() as int };
    let lo=if min > max { e.processed.zxid } else { e.history[min-1].zxid };
    let hi=if min > max { e.processed.zxid } else if max == 0 { z::zero() } else { e.history[max-1].zxid };
    if r.zxid == e.processed.zxid { sync_send_count(s,x,y,r.zxid,e.processed.index,Mode::Diff,i,j); }
    else if z::newer(r.zxid,hi) { sync_send_count(s,x,y,hi,max,Mode::Trunc,i,j); }
    else if !z::newer(lo,r.zxid) {
        let k=z::index(e.history,r.zxid);
        if min <= k <= e.history.len() { sync_send_count(s,x,y,r.zxid,k,Mode::Diff,i,j); }
        else { let k=floor_index(e.history,r.zxid); sync_send_count(s,x,y,if k == 0 { z::zero() } else { e.history[k-1].zxid },k,Mode::Trunc,i,j); }
    } else { sync_send_count(s,x,y,e.processed.zxid,max,Mode::Snap,i,j); }
}
pub proof fn other_count(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),!(a is LeaderInfo),!(a is Sync)
    ensures count(apply(s,c,a).msgs[(i,j)]) <= count(s.msgs[(i,j)])
{
    reveal(enabled); reveal(apply); let x=receiver(a); channel_pair(c,i,j); channels::facts(s,c,i,j); facts(s.msgs[(i,j)]); empty();
    if a != Action::Stutter { channels::facts(s,c,i,x); channels::facts(s,c,j,x); }
    match a {
        Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y); } },
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::AckEpoch(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y); facts(s.msgs[(x,y)]); facts(s.msgs[(y,x)]);
            match a {
                Action::Connect(_,_) => { let m=Message::FollowerInfo(z::Zxid { epoch: s.nodes[y].accepted,counter: 0 }); single(m); concat(s.msgs[(y,x)],seq![m]); },
                Action::FollowerInfo(_,_) => { let m=Message::LeaderInfo(z::Zxid { epoch: s.nodes[x].accepted,counter: 0 }); single(m); concat(s.msgs[(x,y)],seq![m]); },
                Action::NewLeader(_,_) => { if let Message::NewLeader(zxid)=s.msgs[(y,x)][0] {
                    let q=ack_messages(s.nodes[x].pending); ack_batch(s.nodes[x].pending); single(Message::AckLd(zxid)); concat(seq![Message::AckLd(zxid)],q); concat(s.msgs[(x,y)],seq![Message::AckLd(zxid)]+q);
                } },
                Action::AckLd(_,_) => { let m=Message::UpToDate(z::Zxid { epoch: s.nodes[x].accepted,counter: 0 }); single(m); concat(s.msgs[(x,y)],seq![m]); },
                Action::UpToDate(_,_) => { ack_batch(s.nodes[x].pending); concat(s.msgs[(x,y)],ack_messages(s.nodes[x].pending)); },
                Action::Proposal(_,_) => { if let Message::Proposal(zxid,_)=s.msgs[(y,x)][0] { single(Message::Ack(zxid)); concat(s.msgs[(x,y)],seq![Message::Ack(zxid)]); } },
                _ => {},
            }
        },_ => {},
    }
}
} // verus!
