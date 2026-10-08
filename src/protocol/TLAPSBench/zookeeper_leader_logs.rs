//! During continuous leadership, transaction contents only grow by appending new requests.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role,Txn};
use super::zk_election as fle;
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::zookeeper_leader_frame as leader;
use super::zab_log_math as logs;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn prefix(h: Seq<Txn>,k: Seq<Txn>) -> bool {
    h.len() <= k.len() && forall |p: int| 0 <= p < h.len() ==> #[trigger] z::equal(h[p],k[p])
}
pub proof fn trans(h: Seq<Txn>,k: Seq<Txn>,l: Seq<Txn>)
    requires prefix(h,k),prefix(k,l)
    ensures prefix(h,l)
{
    assert forall |p: int| 0 <= p < h.len() implies #[trigger] z::equal(h[p],l[p]) by { assert(z::equal(h[p],k[p])); assert(z::equal(k[p],l[p])); }
}
pub proof fn sync_history(s: LState,i: int,j: int,peer: z::Zxid)
    requires i != j
    ensures logs::same(s.election.nodes[i].history,sync_follower(s,i,j,peer).election.nodes[i].history)
{
    let u=sync_follower(s,i,j,peer); let h=s.election.nodes[i].history; let k=u.election.nodes[i].history;
    assert forall |p: int| 0 <= p < h.len() implies #[trigger] z::equal(h[p],k[p]) by {}
}
pub proof fn election_step(s: LState,c: Constants,ea: fle::Action,i: int)
    requires channels::safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i)
    ensures prefix(s.election.nodes[i].history,apply(s,c,Action::Election(ea)).election.nodes[i].history)
{
    reveal(enabled); reveal(apply); super::zk_election_types::history_frame(s.election,c,ea,i);
}
pub proof fn sync_step(s: LState,c: Constants,x: int,y: int,i: int)
    requires channels::safe(s,c),enabled(s,c,Action::Sync(x,y)),c.servers.contains(i)
    ensures prefix(s.election.nodes[i].history,apply(s,c,Action::Sync(x,y)).election.nodes[i].history)
{
    reveal(enabled); reveal(apply); channels::facts(s,c,i,x); channels::facts(s,c,x,y);
    let r=choose |r: Electing| #![trigger s.nodes[x].electing.contains(r)] s.nodes[x].electing.contains(r) && r.sid == y && r.zxid != unset() && s.nodes[x].learners.contains(y);
    if x == y { assert(r.zxid == unset()); assert(false); }
    sync_history(s,x,y,r.zxid);
}
pub proof fn protocol_step(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),enabled(s,c,a),c.servers.contains(i),s.election.nodes[i].role == Role::Leading,
        apply(s,c,a).election.nodes[i].role == Role::Leading,!(a is Election),!(a is Sync)
    ensures prefix(s.election.nodes[i].history,apply(s,c,a).election.nodes[i].history)
{
    reveal(enabled); reveal(apply); let x=receiver(a); if a != Action::Stutter { channels::facts(s,c,i,x); }
    match a {
        Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,x,y); } },
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,x,y);
        },_ => {},
    }
    let h=s.election.nodes[i].history; let k=apply(s,c,a).election.nodes[i].history;
    assert forall |p: int| 0 <= p < h.len() implies #[trigger] z::equal(h[p],k[p]) by {}
}
pub proof fn step(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),enabled(s,c,a),c.servers.contains(i),s.election.nodes[i].role == Role::Leading,
        apply(s,c,a).election.nodes[i].role == Role::Leading
    ensures prefix(s.election.nodes[i].history,apply(s,c,a).election.nodes[i].history)
{
    match a { Action::Election(ea) => { election_step(s,c,ea,i); },Action::Sync(x,y) => { sync_step(s,c,x,y,i); },_ => { protocol_step(s,c,a,i); } }
}
pub proof fn between(b: Behavior<LState>,c: Constants,i: int,left: int,right: int)
    requires support::safety_spec(b,c),c.servers.contains(i),leader::interval(b,i,left,right)
    ensures prefix(b[left].election.nodes[i].history,b[right].election.nodes[i].history)
    decreases right-left
{
    if left < right {
        between(b,c,i,left,right-1); channels::at(b,c,right-1); let a=support::step(b,c,right-1); step(b[right-1],c,a,i);
        trans(b[left].election.nodes[i].history,b[right-1].election.nodes[i].history,b[right].election.nodes[i].history);
    }
}
} // verus!
