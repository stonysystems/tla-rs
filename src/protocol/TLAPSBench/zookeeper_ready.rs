//! Synchronization traffic and its authorizing receipts belong to followers that accepted the leader's epoch.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role,Phase};
use super::zk_election as fle;
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::zookeeper_receipts as receipts;
use super::zookeeper_receipt_links as links;
use super::zookeeper_epoch_messages as epochs;
use super::zookeeper_message_frames as frames;
use super::zookeeper_leader_frame as leader;
use super::zookeeper_session_frames as session;
use super::zab_connections::channel_pair;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn ready(s: LState,c: Constants,i: int,j: int) -> bool {
    i != j && s.election.nodes[i].role == Role::Leading && s.election.nodes[j].role == Role::Following
    && s.nodes[j].leader == Some(i) && s.nodes[i].learners.contains(j) && session::syncing(s.nodes[j])
    && formed(c,i,z::al_ids(s.nodes[i].connecting)) && s.nodes[j].accepted == s.nodes[i].accepted
}
pub open spec fn node(s: LState,c: Constants,i: int) -> bool {
    s.election.nodes[i].role == Role::Following && session::syncing(s.nodes[i]) ==>
        s.nodes[i].leader is Some && ready(s,c,s.nodes[i].leader.unwrap(),i)
}
pub open spec fn pair(s: LState,c: Constants,i: int,j: int) -> bool {
    s.election.nodes[i].role == Role::Leading && i != j && (s.nodes[i].forwarding.contains(j)
        || links::electing(s.nodes[i].electing,j) || links::ackld(s.nodes[i].ackld,j)) ==> ready(s,c,i,j)
}
pub open spec fn forward(m: Message) -> bool { m is Diff || m is Trunc || m is Snap || m is Proposal || m is Commit || m is NewLeader || m is UpToDate }
pub open spec fn packet(s: LState,c: Constants,i: int,j: int,m: Message) -> bool {
    if forward(m) { ready(s,c,i,j) } else if m is AckEpoch || m is AckLd || m is Ack { ready(s,c,j,i) } else { true }
}
pub open spec fn cell(s: LState,c: Constants,i: int,j: int,m: Message) -> bool { s.msgs[(i,j)].contains(m) ==> packet(s,c,i,j,m) }
pub open spec fn safe(s: LState,c: Constants) -> bool {
    (forall |i: int| c.servers.contains(i) ==> #[trigger] node(s,c,i))
    && (forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) ==> #[trigger] pair(s,c,i,j))
    && forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) ==> #[trigger] cell(s,c,i,j,m)
}
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    let s=initial(c);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(s,c,i) by {}
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] pair(s,c,i,j) by {}
    assert forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(s,c,i,j,m) by { channel_pair(c,i,j); }
}
pub proof fn head(s: LState,c: Constants,i: int,j: int)
    requires safe(s,c),c.servers.contains(i),c.servers.contains(j),s.msgs[(i,j)].len() > 0
    ensures packet(s,c,i,j,s.msgs[(i,j)][0])
{
    assert(s.msgs[(i,j)].contains(s.msgs[(i,j)][0])); assert(cell(s,c,i,j,s.msgs[(i,j)][0]));
}
pub proof fn retained(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),ready(s,c,i,j),
        apply(s,c,a).election.nodes[i].role == Role::Leading,apply(s,c,a).election.nodes[j].role == Role::Following
    ensures ready(apply(s,c,a),c,i,j)
{
    let u=apply(s,c,a); session::follower_step(s,c,a,j); leader::step(s,c,a,i); channels::facts(u,c,i,j);
}
pub proof fn leader_info(s: LState,c: Constants,x: int,y: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,Action::LeaderInfo(x,y)),c),receipts::safe(s,c),epochs::safe(s,c),enabled(s,c,Action::LeaderInfo(x,y)),
        s.msgs[(y,x)][0] is LeaderInfo,s.nodes[x].phase == Phase::Discovery,s.msgs[(y,x)][0]->LeaderInfo_0.epoch >= s.nodes[x].accepted
    ensures ready(apply(s,c,Action::LeaderInfo(x,y)),c,y,x)
{
    reveal(enabled); reveal(apply); epochs::head(s,c,y,x); channels::facts(s,c,x,y); leader::step(s,c,Action::LeaderInfo(x,y),y);
    channels::facts(apply(s,c,Action::LeaderInfo(x,y)),c,x,y);
}
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),receipts::safe(s,c),epochs::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures node(apply(s,c,a),c,i)
{
    let u=apply(s,c,a);
    if u.election.nodes[i].role == Role::Following && session::syncing(u.nodes[i]) {
        if s.election.nodes[i].role == Role::Following && session::syncing(s.nodes[i]) {
            assert(node(s,c,i)); let j=s.nodes[i].leader.unwrap(); channels::facts(s,c,i,i); assert(c.servers.contains(j));
            session::follower_step(s,c,a,i); channels::facts(u,c,i,j); retained(s,c,a,j,i);
        } else {
            reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(a); if a != Action::Stutter { channels::facts(s,c,i,x); }
            match a {
                Action::LeaderInfo(x,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); if x == i { leader_info(s,c,x,y); } },
                Action::UpToDate(x,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); head(s,c,y,x); retained(s,c,a,y,x); },
                _ => {},
            }
        }
    }
}
pub proof fn pair_election(s: LState,c: Constants,ea: fle::Action,i: int,j: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,Action::Election(ea)),c),receipts::safe(s,c),safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i),c.servers.contains(j)
    ensures pair(apply(s,c,Action::Election(ea)),c,i,j)
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(Action::Election(ea)); channels::facts(s,c,i,x); channels::facts(s,c,j,x); assert(pair(s,c,i,j));
    let u=apply(s,c,Action::Election(ea));
    if u.election.nodes[i].role == Role::Leading && i != j && (u.nodes[i].forwarding.contains(j) || links::electing(u.nodes[i].electing,j) || links::ackld(u.nodes[i].ackld,j)) {
        assert(ready(s,c,i,j)); retained(s,c,Action::Election(ea),i,j);
    }
}
pub proof fn pair_environment(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),
        a is Crash || a is Partition || a is Recover || a is Start || a is Stutter
    ensures pair(apply(s,c,a),c,i,j)
{
    reveal(enabled); reveal(apply); let x=receiver(a); assert(pair(s,c,i,j)); assert(receipts::node(s,c,i)); channels::facts(s,c,i,j);
    if a != Action::Stutter { channels::facts(s,c,i,x); channels::facts(s,c,j,x); assert(receipts::node(s,c,x)); }
    if a is Crash { if let Some(y)=s.nodes[x].leader {
        channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y));
        links::disconnect_electing(s.nodes[y].electing,c,x,j); links::disconnect_ackld(s.nodes[y].ackld,c,x,j);
    } }
    if let Action::Partition(_,y)=a {
        channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y);
        links::disconnect_electing(s.nodes[x].electing,c,y,j); links::disconnect_ackld(s.nodes[x].ackld,c,y,j);
    }
    let u=apply(s,c,a);
    if u.election.nodes[i].role == Role::Leading && i != j && (u.nodes[i].forwarding.contains(j) || links::electing(u.nodes[i].electing,j) || links::ackld(u.nodes[i].ackld,j)) {
        assert(ready(s,c,i,j)); retained(s,c,a,i,j);
    }
}
#[verifier::spinoff_prover]
pub proof fn pair_protocol(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),
        !(a is Election),!(a is Crash),!(a is Partition),!(a is Recover),!(a is Start)
    ensures pair(apply(s,c,a),c,i,j)
{
    reveal(enabled); reveal(apply); let x=receiver(a); assert(pair(s,c,i,j)); assert(receipts::node(s,c,i)); channels::facts(s,c,i,j);
    if a != Action::Stutter { channels::facts(s,c,i,x); channels::facts(s,c,j,x); assert(receipts::node(s,c,x)); }
    match a {
        Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::Sync(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y));
            if a is LeaderInfo { links::disconnect_electing(s.nodes[y].electing,c,x,j); links::disconnect_ackld(s.nodes[y].ackld,c,x,j); }
            if a is AckEpoch {
                head(s,c,y,x); if let Message::AckEpoch(zxid,report)=s.msgs[(y,x)][0] {
                    let en=s.election.nodes[x]; let yes=!election_finished(s,c,x) && report > -1 && !(report > en.current || report == en.current && z::newer(zxid,en.processed.zxid));
                    links::update_electing(s.nodes[x].electing,y,zxid,yes,j);
                }
            }
            if a is AckLd { head(s,c,y,x); links::update_ackld(s.nodes[x].ackld,y,j); }
            if a is Sync {
                let r=choose |r: Electing| #![trigger s.nodes[x].electing.contains(r)] s.nodes[x].electing.contains(r) && r.sid == y && r.zxid != unset() && s.nodes[x].learners.contains(y);
                links::clear_electing(s.nodes[x].electing,r,j); assert(links::electing(s.nodes[x].electing,y)); assert(pair(s,c,x,y));
            }
        },_ => {},
    }
    let u=apply(s,c,a);
    if u.election.nodes[i].role == Role::Leading && i != j && (u.nodes[i].forwarding.contains(j) || links::electing(u.nodes[i].electing,j) || links::ackld(u.nodes[i].ackld,j)) {
        assert(ready(s,c,i,j)); retained(s,c,a,i,j);
    }
}
pub proof fn send_origin(s: LState,x: int,y: int,zxid: z::Zxid,k: int,mode: Mode,i: int,j: int,m: Message)
    requires sync_send(s,x,y,zxid,k,mode).msgs[(i,j)].contains(m),!s.msgs[(i,j)].contains(m)
    ensures i == x,j == y,forward(m)
{
    let n=s.nodes[x]; let e=s.election.nodes[x]; let end=e.history.len() as int;
    let committed=if n.phase == Phase::Broadcast { n.committed.index } else { end }; frames::sync_packets(e.history,k+1,end,committed);
    let u=sync_send(s,x,y,zxid,k,mode); let p=choose |p: int| 0 <= p < u.msgs[(i,j)].len() && u.msgs[(i,j)][p] == m;
    if p < s.msgs[(i,j)].len() { assert(s.msgs[(i,j)].contains(m)); assert(false); }
    if !forward(m) { assert(packets(e.history,k+1,end,committed).contains(m)); assert(false); }
}
pub proof fn fresh_sync(s: LState,c: Constants,x: int,y: int,i: int,j: int,m: Message)
    requires channels::safe(s,c),channels::safe(apply(s,c,Action::Sync(x,y)),c),receipts::safe(s,c),safe(s,c),enabled(s,c,Action::Sync(x,y)),c.servers.contains(i),c.servers.contains(j),
        apply(s,c,Action::Sync(x,y)).msgs[(i,j)].contains(m),!s.msgs[(i,j)].contains(m)
    ensures packet(apply(s,c,Action::Sync(x,y)),c,i,j,m)
{
    reveal(enabled); reveal(apply); channels::facts(s,c,x,y);
    let r=choose |r: Electing| #![trigger s.nodes[x].electing.contains(r)] s.nodes[x].electing.contains(r) && r.sid == y && r.zxid != unset() && s.nodes[x].learners.contains(y);
    if x == y { assert(r.zxid == unset()); assert(false); }
    assert(links::electing(s.nodes[x].electing,y)); assert(pair(s,c,x,y));
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
    retained(s,c,Action::Sync(x,y),x,y);
}
pub proof fn fresh_protocol(s: LState,c: Constants,a: Action,i: int,j: int,m: Message)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),receipts::safe(s,c),epochs::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),!(a is Sync),
        apply(s,c,a).msgs[(i,j)].contains(m),!s.msgs[(i,j)].contains(m)
    ensures packet(apply(s,c,a),c,i,j,m)
{
    reveal(enabled); reveal(apply); let x=receiver(a); channel_pair(c,i,j); channels::facts(s,c,i,j); assert(pair(s,c,i,j)); assert(pair(s,c,j,i)); assert(node(s,c,i));
    if a != Action::Stutter { channels::facts(s,c,i,x); channels::facts(s,c,j,x); }
    match a {
        Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y); } },
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y);
            if a is NewLeader || a is AckLd || a is UpToDate { head(s,c,y,x); }
            if a is AckLd { links::update_ackld(s.nodes[x].ackld,y,j); links::connected_member(z::update_al(s.nodes[x].ackld,y),j); links::connected_member(s.nodes[x].ackld,j); }
        },_ => {},
    }
    let u=apply(s,c,a); let k=choose |k: int| 0 <= k < u.msgs[(i,j)].len() && u.msgs[(i,j)][k] == m;
    assert forall |p: int| 0 <= p < s.msgs[(i,j)].len() implies s.msgs[(i,j)][p] != m by {}
    if m is AckEpoch { frames::epoch_origin(s,c,a,i,j,m); assert(a == Action::LeaderInfo(i,j)); leader_info(s,c,i,j); }
    else if forward(m) { assert(ready(s,c,i,j)); retained(s,c,a,i,j); }
    else if m is AckLd || m is Ack { assert(ready(s,c,j,i)); retained(s,c,a,j,i); }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires channels::safe(s,c),receipts::safe(s,c),epochs::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    channels::preserve(s,c,a); let u=apply(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u,c,i) by { preserve_node(s,c,a,i); }
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] pair(u,c,i,j) by {
        match a {
            Action::Election(ea) => { pair_election(s,c,ea,i,j); },
            Action::Crash(_) | Action::Partition(_,_) | Action::Recover(_,_) | Action::Start(_) => { pair_environment(s,c,a,i,j); },
            _ => { pair_protocol(s,c,a,i,j); },
        }
    }
    assert forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(u,c,i,j,m) by {
        if u.msgs[(i,j)].contains(m) {
            if s.msgs[(i,j)].contains(m) {
                assert(cell(s,c,i,j,m)); frames::step_roles(s,c,a,i,j);
                if forward(m) { retained(s,c,a,i,j); } else if m is AckEpoch || m is AckLd || m is Ack { retained(s,c,a,j,i); }
            } else if let Action::Sync(x,y)=a { fresh_sync(s,c,x,y,i,j,m); }
            else { fresh_protocol(s,c,a,i,j,m); }
        }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0
    ensures safe(b[tick],c)
    decreases tick
{
    if tick == 0 { initial_safe(c); }
    else { at(b,c,tick-1); channels::at(b,c,tick-1); receipts::at(b,c,tick-1); epochs::at(b,c,tick-1); let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a); }
}
} // verus!
