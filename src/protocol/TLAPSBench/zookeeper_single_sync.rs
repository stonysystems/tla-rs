//! An epoch acknowledgment can authorize only one synchronization batch per connection.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role,Phase};
use super::zk_election as fle;
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::zookeeper_receipts as receipts;
use super::zookeeper_receipt_links as links;
use super::zookeeper_ready as ready;
use super::zookeeper_ack_count as counts;
use super::zab_connections::channel_pair;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn pending(s: LState,i: int,j: int) -> nat {
    counts::count(s.msgs[(j,i)])+counts::bit(links::electing(s.nodes[i].electing,j))+counts::bit(s.nodes[i].forwarding.contains(j))
}
pub open spec fn pair(s: LState,i: int,j: int) -> bool { s.election.nodes[i].role == Role::Leading && i != j ==> pending(s,i,j) <= 1 }
pub open spec fn safe(s: LState,c: Constants) -> bool {
    forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) ==> #[trigger] pair(s,i,j)
}
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] pair(initial(c),i,j) by {}
}
pub proof fn no_acks(s: LState,c: Constants,i: int,j: int)
    requires ready::safe(s,c),c.servers.contains(i),c.servers.contains(j),s.election.nodes[i].role != Role::Leading || s.nodes[j].phase == Phase::Discovery
    ensures counts::count(s.msgs[(j,i)]) == 0
{
    let q=s.msgs[(j,i)];
    assert forall |m: Message| q.contains(m) implies !counts::is_ack(m) by { assert(ready::cell(s,c,j,i,m)); }
    counts::absent(q);
}
pub proof fn flags_nonincrease(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),!(a is Election),!(a is Sync),!(a is AckEpoch),apply(s,c,a).election.nodes[i].role == Role::Leading
    ensures s.election.nodes[i].role == Role::Leading,
        links::electing(apply(s,c,a).nodes[i].electing,j) ==> links::electing(s.nodes[i].electing,j),
        apply(s,c,a).nodes[i].forwarding.contains(j) ==> s.nodes[i].forwarding.contains(j)
{
    reveal(enabled); reveal(apply); let x=receiver(a); channels::facts(s,c,i,j); assert(receipts::node(s,c,i));
    if a != Action::Stutter { channels::facts(s,c,i,x); channels::facts(s,c,j,x); assert(receipts::node(s,c,x)); }
    match a {
        Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); links::disconnect_electing(s.nodes[y].electing,c,x,j); } },
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y));
            links::disconnect_electing(s.nodes[x].electing,c,y,j); links::disconnect_electing(s.nodes[y].electing,c,x,j);
        },_ => {},
    }
}
pub proof fn election_pair(s: LState,c: Constants,ea: fle::Action,i: int,j: int)
    requires channels::safe(s,c),ready::safe(s,c),safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i),c.servers.contains(j)
    ensures pair(apply(s,c,Action::Election(ea)),i,j)
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(Action::Election(ea)); channels::facts(s,c,i,x); channels::facts(s,c,j,x); assert(pair(s,i,j));
    if s.election.nodes[i].role != Role::Leading { no_acks(s,c,i,j); }
}
pub proof fn leader_info_pair(s: LState,c: Constants,x: int,y: int,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),ready::safe(s,c),safe(s,c),enabled(s,c,Action::LeaderInfo(x,y)),c.servers.contains(i),c.servers.contains(j)
    ensures pair(apply(s,c,Action::LeaderInfo(x,y)),i,j)
{
    reveal(enabled); reveal(apply); channel_pair(c,j,i); channels::facts(s,c,i,x); channels::facts(s,c,j,x); channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y);
    let a=Action::LeaderInfo(x,y); let u=apply(s,c,a); counts::empty(); counts::facts(s.msgs[(j,i)]); counts::facts(s.msgs[(x,y)]); counts::facts(s.msgs[(y,x)]); assert(pair(s,i,j));
    if u.election.nodes[i].role == Role::Leading && i != j {
        flags_nonincrease(s,c,a,i,j);
        if let Message::LeaderInfo(zxid)=s.msgs[(y,x)][0] {
            let report=if zxid.epoch > s.nodes[x].accepted { s.election.nodes[x].current } else { -1 };
            let m=Message::AckEpoch(s.election.nodes[x].processed.zxid,report); counts::single(m); counts::concat(s.msgs[(x,y)],seq![m]);
            if s.nodes[x].phase == Phase::Discovery && zxid.epoch >= s.nodes[x].accepted && i == y && j == x {
                no_acks(s,c,i,j); assert(ready::pair(s,c,i,j)); assert(!links::electing(s.nodes[i].electing,j)); assert(!s.nodes[i].forwarding.contains(j));
            }
        }
    }
}
pub proof fn ackepoch_pair(s: LState,c: Constants,x: int,y: int,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,Action::AckEpoch(x,y)),c.servers.contains(i),c.servers.contains(j)
    ensures pair(apply(s,c,Action::AckEpoch(x,y)),i,j)
{
    reveal(enabled); reveal(apply); channel_pair(c,j,i); channels::facts(s,c,i,x); channels::facts(s,c,j,x); channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y); assert(pair(s,i,j));
    let a=Action::AckEpoch(x,y); let u=apply(s,c,a); counts::facts(s.msgs[(j,i)]); counts::other_count(s,c,a,j,i);
    if u.election.nodes[i].role == Role::Leading && i != j {
        assert(s.election.nodes[i].role == Role::Leading);
        if let Message::AckEpoch(zxid,report)=s.msgs[(y,x)][0] {
            let en=s.election.nodes[x]; let yes=!election_finished(s,c,x) && report > -1 && !(report > en.current || report == en.current && z::newer(zxid,en.processed.zxid));
            links::update_electing(s.nodes[x].electing,y,zxid,yes,j);
            if i == x && j == y { assert(counts::count(s.msgs[(j,i)]) == 1); assert(!s.nodes[i].forwarding.contains(j)); }
        }
    }
}
pub proof fn sync_pair(s: LState,c: Constants,x: int,y: int,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,Action::Sync(x,y)),c.servers.contains(i),c.servers.contains(j)
    ensures pair(apply(s,c,Action::Sync(x,y)),i,j)
{
    reveal(enabled); reveal(apply); channels::facts(s,c,i,x); channels::facts(s,c,j,x); channels::facts(s,c,x,y); assert(receipts::node(s,c,x)); assert(pair(s,i,j));
    counts::sync_count(s,c,x,y,j,i);
    let r=choose |r: Electing| s.nodes[x].electing.contains(r) && r.sid == y && r.zxid != unset() && s.nodes[x].learners.contains(y);
    if x == y { assert(r.zxid == unset()); assert(false); }
    links::clear_electing(s.nodes[x].electing,r,j); links::clear_current(s.nodes[x].electing,c,r);
    if i == x && j == y { assert(links::electing(s.nodes[x].electing,y)); assert(counts::count(s.msgs[(j,i)]) == 0); assert(!s.nodes[i].forwarding.contains(j)); }
}
pub proof fn other_pair(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),!(a is Election),!(a is LeaderInfo),!(a is AckEpoch),!(a is Sync)
    ensures pair(apply(s,c,a),i,j)
{
    counts::other_count(s,c,a,j,i); let u=apply(s,c,a); assert(pair(s,i,j));
    if u.election.nodes[i].role == Role::Leading { flags_nonincrease(s,c,a,i,j); }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires channels::safe(s,c),receipts::safe(s,c),ready::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a);
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] pair(u,i,j) by {
        match a {
            Action::Election(ea) => { election_pair(s,c,ea,i,j); },
            Action::LeaderInfo(x,y) => { leader_info_pair(s,c,x,y,i,j); },
            Action::AckEpoch(x,y) => { ackepoch_pair(s,c,x,y,i,j); },
            Action::Sync(x,y) => { sync_pair(s,c,x,y,i,j); },
            _ => { other_pair(s,c,a,i,j); },
        }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0
    ensures safe(b[tick],c)
    decreases tick
{
    if tick == 0 { initial_safe(c); }
    else { at(b,c,tick-1); channels::at(b,c,tick-1); receipts::at(b,c,tick-1); ready::at(b,c,tick-1); let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a); }
}
pub proof fn before_sync(s: LState,c: Constants,i: int,j: int)
    requires channels::safe(s,c),safe(s,c),enabled(s,c,Action::Sync(i,j))
    ensures !s.nodes[i].forwarding.contains(j),counts::count(s.msgs[(j,i)]) == 0
{
    reveal(enabled); channels::facts(s,c,i,j); let r=choose |r: Electing| s.nodes[i].electing.contains(r) && r.sid == j && r.zxid != unset() && s.nodes[i].learners.contains(j);
    if i == j { assert(r.zxid == unset()); assert(false); }
    assert(links::electing(s.nodes[i].electing,j)); assert(pair(s,i,j));
}
} // verus!
