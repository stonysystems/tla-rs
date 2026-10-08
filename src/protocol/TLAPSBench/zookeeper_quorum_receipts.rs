//! Election receipts retain each positive acknowledgment until leadership ends.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role};
use super::zk_election as fle;
use super::zookeeper_channels as channels;
use super::zookeeper_receipts as receipts;
use super::zookeeper_receipt_sets as sets;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn ids(q: Set<Electing>) -> Set<int> { q.filter(|e: Electing| e.quorum).map(|e: Electing| e.sid) }
pub open spec fn member(q: Set<Electing>,i: int) -> bool { exists |r: Electing| #![trigger q.contains(r)] q.contains(r) && r.sid == i && r.quorum }
pub proof fn membership(q: Set<Electing>,i: int)
    ensures ids(q).contains(i) <==> member(q,i)
{
    if member(q,i) {
        let r=choose |r: Electing| #![trigger q.contains(r)] q.contains(r) && r.sid == i && r.quorum;
        assert(q.filter(|e: Electing| e.quorum).contains(r));
        q.filter(|e: Electing| e.quorum).lemma_map_contains(|e: Electing| e.sid,i);
    }
}
pub proof fn update(q: Set<Electing>,c: Constants,j: int,zxid: z::Zxid,yes: bool,i: int)
    requires sets::electing(q,c)
    ensures member(update_e(q,j,zxid,yes),i) <==> member(q,i) || i == j && yes
{
    if member(update_e(q,j,zxid,yes),i) {
        let r=choose |r: Electing| #![trigger update_e(q,j,zxid,yes).contains(r)] update_e(q,j,zxid,yes).contains(r) && r.sid == i && r.quorum;
        if q.contains(r) { assert(member(q,i)); }
        else if !(i == j && yes) {
            let old=choose |r: Electing| #![trigger q.contains(r)] q.contains(r) && r.sid == j; assert(q.contains(old) && old.quorum && old.sid == i); assert(member(q,i));
        }
    }
    if member(q,i) {
        let r=choose |r: Electing| #![trigger q.contains(r)] q.contains(r) && r.sid == i && r.quorum;
        if i != j { assert(update_e(q,j,zxid,yes).contains(r)); }
        else { assert(update_e(q,j,zxid,yes).contains(Electing { sid: j,zxid,quorum: true })); }
    }
    if i == j && yes { assert(update_e(q,j,zxid,yes).contains(Electing { sid: j,zxid,quorum: true })); }
}
pub proof fn disconnect(q: Set<Electing>,c: Constants,j: int,i: int)
    requires sets::electing(q,c)
    ensures member(disconnect_e(q,j),i) <==> member(q,i)
{
    if member(disconnect_e(q,j),i) {
        let r=choose |r: Electing| #![trigger disconnect_e(q,j).contains(r)] disconnect_e(q,j).contains(r) && r.sid == i && r.quorum;
        if q.contains(r) { assert(member(q,i)); }
        else { let old=choose |r: Electing| #![trigger q.contains(r)] q.contains(r) && r.sid == j; assert(q.contains(old) && old.sid == i && old.quorum); assert(member(q,i)); }
    }
    if member(q,i) {
        let r=choose |r: Electing| #![trigger q.contains(r)] q.contains(r) && r.sid == i && r.quorum;
        if i != j { assert(disconnect_e(q,j).contains(r)); }
        else { assert(disconnect_e(q,j).contains(Electing { zxid: unset(),..r })); }
    }
}
pub proof fn clear(q: Set<Electing>,r: Electing,i: int)
    ensures member(q.remove(r).insert(Electing { zxid: unset(),..r }),i) <==> member(q,i) || r.sid == i && r.quorum
{
    let u=q.remove(r).insert(Electing { zxid: unset(),..r });
    if member(u,i) { let t=choose |t: Electing| #![trigger u.contains(t)] u.contains(t) && t.sid == i && t.quorum; if t != (Electing { zxid: unset(),..r }) { assert(q.contains(t)); assert(member(q,i)); } }
    if member(q,i) { let t=choose |t: Electing| #![trigger q.contains(t)] q.contains(t) && t.sid == i && t.quorum; if t != r { assert(u.contains(t)); } else { assert(u.contains(Electing { zxid: unset(),..r })); } }
    if r.sid == i && r.quorum { assert(u.contains(Electing { zxid: unset(),..r })); }
}
pub open spec fn origin(s: LState,u: LState,a: Action,i: int,j: int) -> bool {
    u.election.nodes[i].role == Role::Leading && member(u.nodes[i].electing,j) && j != i ==>
        s.election.nodes[i].role == Role::Leading && (member(s.nodes[i].electing,j)
            || a == Action::AckEpoch(i,j) && s.msgs[(j,i)][0] is AckEpoch && s.msgs[(j,i)][0]->AckEpoch_1 >= 0)
}
pub proof fn election_origin(s: LState,c: Constants,ea: fle::Action,i: int,j: int)
    requires channels::safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i)
    ensures origin(s,apply(s,c,Action::Election(ea)),Action::Election(ea),i,j)
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(Action::Election(ea)); channels::facts(s,c,i,x);
}
pub proof fn protocol_origin(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election)
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    // Each Action variant is proved by its own helper lemma below, so
    // `apply` unfolds for one variant per query.
    match a {
        Action::Election(_) => protocol_origin_election(s,c,a,i,j),
        Action::Partition(_,_) => protocol_origin_partition(s,c,a,i,j),
        Action::Recover(_,_) => protocol_origin_recover(s,c,a,i,j),
        Action::Crash(_) => protocol_origin_crash(s,c,a,i,j),
        Action::Start(_) => protocol_origin_start(s,c,a,i,j),
        Action::Connect(_,_) => protocol_origin_connect(s,c,a,i,j),
        Action::FollowerInfo(_,_) => protocol_origin_follower_info(s,c,a,i,j),
        Action::LeaderInfo(_,_) => protocol_origin_leader_info(s,c,a,i,j),
        Action::AckEpoch(_,_) => protocol_origin_ack_epoch(s,c,a,i,j),
        Action::Sync(_,_) => protocol_origin_sync(s,c,a,i,j),
        Action::SyncMessage(_,_) => protocol_origin_sync_message(s,c,a,i,j),
        Action::ProposalSync(_,_) => protocol_origin_proposal_sync(s,c,a,i,j),
        Action::CommitSync(_,_) => protocol_origin_commit_sync(s,c,a,i,j),
        Action::NewLeader(_,_) => protocol_origin_new_leader(s,c,a,i,j),
        Action::AckLd(_,_) => protocol_origin_ack_ld(s,c,a,i,j),
        Action::UpToDate(_,_) => protocol_origin_up_to_date(s,c,a,i,j),
        Action::Request(_) => protocol_origin_request(s,c,a,i,j),
        Action::Proposal(_,_) => protocol_origin_proposal(s,c,a,i,j),
        Action::Ack(_,_) => protocol_origin_ack(s,c,a,i,j),
        Action::Commit(_,_) => protocol_origin_commit(s,c,a,i,j),
        Action::Stutter => protocol_origin_stutter(s,c,a,i,j),
    }
}
#[verifier::spinoff_prover]
proof fn protocol_origin_election(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        a is Election
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    let x=receiver(a); reveal(enabled); reveal(apply); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
}

#[verifier::spinoff_prover]
proof fn protocol_origin_partition(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        a is Partition
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    let x=receiver(a); reveal(enabled); reveal(apply); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
    match a { Action::Partition(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); disconnect(s.nodes[x].electing,c,y,j); disconnect(s.nodes[y].electing,c,x,j);  }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn protocol_origin_recover(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        a is Recover
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    let x=receiver(a); reveal(enabled); reveal(apply); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
    match a { Action::Recover(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); disconnect(s.nodes[x].electing,c,y,j); disconnect(s.nodes[y].electing,c,x,j);  }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn protocol_origin_crash(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        a is Crash
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    let x=receiver(a); reveal(enabled); reveal(apply); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
    match a { Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); disconnect(s.nodes[y].electing,c,x,j); } }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn protocol_origin_start(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        a is Start
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    let x=receiver(a); reveal(enabled); reveal(apply); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
}

#[verifier::spinoff_prover]
proof fn protocol_origin_connect(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        a is Connect
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    let x=receiver(a); reveal(enabled); reveal(apply); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
    match a { Action::Connect(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); disconnect(s.nodes[x].electing,c,y,j); disconnect(s.nodes[y].electing,c,x,j);  }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn protocol_origin_follower_info(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        a is FollowerInfo
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    let x=receiver(a); reveal(enabled); reveal(apply); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
    match a { Action::FollowerInfo(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); disconnect(s.nodes[x].electing,c,y,j); disconnect(s.nodes[y].electing,c,x,j);  }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn protocol_origin_leader_info(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        a is LeaderInfo
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    let x=receiver(a); reveal(enabled); reveal(apply); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
    match a { Action::LeaderInfo(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); disconnect(s.nodes[x].electing,c,y,j); disconnect(s.nodes[y].electing,c,x,j);  }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn protocol_origin_ack_epoch(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        a is AckEpoch
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    let x=receiver(a); reveal(enabled); reveal(apply); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
    match a { Action::AckEpoch(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); disconnect(s.nodes[x].electing,c,y,j); disconnect(s.nodes[y].electing,c,x,j); if let Message::AckEpoch(zxid,report)=s.msgs[(y,x)][0] { let en=s.election.nodes[x]; let yes=!election_finished(s,c,x) && report > -1 && !(report > en.current || report == en.current && z::newer(zxid,en.processed.zxid)); update(s.nodes[x].electing,c,y,zxid,yes,j); } }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn protocol_origin_sync(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        a is Sync
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    let x=receiver(a); reveal(enabled); reveal(apply); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
    match a { Action::Sync(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); disconnect(s.nodes[x].electing,c,y,j); disconnect(s.nodes[y].electing,c,x,j); let r=choose |r: Electing| #![trigger s.nodes[x].electing.contains(r)] s.nodes[x].electing.contains(r) && r.sid == y && r.zxid != unset() && s.nodes[x].learners.contains(y); clear(s.nodes[x].electing,r,j); if r.sid == j && r.quorum { assert(member(s.nodes[x].electing,j)); } }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn protocol_origin_sync_message(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        a is SyncMessage
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    let x=receiver(a); reveal(enabled); reveal(apply); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
    match a { Action::SyncMessage(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); disconnect(s.nodes[x].electing,c,y,j); disconnect(s.nodes[y].electing,c,x,j);  }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn protocol_origin_proposal_sync(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        a is ProposalSync
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    let x=receiver(a); reveal(enabled); reveal(apply); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
    match a { Action::ProposalSync(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); disconnect(s.nodes[x].electing,c,y,j); disconnect(s.nodes[y].electing,c,x,j);  }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn protocol_origin_commit_sync(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        a is CommitSync
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    let x=receiver(a); reveal(enabled); reveal(apply); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
    match a { Action::CommitSync(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); disconnect(s.nodes[x].electing,c,y,j); disconnect(s.nodes[y].electing,c,x,j);  }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn protocol_origin_new_leader(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        a is NewLeader
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    let x=receiver(a); reveal(enabled); reveal(apply); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
    match a { Action::NewLeader(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); disconnect(s.nodes[x].electing,c,y,j); disconnect(s.nodes[y].electing,c,x,j);  }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn protocol_origin_ack_ld(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        a is AckLd
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    let x=receiver(a); reveal(enabled); reveal(apply); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
    match a { Action::AckLd(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); disconnect(s.nodes[x].electing,c,y,j); disconnect(s.nodes[y].electing,c,x,j);  }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn protocol_origin_up_to_date(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        a is UpToDate
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    let x=receiver(a); reveal(enabled); reveal(apply); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
    match a { Action::UpToDate(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); disconnect(s.nodes[x].electing,c,y,j); disconnect(s.nodes[y].electing,c,x,j);  }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn protocol_origin_request(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        a is Request
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    hide(floor_index);
    let x=receiver(a); reveal(enabled); reveal(apply); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
}

#[verifier::spinoff_prover]
proof fn protocol_origin_proposal(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        a is Proposal
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    let x=receiver(a); reveal(enabled); reveal(apply); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
    match a { Action::Proposal(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); disconnect(s.nodes[x].electing,c,y,j); disconnect(s.nodes[y].electing,c,x,j);  }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn protocol_origin_ack(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        a is Ack
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    let x=receiver(a); reveal(enabled); reveal(apply); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
    match a { Action::Ack(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); disconnect(s.nodes[x].electing,c,y,j); disconnect(s.nodes[y].electing,c,x,j);  }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn protocol_origin_commit(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        a is Commit
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    hide(floor_index);
    let x=receiver(a); reveal(enabled); reveal(apply); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
    match a { Action::Commit(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); disconnect(s.nodes[x].electing,c,y,j); disconnect(s.nodes[y].electing,c,x,j);  }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn protocol_origin_stutter(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),
        a is Stutter
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    let x=receiver(a); reveal(enabled); reveal(apply); assert(receipts::node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(receipts::node(s,c,x)); }
}

pub proof fn step(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures origin(s,apply(s,c,a),a,i,j),s.election.nodes[i].role == Role::Leading && apply(s,c,a).election.nodes[i].role == Role::Leading
        && member(s.nodes[i].electing,j) ==> member(apply(s,c,a).nodes[i].electing,j)
{
    if let Action::Election(ea)=a {
        election_origin(s,c,ea,i,j); reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(a); channels::facts(s,c,i,x);
    } else { protocol_origin(s,c,a,i,j); }
}
pub proof fn finished_retained(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),enabled(s,c,a),c.servers.contains(i),s.election.nodes[i].role == Role::Leading,
        apply(s,c,a).election.nodes[i].role == Role::Leading,election_finished(s,c,i)
    ensures election_finished(apply(s,c,a),c,i)
{
    let u=apply(s,c,a); receipts::preserve(s,c,a); assert(receipts::node(u,c,i));
    assert(ids(u.nodes[i].electing).subset_of(c.servers)) by {
        assert forall |j: int| #![trigger c.servers.contains(j)] ids(u.nodes[i].electing).contains(j) implies c.servers.contains(j) by {
            membership(u.nodes[i].electing,j); let r=choose |r: Electing| #![trigger u.nodes[i].electing.contains(r)] u.nodes[i].electing.contains(r) && r.sid == j && r.quorum;
            u.nodes[i].electing.lemma_map_contains(|r: Electing| r.sid,j);
        }
    }
    assert(ids(s.nodes[i].electing).subset_of(ids(u.nodes[i].electing))) by {
        assert forall |j: int| ids(s.nodes[i].electing).contains(j) implies ids(u.nodes[i].electing).contains(j) by {
            membership(s.nodes[i].electing,j); step(s,c,a,i,j); membership(u.nodes[i].electing,j);
        }
    }
    super::zab_collections::quorum_superset(ids(s.nodes[i].electing),ids(u.nodes[i].electing),c);
}
} // verus!
