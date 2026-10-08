//! Completing discovery installs the accepted epoch as the leader's current epoch.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role,Phase};
use super::zk_election as fle;
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::zookeeper_receipts as receipts;
use super::zookeeper_quorum_receipts as quorum;
use super::zookeeper_leader_frame as leader;
use super::zookeeper_epoch_messages as messages;
use super::zookeeper_completion as completion;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn active(s: LState,c: Constants,i: int) -> bool {
    s.election.nodes[i].role == Role::Leading && c.servers.len() > 1 && election_finished(s,c,i)
}
pub open spec fn node(s: LState,c: Constants,i: int) -> bool {
    active(s,c,i) ==> (s.nodes[i].phase == Phase::Synchronization || s.nodes[i].phase == Phase::Broadcast)
        && s.election.nodes[i].current == s.nodes[i].accepted && formed(c,i,z::al_ids(s.nodes[i].connecting))
}
pub open spec fn safe(s: LState,c: Constants) -> bool { forall |i: int| c.servers.contains(i) ==> #[trigger] node(s,c,i) }
pub proof fn ids_bounded(s: LState,c: Constants,i: int)
    requires receipts::safe(s,c),c.servers.contains(i)
    ensures quorum::ids(s.nodes[i].electing).subset_of(c.servers)
{
    assert(receipts::node(s,c,i));
    assert forall |j: int| #![trigger c.servers.contains(j)] quorum::ids(s.nodes[i].electing).contains(j) implies c.servers.contains(j) by {
        quorum::membership(s.nodes[i].electing,j); let r=choose |r: Electing| #![trigger s.nodes[i].electing.contains(r)] s.nodes[i].electing.contains(r) && r.sid == j && r.quorum;
        s.nodes[i].electing.lemma_map_contains(|r: Electing| r.sid,j);
    }
}
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(initial(c),c,i) by {}
}
pub proof fn first_finished(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),messages::safe(s,c),enabled(s,c,a),c.servers.contains(i),
        active(apply(s,c,a),c,i),!active(s,c,i)
    ensures node(apply(s,c,a),c,i)
{
    let u=apply(s,c,a); let q=quorum::ids(u.nodes[i].electing); let old=quorum::ids(s.nodes[i].electing);
    if q.subset_of(set![i]) { vstd::set_lib::lemma_len_subset(q,set![i]); assert(false); }
    let peer=choose |j: int| q.contains(j) && j != i;
    quorum::membership(u.nodes[i].electing,peer); quorum::step(s,c,a,i,peer); assert(s.election.nodes[i].role == Role::Leading);
    assert(receipts::node(s,c,i)); assert(quorum::member(s.nodes[i].electing,i)); quorum::membership(s.nodes[i].electing,i); ids_bounded(s,c,i);
    if q.subset_of(old) { super::zab_collections::quorum_superset(q,old,c); assert(false); }
    let j=choose |j: int| q.contains(j) && !old.contains(j); assert(j != i);
    quorum::membership(u.nodes[i].electing,j); quorum::membership(s.nodes[i].electing,j); quorum::step(s,c,a,i,j);
    assert(a == Action::AckEpoch(i,j)); reveal(enabled); reveal(apply); messages::head(s,c,j,i);
}
pub proof fn continuing_election(s: LState,c: Constants,ea: fle::Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,Action::Election(ea)),c.servers.contains(i),
        active(s,c,i),active(apply(s,c,Action::Election(ea)),c,i)
    ensures node(apply(s,c,Action::Election(ea)),c,i)
{
    assert(node(s,c,i)); leader::step(s,c,Action::Election(ea),i);
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(Action::Election(ea)); channels::facts(s,c,i,x);
}
pub proof fn continuing_fields(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i)
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    // Each Action variant is proved by its own helper lemma below, so
    // `apply` unfolds for one variant per query.
    match a {
        Action::Election(_) => continuing_fields_election(s,c,a,i),
        Action::Partition(_,_) => continuing_fields_partition(s,c,a,i),
        Action::Recover(_,_) => continuing_fields_recover(s,c,a,i),
        Action::Crash(_) => continuing_fields_crash(s,c,a,i),
        Action::Start(_) => continuing_fields_start(s,c,a,i),
        Action::Connect(_,_) => continuing_fields_connect(s,c,a,i),
        Action::FollowerInfo(_,_) => continuing_fields_follower_info(s,c,a,i),
        Action::LeaderInfo(_,_) => continuing_fields_leader_info(s,c,a,i),
        Action::AckEpoch(_,_) => continuing_fields_ack_epoch(s,c,a,i),
        Action::Sync(_,_) => continuing_fields_sync(s,c,a,i),
        Action::SyncMessage(_,_) => continuing_fields_sync_message(s,c,a,i),
        Action::ProposalSync(_,_) => continuing_fields_proposal_sync(s,c,a,i),
        Action::CommitSync(_,_) => continuing_fields_commit_sync(s,c,a,i),
        Action::NewLeader(_,_) => continuing_fields_new_leader(s,c,a,i),
        Action::AckLd(_,_) => continuing_fields_ack_ld(s,c,a,i),
        Action::UpToDate(_,_) => continuing_fields_up_to_date(s,c,a,i),
        Action::Request(_) => continuing_fields_request(s,c,a,i),
        Action::Proposal(_,_) => continuing_fields_proposal(s,c,a,i),
        Action::Ack(_,_) => continuing_fields_ack(s,c,a,i),
        Action::Commit(_,_) => continuing_fields_commit(s,c,a,i),
        Action::Stutter => continuing_fields_stutter(s,c,a,i),
    }
}
#[verifier::spinoff_prover]
proof fn continuing_fields_election(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i),
        a is Election
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    let x=receiver(a); assert(node(s,c,i)); reveal(enabled); reveal(apply); if a != Action::Stutter { channels::facts(s,c,i,x); }
}

#[verifier::spinoff_prover]
proof fn continuing_fields_partition(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i),
        a is Partition
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    let x=receiver(a); assert(node(s,c,i)); reveal(enabled); reveal(apply); if a != Action::Stutter { channels::facts(s,c,i,x); }
    match a { Action::Partition(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn continuing_fields_recover(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i),
        a is Recover
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    let x=receiver(a); assert(node(s,c,i)); reveal(enabled); reveal(apply); if a != Action::Stutter { channels::facts(s,c,i,x); }
    match a { Action::Recover(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn continuing_fields_crash(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i),
        a is Crash
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    let x=receiver(a); assert(node(s,c,i)); reveal(enabled); reveal(apply); if a != Action::Stutter { channels::facts(s,c,i,x); }
    match a { Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,x,y); } }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn continuing_fields_start(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i),
        a is Start
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    let x=receiver(a); assert(node(s,c,i)); reveal(enabled); reveal(apply); if a != Action::Stutter { channels::facts(s,c,i,x); }
}

#[verifier::spinoff_prover]
proof fn continuing_fields_connect(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i),
        a is Connect
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    let x=receiver(a); assert(node(s,c,i)); reveal(enabled); reveal(apply); if a != Action::Stutter { channels::facts(s,c,i,x); }
    match a { Action::Connect(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn continuing_fields_follower_info(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i),
        a is FollowerInfo
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    let x=receiver(a); assert(node(s,c,i)); reveal(enabled); reveal(apply); if a != Action::Stutter { channels::facts(s,c,i,x); }
    match a { Action::FollowerInfo(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn continuing_fields_leader_info(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i),
        a is LeaderInfo
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    let x=receiver(a); assert(node(s,c,i)); reveal(enabled); reveal(apply); if a != Action::Stutter { channels::facts(s,c,i,x); }
    match a { Action::LeaderInfo(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn continuing_fields_ack_epoch(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i),
        a is AckEpoch
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    let x=receiver(a); assert(node(s,c,i)); reveal(enabled); reveal(apply); if a != Action::Stutter { channels::facts(s,c,i,x); }
    match a { Action::AckEpoch(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn continuing_fields_sync(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i),
        a is Sync
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    let x=receiver(a); assert(node(s,c,i)); reveal(enabled); reveal(apply); if a != Action::Stutter { channels::facts(s,c,i,x); }
    match a { Action::Sync(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn continuing_fields_sync_message(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i),
        a is SyncMessage
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    let x=receiver(a); assert(node(s,c,i)); reveal(enabled); reveal(apply); if a != Action::Stutter { channels::facts(s,c,i,x); }
    match a { Action::SyncMessage(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn continuing_fields_proposal_sync(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i),
        a is ProposalSync
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    let x=receiver(a); assert(node(s,c,i)); reveal(enabled); reveal(apply); if a != Action::Stutter { channels::facts(s,c,i,x); }
    match a { Action::ProposalSync(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn continuing_fields_commit_sync(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i),
        a is CommitSync
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    let x=receiver(a); assert(node(s,c,i)); reveal(enabled); reveal(apply); if a != Action::Stutter { channels::facts(s,c,i,x); }
    match a { Action::CommitSync(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn continuing_fields_new_leader(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i),
        a is NewLeader
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    let x=receiver(a); assert(node(s,c,i)); reveal(enabled); reveal(apply); if a != Action::Stutter { channels::facts(s,c,i,x); }
    match a { Action::NewLeader(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn continuing_fields_ack_ld(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i),
        a is AckLd
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    // floor_index is irrelevant to these fields; its choose/forall
    // otherwise dominates the query.
    hide(floor_index);
    let x=receiver(a); assert(node(s,c,i)); reveal(enabled); reveal(apply); if a != Action::Stutter { channels::facts(s,c,i,x); }
    match a { Action::AckLd(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn continuing_fields_up_to_date(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i),
        a is UpToDate
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    let x=receiver(a); assert(node(s,c,i)); reveal(enabled); reveal(apply); if a != Action::Stutter { channels::facts(s,c,i,x); }
    match a { Action::UpToDate(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn continuing_fields_request(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i),
        a is Request
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    hide(floor_index);
    let x=receiver(a); assert(node(s,c,i)); reveal(enabled); reveal(apply); if a != Action::Stutter { channels::facts(s,c,i,x); }
}

#[verifier::spinoff_prover]
proof fn continuing_fields_proposal(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i),
        a is Proposal
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    let x=receiver(a); assert(node(s,c,i)); reveal(enabled); reveal(apply); if a != Action::Stutter { channels::facts(s,c,i,x); }
    match a { Action::Proposal(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn continuing_fields_ack(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i),
        a is Ack
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    let x=receiver(a); assert(node(s,c,i)); reveal(enabled); reveal(apply); if a != Action::Stutter { channels::facts(s,c,i,x); }
    match a { Action::Ack(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn continuing_fields_commit(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i),
        a is Commit
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    let x=receiver(a); assert(node(s,c,i)); reveal(enabled); reveal(apply); if a != Action::Stutter { channels::facts(s,c,i,x); }
    match a { Action::Commit(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn continuing_fields_stutter(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i),
        a is Stutter
    ensures apply(s,c,a).election.nodes[i].current == s.election.nodes[i].current,
        apply(s,c,a).nodes[i].phase == Phase::Synchronization || apply(s,c,a).nodes[i].phase == Phase::Broadcast
{
    let x=receiver(a); assert(node(s,c,i)); reveal(enabled); reveal(apply); if a != Action::Stutter { channels::facts(s,c,i,x); }
}

pub proof fn continuing_protocol(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),receipts::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i),!(a is Election),active(s,c,i),active(apply(s,c,a),c,i)
    ensures node(apply(s,c,a),c,i)
{
    assert(node(s,c,i)); leader::step(s,c,a,i); continuing_fields(s,c,a,i);
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires channels::safe(s,c),receipts::safe(s,c),messages::safe(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u,c,i) by {
        if active(u,c,i) {
            if !active(s,c,i) { first_finished(s,c,a,i); }
            else if let Action::Election(ea)=a { continuing_election(s,c,ea,i); }
            else { continuing_protocol(s,c,a,i); }
        }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,tick: int)
    requires support::safety_spec(b,c),tick >= 0
    ensures safe(b[tick],c)
    decreases tick
{
    if tick == 0 { initial_safe(c); }
    else { at(b,c,tick-1); channels::at(b,c,tick-1); receipts::at(b,c,tick-1); messages::at(b,c,tick-1); let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a); }
}
pub proof fn broadcasting(b: Behavior<LState>,c: Constants,tick: int,i: int)
    requires support::safety_spec(b,c),tick >= 0,c.servers.contains(i),c.servers.len() > 1,
        b[tick].election.nodes[i].role == Role::Leading,b[tick].nodes[i].phase == Phase::Broadcast
    ensures b[tick].election.nodes[i].current == b[tick].nodes[i].accepted
{
    at(b,c,tick); completion::at(b,c,tick); assert(completion::node(b[tick],c,i)); assert(node(b[tick],c,i));
}
} // verus!
