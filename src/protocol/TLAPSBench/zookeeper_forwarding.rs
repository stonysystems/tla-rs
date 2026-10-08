//! A synchronization batch precedes every proposal, commit, and activation acknowledgment on a connection.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{self as z,Role,Phase};
use super::zk_election as fle;
use super::zookeeper_support as support;
use super::zookeeper_channels as channels;
use super::zookeeper_receipts as receipts;
use super::zookeeper_receipt_links as links;
use super::zookeeper_ready as ready;
use super::zookeeper_message_frames as frames;
use super::zookeeper_session_frames as session;
use super::zab_connections::channel_pair;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub open spec fn node(s: LState,c: Constants,i: int) -> bool {
    (s.nodes[i].received_leader ==> s.election.nodes[i].role == Role::Following)
    && (s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast) ==>
        s.nodes[i].leader is Some && s.nodes[s.nodes[i].leader.unwrap()].forwarding.contains(i))
}
pub open spec fn pair(s: LState,i: int,j: int) -> bool {
    s.election.nodes[i].role == Role::Leading && i != j && links::ackld(s.nodes[i].ackld,j) ==> s.nodes[i].forwarding.contains(j)
}
pub open spec fn packet(s: LState,i: int,j: int,m: Message) -> bool {
    if ready::forward(m) { s.nodes[i].forwarding.contains(j) } else if m is AckLd || m is Ack { s.nodes[j].forwarding.contains(i) } else { true }
}
pub open spec fn cell(s: LState,i: int,j: int,m: Message) -> bool { s.msgs[(i,j)].contains(m) ==> packet(s,i,j,m) }
pub open spec fn safe(s: LState,c: Constants) -> bool {
    (forall |i: int| c.servers.contains(i) ==> #[trigger] node(s,c,i))
    && (forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) ==> #[trigger] pair(s,i,j))
    && forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) ==> #[trigger] cell(s,i,j,m)
}
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    let s=initial(c);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(s,c,i) by {}
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] pair(s,i,j) by {}
    assert forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(s,i,j,m) by { channel_pair(c,i,j); }
}
pub proof fn head(s: LState,c: Constants,i: int,j: int)
    requires safe(s,c),c.servers.contains(i),c.servers.contains(j),s.msgs[(i,j)].len() > 0
    ensures packet(s,i,j,s.msgs[(i,j)][0])
{
    assert(s.msgs[(i,j)].contains(s.msgs[(i,j)][0])); assert(cell(s,i,j,s.msgs[(i,j)][0]));
}
#[verifier::spinoff_prover]
pub proof fn retained(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),i != j,
        s.election.nodes[i].role == Role::Leading,s.nodes[i].forwarding.contains(j),
        apply(s,c,a).election.nodes[i].role == Role::Leading,apply(s,c,a).election.nodes[j].role == Role::Following
    ensures apply(s,c,a).nodes[i].forwarding.contains(j)
{
    hide(floor_index);
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(a); channels::facts(s,c,i,j);
    if a != Action::Stutter { channels::facts(s,c,i,x); channels::facts(s,c,j,x); }
    match a {
        Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y); } },
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::Sync(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y);
        },_ => {},
    }
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn received_role(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),safe(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures apply(s,c,a).nodes[i].received_leader ==> apply(s,c,a).election.nodes[i].role == Role::Following
{
    hide(floor_index);
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(a); assert(node(s,c,i));
    if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
    if a is Crash { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,x,y); } }
    match a {
        Action::Partition(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) => { channels::facts(s,c,i,y); channels::facts(s,c,x,y); },
        _ => {},
    }
}
pub proof fn first_activation(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast))
    ensures node(apply(s,c,a),c,i)
{
    // Each Action variant is proved by its own helper lemma below, so
    // `apply` unfolds for one variant per query.
    match a {
        Action::Election(_) => first_activation_election(s,c,a,i),
        Action::Partition(_,_) => first_activation_partition(s,c,a,i),
        Action::Recover(_,_) => first_activation_recover(s,c,a,i),
        Action::Crash(_) => first_activation_crash(s,c,a,i),
        Action::Start(_) => first_activation_start(s,c,a,i),
        Action::Connect(_,_) => first_activation_connect(s,c,a,i),
        Action::FollowerInfo(_,_) => first_activation_follower_info(s,c,a,i),
        Action::LeaderInfo(_,_) => first_activation_leader_info(s,c,a,i),
        Action::AckEpoch(_,_) => first_activation_ack_epoch(s,c,a,i),
        Action::Sync(_,_) => first_activation_sync(s,c,a,i),
        Action::SyncMessage(_,_) => first_activation_sync_message(s,c,a,i),
        Action::ProposalSync(_,_) => first_activation_proposal_sync(s,c,a,i),
        Action::CommitSync(_,_) => first_activation_commit_sync(s,c,a,i),
        Action::NewLeader(_,_) => first_activation_new_leader(s,c,a,i),
        Action::AckLd(_,_) => first_activation_ack_ld(s,c,a,i),
        Action::UpToDate(_,_) => first_activation_up_to_date(s,c,a,i),
        Action::Request(_) => first_activation_request(s,c,a,i),
        Action::Proposal(_,_) => first_activation_proposal(s,c,a,i),
        Action::Ack(_,_) => first_activation_ack(s,c,a,i),
        Action::Commit(_,_) => first_activation_commit(s,c,a,i),
        Action::Stutter => first_activation_stutter(s,c,a,i),
    }
}
#[verifier::spinoff_prover]
proof fn first_activation_election(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast)),
        a is Election
    ensures node(apply(s,c,a),c,i)
{
    let x=receiver(a); reveal(enabled); reveal(apply); reveal(fle::apply); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
}

#[verifier::spinoff_prover]
proof fn first_activation_partition(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast)),
        a is Partition
    ensures node(apply(s,c,a),c,i)
{
    let x=receiver(a); reveal(enabled); reveal(apply); reveal(fle::apply); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
}

#[verifier::spinoff_prover]
proof fn first_activation_recover(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast)),
        a is Recover
    ensures node(apply(s,c,a),c,i)
{
    let x=receiver(a); reveal(enabled); reveal(apply); reveal(fle::apply); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
}

#[verifier::spinoff_prover]
proof fn first_activation_crash(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast)),
        a is Crash
    ensures node(apply(s,c,a),c,i)
{
    hide(floor_index);
    let x=receiver(a); reveal(enabled); reveal(apply); reveal(fle::apply); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
}

#[verifier::spinoff_prover]
proof fn first_activation_start(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast)),
        a is Start
    ensures node(apply(s,c,a),c,i)
{
    let x=receiver(a); reveal(enabled); reveal(apply); reveal(fle::apply); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
}

#[verifier::spinoff_prover]
proof fn first_activation_connect(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast)),
        a is Connect
    ensures node(apply(s,c,a),c,i)
{
    let x=receiver(a); reveal(enabled); reveal(apply); reveal(fle::apply); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
}

#[verifier::spinoff_prover]
proof fn first_activation_follower_info(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast)),
        a is FollowerInfo
    ensures node(apply(s,c,a),c,i)
{
    hide(floor_index);
    let x=receiver(a); reveal(enabled); reveal(apply); reveal(fle::apply); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
}

#[verifier::spinoff_prover]
proof fn first_activation_leader_info(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast)),
        a is LeaderInfo
    ensures node(apply(s,c,a),c,i)
{
    hide(floor_index);
    let x=receiver(a); reveal(enabled); reveal(apply); reveal(fle::apply); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
}

#[verifier::spinoff_prover]
proof fn first_activation_ack_epoch(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast)),
        a is AckEpoch
    ensures node(apply(s,c,a),c,i)
{
    let x=receiver(a); reveal(enabled); reveal(apply); reveal(fle::apply); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
}

#[verifier::spinoff_prover]
proof fn first_activation_sync(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast)),
        a is Sync
    ensures node(apply(s,c,a),c,i)
{
    let x=receiver(a); reveal(enabled); reveal(apply); reveal(fle::apply); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
}

#[verifier::spinoff_prover]
proof fn first_activation_sync_message(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast)),
        a is SyncMessage
    ensures node(apply(s,c,a),c,i)
{
    let x=receiver(a); reveal(enabled); reveal(apply); reveal(fle::apply); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
}

#[verifier::spinoff_prover]
proof fn first_activation_proposal_sync(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast)),
        a is ProposalSync
    ensures node(apply(s,c,a),c,i)
{
    let x=receiver(a); reveal(enabled); reveal(apply); reveal(fle::apply); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
}

#[verifier::spinoff_prover]
proof fn first_activation_commit_sync(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast)),
        a is CommitSync
    ensures node(apply(s,c,a),c,i)
{
    let x=receiver(a); reveal(enabled); reveal(apply); reveal(fle::apply); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
}

#[verifier::spinoff_prover]
proof fn first_activation_new_leader(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast)),
        a is NewLeader
    ensures node(apply(s,c,a),c,i)
{
    let x=receiver(a); reveal(enabled); reveal(apply); reveal(fle::apply); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
    match a { Action::NewLeader(_,y) => { channels::facts(s,c,x,y); head(s,c,y,x); ready::head(s,c,y,x); retained(s,c,a,y,x); }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn first_activation_ack_ld(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast)),
        a is AckLd
    ensures node(apply(s,c,a),c,i)
{
    hide(floor_index);
    let x=receiver(a); reveal(enabled); reveal(apply); reveal(fle::apply); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
}

#[verifier::spinoff_prover]
proof fn first_activation_up_to_date(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast)),
        a is UpToDate
    ensures node(apply(s,c,a),c,i)
{
    let x=receiver(a); reveal(enabled); reveal(apply); reveal(fle::apply); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
    match a { Action::UpToDate(_,y) => { channels::facts(s,c,x,y); head(s,c,y,x); ready::head(s,c,y,x); retained(s,c,a,y,x); }, _ => {} }
}

#[verifier::spinoff_prover]
proof fn first_activation_request(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast)),
        a is Request
    ensures node(apply(s,c,a),c,i)
{
    let x=receiver(a); reveal(enabled); reveal(apply); reveal(fle::apply); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
}

#[verifier::spinoff_prover]
proof fn first_activation_proposal(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast)),
        a is Proposal
    ensures node(apply(s,c,a),c,i)
{
    let x=receiver(a); reveal(enabled); reveal(apply); reveal(fle::apply); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
}

#[verifier::spinoff_prover]
proof fn first_activation_ack(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast)),
        a is Ack
    ensures node(apply(s,c,a),c,i)
{
    hide(floor_index);
    let x=receiver(a); reveal(enabled); reveal(apply); reveal(fle::apply); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
}

#[verifier::spinoff_prover]
proof fn first_activation_commit(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast)),
        a is Commit
    ensures node(apply(s,c,a),c,i)
{
    hide(floor_index);
    let x=receiver(a); reveal(enabled); reveal(apply); reveal(fle::apply); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
}

#[verifier::spinoff_prover]
proof fn first_activation_stutter(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),
        apply(s,c,a).election.nodes[i].role == Role::Following,apply(s,c,a).nodes[i].received_leader || apply(s,c,a).nodes[i].phase == Phase::Broadcast,
        !(s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast)),
        a is Stutter
    ensures node(apply(s,c,a),c,i)
{
    let x=receiver(a); reveal(enabled); reveal(apply); reveal(fle::apply); assert(node(s,c,i)); if a != Action::Stutter { channels::facts(s,c,i,x); assert(node(s,c,x)); }
}
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures node(apply(s,c,a),c,i)
{
    let u=apply(s,c,a); assert(node(s,c,i)); received_role(s,c,a,i);
    if u.election.nodes[i].role == Role::Following && (u.nodes[i].received_leader || u.nodes[i].phase == Phase::Broadcast) {
        if s.election.nodes[i].role == Role::Following && (s.nodes[i].received_leader || s.nodes[i].phase == Phase::Broadcast) {
            let j=s.nodes[i].leader.unwrap(); channels::facts(s,c,i,i); assert(c.servers.contains(j));
            session::follower_step(s,c,a,i); channels::facts(s,c,i,j); channels::facts(u,c,i,j); retained(s,c,a,j,i);
        } else { first_activation(s,c,a,i); }
    }
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn preserve_pair(s: LState,c: Constants,a: Action,i: int,j: int)
    requires channels::safe(s,c),channels::safe(apply(s,c,a),c),receipts::safe(s,c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j)
    ensures pair(apply(s,c,a),i,j)
{
    reveal(enabled); reveal(apply); reveal(fle::apply); let x=receiver(a); assert(pair(s,i,j)); channels::facts(s,c,i,j); assert(receipts::node(s,c,i));
    if a != Action::Stutter { channels::facts(s,c,i,x); channels::facts(s,c,j,x); assert(receipts::node(s,c,x)); }
    match a {
        Action::Crash(_) => { if let Some(y)=s.nodes[x].leader { channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y)); links::disconnect_ackld(s.nodes[y].ackld,c,x,j); } },
        Action::Partition(_,y) | Action::Recover(_,y) | Action::Connect(_,y) | Action::FollowerInfo(_,y) | Action::LeaderInfo(_,y) | Action::AckEpoch(_,y) | Action::Sync(_,y) | Action::SyncMessage(_,y) | Action::ProposalSync(_,y) | Action::CommitSync(_,y) | Action::NewLeader(_,y) | Action::AckLd(_,y) | Action::UpToDate(_,y) | Action::Proposal(_,y) | Action::Ack(_,y) | Action::Commit(_,y) => {
            channels::facts(s,c,i,y); channels::facts(s,c,j,y); channels::facts(s,c,x,y); assert(receipts::node(s,c,y));
            links::disconnect_ackld(s.nodes[x].ackld,c,y,j); links::disconnect_ackld(s.nodes[y].ackld,c,x,j);
            if a is AckLd { links::update_ackld(s.nodes[x].ackld,y,j); head(s,c,y,x); }
        },_ => {},
    }
    let u=apply(s,c,a);
    if u.election.nodes[i].role == Role::Leading && i != j && links::ackld(u.nodes[i].ackld,j) {
        assert(ready::pair(u,c,i,j)); assert(s.nodes[i].forwarding.contains(j)); assert(s.election.nodes[i].role == Role::Leading); retained(s,c,a,i,j);
    }
}
pub proof fn fresh_sync(s: LState,c: Constants,x: int,y: int,i: int,j: int,m: Message)
    requires channels::safe(s,c),enabled(s,c,Action::Sync(x,y)),c.servers.contains(i),c.servers.contains(j),apply(s,c,Action::Sync(x,y)).msgs[(i,j)].contains(m),!s.msgs[(i,j)].contains(m)
    ensures packet(apply(s,c,Action::Sync(x,y)),i,j,m)
{
    reveal(enabled); reveal(apply);
    let r=choose |r: Electing| #![trigger s.nodes[x].electing.contains(r)] s.nodes[x].electing.contains(r) && r.sid == y && r.zxid != unset() && s.nodes[x].learners.contains(y);
    let n=s.nodes[x]; let e=s.election.nodes[x]; let min=n.snapshot.index+1;
    let max=if n.phase == Phase::Broadcast { n.committed.index } else { e.history.len() as int };
    let lo=if min > max { e.processed.zxid } else { e.history[min-1].zxid };
    let hi=if min > max { e.processed.zxid } else if max == 0 { z::zero() } else { e.history[max-1].zxid };
    if r.zxid == e.processed.zxid { ready::send_origin(s,x,y,r.zxid,e.processed.index,Mode::Diff,i,j,m); }
    else if z::newer(r.zxid,hi) { ready::send_origin(s,x,y,hi,max,Mode::Trunc,i,j,m); }
    else if !z::newer(lo,r.zxid) {
        let k=z::index(e.history,r.zxid);
        if min <= k <= e.history.len() { ready::send_origin(s,x,y,r.zxid,k,Mode::Diff,i,j,m); }
        else { let k=floor_index(e.history,r.zxid); ready::send_origin(s,x,y,if k == 0 { z::zero() } else { e.history[k-1].zxid },k,Mode::Trunc,i,j,m); }
    } else { ready::send_origin(s,x,y,e.processed.zxid,max,Mode::Snap,i,j,m); }
}
pub proof fn fresh_protocol(s: LState,c: Constants,a: Action,i: int,j: int,m: Message)
    requires channels::safe(s,c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),!(a is Sync),
        apply(s,c,a).msgs[(i,j)].contains(m),!s.msgs[(i,j)].contains(m)
    ensures packet(apply(s,c,a),i,j,m)
{
    reveal(enabled); reveal(apply); let x=receiver(a); channel_pair(c,i,j); channels::facts(s,c,i,j); assert(pair(s,i,j)); assert(pair(s,j,i)); assert(node(s,c,i));
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
    assert(ready::cell(u,c,i,j,m));
    if ready::forward(m) { assert(s.nodes[i].forwarding.contains(j)); assert(s.election.nodes[i].role == Role::Leading); retained(s,c,a,i,j); }
    else if m is AckLd || m is Ack { assert(s.nodes[j].forwarding.contains(i)); assert(s.election.nodes[j].role == Role::Leading); retained(s,c,a,j,i); }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires channels::safe(s,c),receipts::safe(s,c),ready::safe(s,c),ready::safe(apply(s,c,a),c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    channels::preserve(s,c,a); let u=apply(s,c,a);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u,c,i) by { preserve_node(s,c,a,i); }
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] pair(u,i,j) by { preserve_pair(s,c,a,i,j); }
    assert forall |i: int,j: int,m: Message| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] cell(u,i,j,m) by {
        if u.msgs[(i,j)].contains(m) {
            assert(ready::cell(u,c,i,j,m));
            if s.msgs[(i,j)].contains(m) {
                assert(cell(s,i,j,m)); assert(ready::cell(s,c,i,j,m));
                if ready::forward(m) { retained(s,c,a,i,j); } else if m is AckLd || m is Ack { retained(s,c,a,j,i); }
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
    else { at(b,c,tick-1); channels::at(b,c,tick-1); receipts::at(b,c,tick-1); ready::at(b,c,tick-1); ready::at(b,c,tick); let a=support::step(b,c,tick-1); preserve(b[tick-1],c,a); }
}
} // verus!
