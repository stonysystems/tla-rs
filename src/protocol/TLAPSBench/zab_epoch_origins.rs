//! Current epochs originate at an active leader and identify one leadership interval.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_epochs as epochs;
use super::zab_phases as phases;
use super::zab_receipts as receipts;
use super::zab_sessions::{self as sessions,interval};
use super::zab_ce_trace as ce;
use super::temporal::Behavior;
verus! {
pub proof fn current_change(s: LState,c: Constants,a: Action,i: int) -> (leader: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),apply(s,c,a).nodes[i].current != s.nodes[i].current
    ensures c.servers.contains(leader),
        (leader == i && apply(s,c,a).nodes[i].role == Role::Leading && apply(s,c,a).nodes[i].phase != Phase::Discovery)
        || (s.nodes[leader].role == Role::Leading && s.nodes[leader].phase != Phase::Discovery && s.nodes[leader].current == apply(s,c,a).nodes[i].current)
{
    // Each Action variant is proved by its own helper lemma below, so
    // `apply` unfolds for one variant per query.
    match a {
        Action::UpdateLeader(..) => current_change_update_leader(s,c,a,i),
        Action::FollowLeader(..) => current_change_follow_leader(s,c,a,i),
        Action::Timeout(..) => current_change_timeout(s,c,a,i),
        Action::Restart(..) => current_change_restart(s,c,a,i),
        Action::Connect(..) => current_change_connect(s,c,a,i),
        Action::CEpoch(..) => current_change_c_epoch(s,c,a,i),
        Action::NewEpoch(..) => current_change_new_epoch(s,c,a,i),
        Action::AckEpoch(..) => current_change_ack_epoch(s,c,a,i),
        Action::NewLeader(..) => current_change_new_leader(s,c,a,i),
        Action::AckLd(..) => current_change_ack_ld(s,c,a,i),
        Action::CommitLd(..) => current_change_commit_ld(s,c,a,i),
        Action::Request(..) => current_change_request(s,c,a,i),
        Action::Broadcast(..) => current_change_broadcast(s,c,a,i),
        Action::Propose(..) => current_change_propose(s,c,a,i),
        Action::Ack(..) => current_change_ack(s,c,a,i),
        Action::Commit(..) => current_change_commit(s,c,a,i),
        Action::Stutter => current_change_stutter(s,c,a,i),
    }
}
#[verifier::spinoff_prover]
proof fn current_change_update_leader(s: LState,c: Constants,a: Action,i: int) -> (leader: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),apply(s,c,a).nodes[i].current != s.nodes[i].current,
        a is UpdateLeader
    ensures c.servers.contains(leader),
        (leader == i && apply(s,c,a).nodes[i].role == Role::Leading && apply(s,c,a).nodes[i].phase != Phase::Discovery)
        || (s.nodes[leader].role == Role::Leading && s.nodes[leader].phase != Phase::Discovery && s.nodes[leader].current == apply(s,c,a).nodes[i].current)
{
    hide(update_ack);
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,i);
    match a {
        Action::NewLeader(x,y) => { receipts::facts(s,c,x,y); assert(x == i); y },
        _ => { assert(exists |j: int| a == Action::AckEpoch(i,j)); i },
    }
}
#[verifier::spinoff_prover]
proof fn current_change_follow_leader(s: LState,c: Constants,a: Action,i: int) -> (leader: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),apply(s,c,a).nodes[i].current != s.nodes[i].current,
        a is FollowLeader
    ensures c.servers.contains(leader),
        (leader == i && apply(s,c,a).nodes[i].role == Role::Leading && apply(s,c,a).nodes[i].phase != Phase::Discovery)
        || (s.nodes[leader].role == Role::Leading && s.nodes[leader].phase != Phase::Discovery && s.nodes[leader].current == apply(s,c,a).nodes[i].current)
{
    hide(update_ack);
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,i);
    match a {
        Action::NewLeader(x,y) => { receipts::facts(s,c,x,y); assert(x == i); y },
        _ => { assert(exists |j: int| a == Action::AckEpoch(i,j)); i },
    }
}
#[verifier::spinoff_prover]
proof fn current_change_timeout(s: LState,c: Constants,a: Action,i: int) -> (leader: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),apply(s,c,a).nodes[i].current != s.nodes[i].current,
        a is Timeout
    ensures c.servers.contains(leader),
        (leader == i && apply(s,c,a).nodes[i].role == Role::Leading && apply(s,c,a).nodes[i].phase != Phase::Discovery)
        || (s.nodes[leader].role == Role::Leading && s.nodes[leader].phase != Phase::Discovery && s.nodes[leader].current == apply(s,c,a).nodes[i].current)
{
    hide(update_ack);
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,i);
    match a {
        Action::NewLeader(x,y) => { receipts::facts(s,c,x,y); assert(x == i); y },
        _ => { assert(exists |j: int| a == Action::AckEpoch(i,j)); i },
    }
}
#[verifier::spinoff_prover]
proof fn current_change_restart(s: LState,c: Constants,a: Action,i: int) -> (leader: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),apply(s,c,a).nodes[i].current != s.nodes[i].current,
        a is Restart
    ensures c.servers.contains(leader),
        (leader == i && apply(s,c,a).nodes[i].role == Role::Leading && apply(s,c,a).nodes[i].phase != Phase::Discovery)
        || (s.nodes[leader].role == Role::Leading && s.nodes[leader].phase != Phase::Discovery && s.nodes[leader].current == apply(s,c,a).nodes[i].current)
{
    hide(update_ack);
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,i);
    match a {
        Action::NewLeader(x,y) => { receipts::facts(s,c,x,y); assert(x == i); y },
        _ => { assert(exists |j: int| a == Action::AckEpoch(i,j)); i },
    }
}
#[verifier::spinoff_prover]
proof fn current_change_connect(s: LState,c: Constants,a: Action,i: int) -> (leader: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),apply(s,c,a).nodes[i].current != s.nodes[i].current,
        a is Connect
    ensures c.servers.contains(leader),
        (leader == i && apply(s,c,a).nodes[i].role == Role::Leading && apply(s,c,a).nodes[i].phase != Phase::Discovery)
        || (s.nodes[leader].role == Role::Leading && s.nodes[leader].phase != Phase::Discovery && s.nodes[leader].current == apply(s,c,a).nodes[i].current)
{
    hide(update_ack);
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,i);
    match a {
        Action::NewLeader(x,y) => { receipts::facts(s,c,x,y); assert(x == i); y },
        _ => { assert(exists |j: int| a == Action::AckEpoch(i,j)); i },
    }
}
#[verifier::spinoff_prover]
proof fn current_change_c_epoch(s: LState,c: Constants,a: Action,i: int) -> (leader: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),apply(s,c,a).nodes[i].current != s.nodes[i].current,
        a is CEpoch
    ensures c.servers.contains(leader),
        (leader == i && apply(s,c,a).nodes[i].role == Role::Leading && apply(s,c,a).nodes[i].phase != Phase::Discovery)
        || (s.nodes[leader].role == Role::Leading && s.nodes[leader].phase != Phase::Discovery && s.nodes[leader].current == apply(s,c,a).nodes[i].current)
{
    hide(update_ack);
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,i);
    match a {
        Action::NewLeader(x,y) => { receipts::facts(s,c,x,y); assert(x == i); y },
        _ => { assert(exists |j: int| a == Action::AckEpoch(i,j)); i },
    }
}
#[verifier::spinoff_prover]
proof fn current_change_new_epoch(s: LState,c: Constants,a: Action,i: int) -> (leader: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),apply(s,c,a).nodes[i].current != s.nodes[i].current,
        a is NewEpoch
    ensures c.servers.contains(leader),
        (leader == i && apply(s,c,a).nodes[i].role == Role::Leading && apply(s,c,a).nodes[i].phase != Phase::Discovery)
        || (s.nodes[leader].role == Role::Leading && s.nodes[leader].phase != Phase::Discovery && s.nodes[leader].current == apply(s,c,a).nodes[i].current)
{
    hide(update_ack);
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,i);
    match a {
        Action::NewLeader(x,y) => { receipts::facts(s,c,x,y); assert(x == i); y },
        _ => { assert(exists |j: int| a == Action::AckEpoch(i,j)); i },
    }
}
#[verifier::spinoff_prover]
proof fn current_change_ack_epoch(s: LState,c: Constants,a: Action,i: int) -> (leader: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),apply(s,c,a).nodes[i].current != s.nodes[i].current,
        a is AckEpoch
    ensures c.servers.contains(leader),
        (leader == i && apply(s,c,a).nodes[i].role == Role::Leading && apply(s,c,a).nodes[i].phase != Phase::Discovery)
        || (s.nodes[leader].role == Role::Leading && s.nodes[leader].phase != Phase::Discovery && s.nodes[leader].current == apply(s,c,a).nodes[i].current)
{
    hide(update_ack);
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,i);
    match a {
        Action::NewLeader(x,y) => { receipts::facts(s,c,x,y); assert(x == i); y },
        _ => { assert(exists |j: int| a == Action::AckEpoch(i,j)); i },
    }
}
#[verifier::spinoff_prover]
proof fn current_change_new_leader(s: LState,c: Constants,a: Action,i: int) -> (leader: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),apply(s,c,a).nodes[i].current != s.nodes[i].current,
        a is NewLeader
    ensures c.servers.contains(leader),
        (leader == i && apply(s,c,a).nodes[i].role == Role::Leading && apply(s,c,a).nodes[i].phase != Phase::Discovery)
        || (s.nodes[leader].role == Role::Leading && s.nodes[leader].phase != Phase::Discovery && s.nodes[leader].current == apply(s,c,a).nodes[i].current)
{
    hide(update_ack);
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,i);
    match a {
        Action::NewLeader(x,y) => { receipts::facts(s,c,x,y); assert(x == i); y },
        _ => { assert(exists |j: int| a == Action::AckEpoch(i,j)); i },
    }
}
#[verifier::spinoff_prover]
proof fn current_change_ack_ld(s: LState,c: Constants,a: Action,i: int) -> (leader: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),apply(s,c,a).nodes[i].current != s.nodes[i].current,
        a is AckLd
    ensures c.servers.contains(leader),
        (leader == i && apply(s,c,a).nodes[i].role == Role::Leading && apply(s,c,a).nodes[i].phase != Phase::Discovery)
        || (s.nodes[leader].role == Role::Leading && s.nodes[leader].phase != Phase::Discovery && s.nodes[leader].current == apply(s,c,a).nodes[i].current)
{
    hide(update_ack);
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,i);
    match a {
        Action::NewLeader(x,y) => { receipts::facts(s,c,x,y); assert(x == i); y },
        _ => { assert(exists |j: int| a == Action::AckEpoch(i,j)); i },
    }
}
#[verifier::spinoff_prover]
proof fn current_change_commit_ld(s: LState,c: Constants,a: Action,i: int) -> (leader: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),apply(s,c,a).nodes[i].current != s.nodes[i].current,
        a is CommitLd
    ensures c.servers.contains(leader),
        (leader == i && apply(s,c,a).nodes[i].role == Role::Leading && apply(s,c,a).nodes[i].phase != Phase::Discovery)
        || (s.nodes[leader].role == Role::Leading && s.nodes[leader].phase != Phase::Discovery && s.nodes[leader].current == apply(s,c,a).nodes[i].current)
{
    hide(update_ack);
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,i);
    match a {
        Action::NewLeader(x,y) => { receipts::facts(s,c,x,y); assert(x == i); y },
        _ => { assert(exists |j: int| a == Action::AckEpoch(i,j)); i },
    }
}
#[verifier::spinoff_prover]
proof fn current_change_request(s: LState,c: Constants,a: Action,i: int) -> (leader: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),apply(s,c,a).nodes[i].current != s.nodes[i].current,
        a is Request
    ensures c.servers.contains(leader),
        (leader == i && apply(s,c,a).nodes[i].role == Role::Leading && apply(s,c,a).nodes[i].phase != Phase::Discovery)
        || (s.nodes[leader].role == Role::Leading && s.nodes[leader].phase != Phase::Discovery && s.nodes[leader].current == apply(s,c,a).nodes[i].current)
{
    hide(update_ack);
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,i);
    match a {
        Action::NewLeader(x,y) => { receipts::facts(s,c,x,y); assert(x == i); y },
        _ => { assert(exists |j: int| a == Action::AckEpoch(i,j)); i },
    }
}
#[verifier::spinoff_prover]
proof fn current_change_broadcast(s: LState,c: Constants,a: Action,i: int) -> (leader: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),apply(s,c,a).nodes[i].current != s.nodes[i].current,
        a is Broadcast
    ensures c.servers.contains(leader),
        (leader == i && apply(s,c,a).nodes[i].role == Role::Leading && apply(s,c,a).nodes[i].phase != Phase::Discovery)
        || (s.nodes[leader].role == Role::Leading && s.nodes[leader].phase != Phase::Discovery && s.nodes[leader].current == apply(s,c,a).nodes[i].current)
{
    hide(update_ack);
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,i);
    match a {
        Action::NewLeader(x,y) => { receipts::facts(s,c,x,y); assert(x == i); y },
        _ => { assert(exists |j: int| a == Action::AckEpoch(i,j)); i },
    }
}
#[verifier::spinoff_prover]
proof fn current_change_propose(s: LState,c: Constants,a: Action,i: int) -> (leader: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),apply(s,c,a).nodes[i].current != s.nodes[i].current,
        a is Propose
    ensures c.servers.contains(leader),
        (leader == i && apply(s,c,a).nodes[i].role == Role::Leading && apply(s,c,a).nodes[i].phase != Phase::Discovery)
        || (s.nodes[leader].role == Role::Leading && s.nodes[leader].phase != Phase::Discovery && s.nodes[leader].current == apply(s,c,a).nodes[i].current)
{
    hide(update_ack);
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,i);
    match a {
        Action::NewLeader(x,y) => { receipts::facts(s,c,x,y); assert(x == i); y },
        _ => { assert(exists |j: int| a == Action::AckEpoch(i,j)); i },
    }
}
#[verifier::spinoff_prover]
proof fn current_change_ack(s: LState,c: Constants,a: Action,i: int) -> (leader: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),apply(s,c,a).nodes[i].current != s.nodes[i].current,
        a is Ack
    ensures c.servers.contains(leader),
        (leader == i && apply(s,c,a).nodes[i].role == Role::Leading && apply(s,c,a).nodes[i].phase != Phase::Discovery)
        || (s.nodes[leader].role == Role::Leading && s.nodes[leader].phase != Phase::Discovery && s.nodes[leader].current == apply(s,c,a).nodes[i].current)
{
    hide(update_ack);
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,i);
    match a {
        Action::NewLeader(x,y) => { receipts::facts(s,c,x,y); assert(x == i); y },
        _ => { assert(exists |j: int| a == Action::AckEpoch(i,j)); i },
    }
}
#[verifier::spinoff_prover]
proof fn current_change_commit(s: LState,c: Constants,a: Action,i: int) -> (leader: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),apply(s,c,a).nodes[i].current != s.nodes[i].current,
        a is Commit
    ensures c.servers.contains(leader),
        (leader == i && apply(s,c,a).nodes[i].role == Role::Leading && apply(s,c,a).nodes[i].phase != Phase::Discovery)
        || (s.nodes[leader].role == Role::Leading && s.nodes[leader].phase != Phase::Discovery && s.nodes[leader].current == apply(s,c,a).nodes[i].current)
{
    hide(update_ack);
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,i);
    match a {
        Action::NewLeader(x,y) => { receipts::facts(s,c,x,y); assert(x == i); y },
        _ => { assert(exists |j: int| a == Action::AckEpoch(i,j)); i },
    }
}
#[verifier::spinoff_prover]
proof fn current_change_stutter(s: LState,c: Constants,a: Action,i: int) -> (leader: int)
    requires receipts::inductive(s,c),enabled(s,c,a),c.servers.contains(i),apply(s,c,a).nodes[i].current != s.nodes[i].current,
        a is Stutter
    ensures c.servers.contains(leader),
        (leader == i && apply(s,c,a).nodes[i].role == Role::Leading && apply(s,c,a).nodes[i].phase != Phase::Discovery)
        || (s.nodes[leader].role == Role::Leading && s.nodes[leader].phase != Phase::Discovery && s.nodes[leader].current == apply(s,c,a).nodes[i].current)
{
    hide(update_ack);
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,i);
    match a {
        Action::NewLeader(x,y) => { receipts::facts(s,c,x,y); assert(x == i); y },
        _ => { assert(exists |j: int| a == Action::AckEpoch(i,j)); i },
    }
}
pub proof fn current_origin(b: Behavior<LState>,c: Constants,time: int,i: int) -> (w: (int,int))
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),b[time].nodes[i].current > 0
    ensures 0 <= w.0 <= time,c.servers.contains(w.1),b[w.0].nodes[w.1].role == Role::Leading,
        b[w.0].nodes[w.1].phase != Phase::Discovery,b[w.0].nodes[w.1].current == b[time].nodes[i].current
    decreases time
{
    if time == 0 { assert(false); (0,i) }
    else {
        let prev=time-1; let a=sessions::step(b,c,prev);
        if b[time].nodes[i].current == b[prev].nodes[i].current { current_origin(b,c,prev,i) }
        else {
            let leader=current_change(b[prev],c,a,i);
            if leader == i && b[time].nodes[i].role == Role::Leading && b[time].nodes[i].phase != Phase::Discovery { (time,i) }
            else { (prev,leader) }
        }
    }
}
pub proof fn same_session(b: Behavior<LState>,c: Constants,i: int,left: int,right: int)
    requires connections::safety_spec(b,c),c.servers.contains(i),0 <= left <= right,
        b[left].nodes[i].role == Role::Leading,b[right].nodes[i].role == Role::Leading,
        b[left].nodes[i].phase != Phase::Discovery,b[right].nodes[i].phase != Phase::Discovery,
        b[left].nodes[i].current == b[right].nodes[i].current
    ensures interval(b,i,left,right)
{
    phases::at(b,c,left); phases::at(b,c,right); phases::facts(b[left],c,i,i); phases::facts(b[right],c,i,i);
    let since=sessions::start(b,c,right,i);
    if since > left {
        let at=ce::proposal(b,c,since,right,i);
        epochs::at(b,c,at); epochs::facts(b[at],c,i,i);
        let r=choose |r: CE| #![trigger b[at].nodes[i].ce.contains(r)] b[at].nodes[i].ce.contains(r) && r.sid == i && r.connected && r.epoch <= b[at].nodes[i].accepted
            && (!quorum(ce_ids(b[at].nodes[i].ce),c) ==> r.epoch == b[at].nodes[i].accepted);
        assert(r.epoch < b[right].nodes[i].accepted);
        assert(ce::payload(b[at].nodes[i].ce,i,r.epoch));
        let read=ce::receipt_origin(b,c,since,at,i,i,r.epoch);
        epochs::monotone(b,c,left,read,i); assert(false);
    }
}
} // verus!
