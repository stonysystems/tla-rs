//! Quorum intersection orders completed elections by leadership-interval start.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_collections as collections;
use super::zab_epochs as epochs;
use super::zab_phases as phases;
use super::zab_sessions::{self as sessions,interval};
use super::zab_ce_trace as ce;
use super::zab_ae_trace as ae;
use super::temporal::Behavior;
verus! {
pub proof fn ordered_sessions(b: Behavior<LState>,c: Constants,si: int,ti: int,i: int,sj: int,tj: int,j: int)
    requires connections::safety_spec(b,c),c.servers.contains(i),c.servers.contains(j),i != j,c.servers.len() > 1,
        0 < si < sj,interval(b,i,si,ti),interval(b,j,sj,tj),b[si-1].nodes[i].role != Role::Leading,b[sj-1].nodes[j].role != Role::Leading,
        quorum(ae_ids(b[ti].nodes[i].ae),c),quorum(ae_ids(b[tj].nodes[j].ae),c)
    ensures b[ti].nodes[i].accepted < b[tj].nodes[j].accepted
{
    phases::at(b,c,tj); phases::facts(b[tj],c,j,j);
    let proposal=ce::proposal(b,c,sj,tj,j);
    let voter=collections::intersect_quorums(ae_ids(b[ti].nodes[i].ae),ce_ids(b[proposal].nodes[j].ce),c);
    let r=choose |r: CE| b[proposal].nodes[j].ce.contains(r) && r.sid == voter;
    assert(r.epoch < b[tj].nodes[j].accepted); assert(ce::payload(b[proposal].nodes[j].ce,voter,r.epoch));
    let read=ce::receipt_origin(b,c,sj,proposal,j,voter,r.epoch);
    let accepted=ae::accepted_witness(b,c,si,ti,i,voter);
    if accepted >= read {
        sessions::start_state(b,c,sj,j);
        sessions::shrink(b,c,i,sj,read); sessions::shrink(b,c,i,read,accepted);
        assert(b[read].nodes[i].learners.contains(voter));
        connections::at(b,c,read); sessions::disjoint_learners(b[read],c,i,j,voter); assert(false);
    } else { epochs::monotone(b,c,accepted,read,voter); }
}
pub proof fn unique(b: Behavior<LState>,c: Constants,ti: int,i: int,tj: int,j: int)
    requires connections::safety_spec(b,c),ti >= 0,tj >= 0,c.servers.contains(i),c.servers.contains(j),
        b[ti].nodes[i].role == Role::Leading,b[tj].nodes[j].role == Role::Leading,
        b[ti].nodes[i].phase != Phase::Discovery,b[tj].nodes[j].phase != Phase::Discovery,
        b[ti].nodes[i].current == b[tj].nodes[j].current
    ensures i == j
{
    if i != j {
        phases::at(b,c,ti); phases::at(b,c,tj); phases::facts(b[ti],c,i,j); phases::facts(b[tj],c,i,j);
        let si=sessions::start(b,c,ti,i); let sj=sessions::start(b,c,tj,j);
        if si == sj { sessions::start_state(b,c,si,i); sessions::start_state(b,c,sj,j); assert(false); }
        else if si < sj { ordered_sessions(b,c,si,ti,i,sj,tj,j); }
        else { ordered_sessions(b,c,sj,tj,j,si,ti,i); }
    }
}
pub proof fn leadership1_at(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0
    ensures leadership1(b[time],c)
{
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) && b[time].nodes[i].role == Role::Leading && b[time].nodes[j].role == Role::Leading
        && (b[time].nodes[i].phase == Phase::Synchronization || b[time].nodes[i].phase == Phase::Broadcast)
        && (b[time].nodes[j].phase == Phase::Synchronization || b[time].nodes[j].phase == Phase::Broadcast)
        && b[time].nodes[i].current == b[time].nodes[j].current implies i == j by { unique(b,c,time,i,time,j); }
}
pub proof fn history_domain(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0
    ensures b[time].epoch_leader.dom() == Set::range(1,c.max_epoch+1)
    decreases time
{
    if time > 0 {
        let prev=time-1; history_domain(b,c,prev); let a=sessions::step(b,c,prev);
        reveal(apply); assert(b[time].epoch_leader.dom() =~= b[prev].epoch_leader.dom());
    }
}
pub proof fn recorded(b: Behavior<LState>,c: Constants,time: int,e: int,i: int) -> (at: int)
    requires connections::safety_spec(b,c),time >= 0,1 <= e <= c.max_epoch,b[time].epoch_leader[e].contains(i)
    ensures 0 <= at <= time,c.servers.contains(i),b[at].nodes[i].role == Role::Leading,b[at].nodes[i].phase == Phase::Synchronization,b[at].nodes[i].current == e
    decreases time
{
    if time == 0 { assert(false); 0 }
    else {
        let prev=time-1; history_domain(b,c,prev); let a=sessions::step(b,c,prev);
        if b[prev].epoch_leader[e].contains(i) { recorded(b,c,prev,e,i) }
        else {
            reveal(apply); reveal(enabled);
            assert(exists |j: int| a == Action::AckEpoch(i,j));
            time
        }
    }
}
pub proof fn leadership2_at(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0
    ensures leadership2(b[time],c)
{
    assert forall |e: int| 1 <= e <= c.max_epoch implies (#[trigger] b[time].epoch_leader[e]).len() <= 1 by {
        let q=b[time].epoch_leader[e];
        if !q.is_empty() {
            let i=choose |i: int| q.contains(i); let ti=recorded(b,c,time,e,i);
            assert(q.subset_of(set![i])) by {
                assert forall |j: int| q.contains(j) implies j == i by { let tj=recorded(b,c,time,e,j); unique(b,c,ti,i,tj,j); }
            }
            vstd::set_lib::lemma_len_subset(q,set![i]);
        }
    }
}
pub proof fn benchmark_leadership(b: Behavior<LState>,c: Constants)
    requires connections::safety_spec(b,c)
    ensures forall |time: int| time >= 0 ==> #[trigger] leadership1(b[time],c),
        forall |time: int| time >= 0 ==> #[trigger] leadership2(b[time],c)
{
    assert forall |time: int| time >= 0 implies #[trigger] leadership1(b[time],c) by { leadership1_at(b,c,time); }
    assert forall |time: int| time >= 0 implies #[trigger] leadership2(b[time],c) by { leadership2_at(b,c,time); }
}
} // verus!
