//! Induction over current epochs preserves prefixes certified by earlier quorums.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_collections as collections;
use super::zab_epochs as epochs;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_leader_logs as leader;
use super::zab_entry_origins::through;
use super::zab_epoch_retention as retention;
use super::zab_activation_logs as activation;
use super::zab_discovery_logs as discovery;
use super::zab_history_compare as compare;
use super::zab_ack_certificates as acks;
use super::zab_commit_certificates::certified;
use super::zab_sessions as sessions;
use super::temporal::Behavior;
verus! {
pub open spec fn lower(b: Behavior<LState>,c: Constants,e: int,h: Seq<Txn>,k: int,epoch: int) -> bool {
    forall |time: int,i: int| time >= 0 && c.servers.contains(i) && e < b[time].nodes[i].current < epoch
        ==> #[trigger] through(h,b[time].nodes[i].history,k)
}
pub open spec fn node(n: LServer,epoch: int,h: Seq<Txn>,k: int) -> bool { n.current == epoch ==> through(h,n.history,k) }
pub open spec fn packet(m: Message,epoch: int,h: Seq<Txn>,k: int) -> bool {
    match m { Message::NewLeader(e,copy) => e == epoch ==> through(h,copy,k),_ => true }
}
pub open spec fn inductive(b: Behavior<LState>,c: Constants,time: int,epoch: int,h: Seq<Txn>,k: int) -> bool {
    (forall |i: int| c.servers.contains(i) ==> #[trigger] node(b[time].nodes[i],epoch,h,k))
    && (forall |i: int,j: int,p: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= p < b[time].msgs[(i,j)].len()
        ==> #[trigger] packet(b[time].msgs[(i,j)][p],epoch,h,k))
}
pub proof fn selected(b: Behavior<LState>,c: Constants,until: int,e: int,h: Seq<Txn>,k: int,time: int,i: int)
    requires connections::safety_spec(b,c),until >= 0,certified(b,c,until,e,h,k),e > 0,time >= 0,c.servers.contains(i),
        b[time].nodes[i].role == Role::Leading,b[time].nodes[i].phase == Phase::Discovery,
        b[time+1].nodes[i].role == Role::Leading,b[time+1].nodes[i].phase != Phase::Discovery,
        b[time+1].nodes[i].current > e,lower(b,c,e,h,k,b[time+1].nodes[i].current)
    ensures through(h,b[time+1].nodes[i].history,k)
{
    activation::activation_step(b,c,time,i); logs::at(b,c,time+1); let u=b[time+1]; logs::facts(u,c,i,i);
    let epoch=u.nodes[i].current; let reports=u.nodes[i].ae;
    let owner=choose |owner: int| c.servers.contains(owner) && exists |q: Set<int>| quorum(q,c)
        && forall |j: int| #![trigger q.contains(j)] q.contains(j) ==> acks::certificate(b,c,until,owner,e,h,k,j);
    let q=choose |q: Set<int>| quorum(q,c) && forall |j: int| #![trigger q.contains(j)] q.contains(j) ==> acks::certificate(b,c,until,owner,e,h,k,j);
    let voter=collections::intersect_quorums(q,ae_ids(reports),c);
    let r=choose |r: AE| #![trigger reports.contains(r)] reports.contains(r) && r.sid == voter;
    let report=discovery::report_witness(b,c,time,i,r);
    assert(acks::certificate(b,c,until,owner,e,h,k,voter));
    let stored=choose |stored: int| acks::witness(b,until,owner,e,h,k,voter,stored);
    if stored >= report { epochs::monotone(b,c,report,stored,voter); assert(false); }
    epochs::monotone(b,c,stored,report,voter); assert(r.epoch >= e);
    let chosen=collections::selected_maximal(reports); let chosen_report=discovery::report_witness(b,c,time,i,chosen);
    leader::fresh_activation(b,c,time,i,chosen_report,chosen.sid);
    assert(chosen.epoch < epoch && chosen.epoch >= r.epoch);
    if chosen.epoch > e { assert(through(h,b[chosen_report].nodes[chosen.sid].history,k)); }
    else {
        assert(chosen.epoch == e && r.epoch == e);
        retention::between(b,c,stored,report,voter); compare::extend(h,b[stored].nodes[voter].history,r.history,k);
        compare::reports(b,c,report,voter,chosen_report,chosen.sid); compare::extend(h,r.history,chosen.history,k);
    }
    math::ack_contents(chosen.history,i,zero()); compare::extend(h,chosen.history,u.nodes[i].history,k);
}
pub proof fn initial_inductive(b: Behavior<LState>,c: Constants,epoch: int,h: Seq<Txn>,k: int)
    requires connections::safety_spec(b,c),epoch > 0
    ensures inductive(b,c,0,epoch,h,k)
{
    assert forall |i: int,j: int,p: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= p < b[0].msgs[(i,j)].len()
        implies #[trigger] packet(b[0].msgs[(i,j)][p],epoch,h,k) by { connections::channel_pair(c,i,j); }
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn preserve_node(b: Behavior<LState>,c: Constants,until: int,e: int,h: Seq<Txn>,k: int,epoch: int,time: int,i: int)
    requires connections::safety_spec(b,c),until >= 0,certified(b,c,until,e,h,k),0 < e < epoch,lower(b,c,e,h,k,epoch),
        time >= 0,c.servers.contains(i),inductive(b,c,time,epoch,h,k)
    ensures node(b[time+1].nodes[i],epoch,h,k)
{
    hide(update_ack);
    let a=sessions::step(b,c,time); let s=b[time]; let u=b[time+1]; logs::at(b,c,time); logs::preserve(s,c,a);
    logs::facts(s,c,i,i); logs::facts(u,c,i,i); assert(node(s.nodes[i],epoch,h,k));
    if u.nodes[i].current == epoch {
        if s.nodes[i].current == epoch {
            retention::step(b,c,time,i); compare::extend(h,s.nodes[i].history,u.nodes[i].history,k);
        } else {
            reveal(enabled); reveal(apply);
            match a {
                Action::AckEpoch(x,y) => {
                    logs::facts(s,c,x,y); assert(x == i); assert(s.nodes[i].phase == Phase::Discovery);
                    selected(b,c,until,e,h,k,time,i);
                },
                Action::NewLeader(x,y) => {
                    logs::facts(s,c,x,y); assert(x == i); assert(packet(s.msgs[(y,x)][0],epoch,h,k));
                },
                _ => { assert(false); },
            }
        }
    }
}
pub proof fn preserve_packet(b: Behavior<LState>,c: Constants,until: int,e: int,h: Seq<Txn>,k: int,epoch: int,time: int,i: int,j: int,p: int)
    requires connections::safety_spec(b,c),until >= 0,certified(b,c,until,e,h,k),0 < e < epoch,lower(b,c,e,h,k,epoch),
        time >= 0,c.servers.contains(i),c.servers.contains(j),inductive(b,c,time,epoch,h,k),0 <= p < b[time+1].msgs[(i,j)].len()
    ensures packet(b[time+1].msgs[(i,j)][p],epoch,h,k)
{
    hide(update_ack);
    let a=sessions::step(b,c,time); let s=b[time]; let u=b[time+1]; logs::at(b,c,time);
    logs::facts(s,c,i,j); connections::channel_pair(c,i,j); reveal(enabled); reveal(apply);
    if let Action::AckEpoch(x,y)=a {
        logs::facts(s,c,x,y); preserve_node(b,c,until,e,h,k,epoch,time,x); logs::preserve(s,c,a); logs::facts(u,c,x,y);
    }
    if p < s.msgs[(i,j)].len() { assert(packet(s.msgs[(i,j)][p],epoch,h,k)); }
    if p+1 < s.msgs[(i,j)].len() { assert(packet(s.msgs[(i,j)][p+1],epoch,h,k)); }
}
pub proof fn at(b: Behavior<LState>,c: Constants,until: int,e: int,h: Seq<Txn>,k: int,epoch: int,time: int)
    requires connections::safety_spec(b,c),until >= 0,certified(b,c,until,e,h,k),0 < e < epoch,lower(b,c,e,h,k,epoch),time >= 0
    ensures inductive(b,c,time,epoch,h,k)
    decreases time
{
    if time == 0 { initial_inductive(b,c,epoch,h,k); }
    else {
        let prev=time-1; at(b,c,until,e,h,k,epoch,prev);
        assert forall |i: int| c.servers.contains(i) implies #[trigger] node(b[time].nodes[i],epoch,h,k) by { preserve_node(b,c,until,e,h,k,epoch,prev,i); }
        assert forall |i: int,j: int,p: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= p < b[time].msgs[(i,j)].len()
            implies #[trigger] packet(b[time].msgs[(i,j)][p],epoch,h,k) by { preserve_packet(b,c,until,e,h,k,epoch,prev,i,j,p); }
    }
}
pub proof fn higher_epoch(b: Behavior<LState>,c: Constants,until: int,e: int,h: Seq<Txn>,k: int,epoch: int)
    requires connections::safety_spec(b,c),until >= 0,certified(b,c,until,e,h,k),0 < e < epoch
    ensures forall |time: int,i: int| time >= 0 && c.servers.contains(i) && b[time].nodes[i].current == epoch
        ==> #[trigger] through(h,b[time].nodes[i].history,k)
    decreases epoch
{
    assert forall |time: int,i: int| time >= 0 && c.servers.contains(i) && e < b[time].nodes[i].current < epoch
        implies #[trigger] through(h,b[time].nodes[i].history,k) by {
        higher_epoch(b,c,until,e,h,k,b[time].nodes[i].current);
    }
    assert(lower(b,c,e,h,k,epoch));
    assert forall |time: int,i: int| time >= 0 && c.servers.contains(i) && b[time].nodes[i].current == epoch
        implies #[trigger] through(h,b[time].nodes[i].history,k) by { at(b,c,until,e,h,k,epoch,time); assert(node(b[time].nodes[i],epoch,h,k)); }
}
} // verus!
