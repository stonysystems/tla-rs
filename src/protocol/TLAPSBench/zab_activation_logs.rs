//! The selected history at activation contains only transactions from earlier epochs.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_collections as collections;
use super::zab_logs as logs;
use super::zab_log_math as math;
use super::zab_leader_logs as leader;
use super::zab_history_trace as history;
use super::zab_sessions as sessions;
use super::temporal::Behavior;
verus! {
pub proof fn activation_step(b: Behavior<LState>,c: Constants,time: int,i: int) -> (j: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),
        b[time].nodes[i].role == Role::Leading,b[time].nodes[i].phase == Phase::Discovery,
        b[time+1].nodes[i].role == Role::Leading,b[time+1].nodes[i].phase != Phase::Discovery
    ensures c.servers.contains(j),enabled(b[time],c,Action::AckEpoch(i,j)),b[time+1] == apply(b[time],c,Action::AckEpoch(i,j)),
        !quorum(ae_ids(b[time].nodes[i].ae),c),quorum(ae_ids(b[time+1].nodes[i].ae),c),
        b[time+1].nodes[i].history == init_ack(select_history(b[time+1].nodes[i].ae),i)
{
    let a=sessions::step(b,c,time); let s=b[time]; logs::at(b,c,time); logs::facts(s,c,i,i);
    reveal(enabled); reveal(apply);
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            logs::facts(s,c,x,y); logs::facts(s,c,i,x); logs::facts(s,c,i,y);
        },
        _ => {},
    }
    assert(exists |j: int| a == Action::AckEpoch(i,j));
    choose |j: int| a == Action::AckEpoch(i,j)
}
pub proof fn earlier_history(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),
        b[time].nodes[i].role == Role::Leading,b[time].nodes[i].phase == Phase::Discovery,
        b[time+1].nodes[i].role == Role::Leading,b[time+1].nodes[i].phase != Phase::Discovery
    ensures math::bounded(b[time+1].nodes[i].history,b[time+1].nodes[i].current-1)
{
    let j=activation_step(b,c,time,i); let s=b[time+1]; logs::at(b,c,time+1); logs::facts(s,c,i,i);
    let since=sessions::start(b,c,time+1,i); assert(since <= time);
    let q=s.nodes[i].ae; assert(!q.is_empty()); let r=collections::selected_origin(q);
    assert(ae_ids(q).contains(r.sid)); assert(c.servers.contains(r.sid)); assert(history::payload(q,r.sid,r.epoch,r.history));
    let read=history::receipt_origin(b,c,since,time+1,i,r.sid,r.epoch,r.history);
    leader::fresh_activation(b,c,time,i,read,r.sid);
    assert(r.epoch < s.nodes[i].current); assert(math::shape(r.history) && math::bounded(r.history,r.epoch));
    math::ack_contents(r.history,i,zero()); math::transfer(r.history,s.nodes[i].history,r.epoch);
    assert forall |k: int| 0 <= k < s.nodes[i].history.len() implies (#[trigger] s.nodes[i].history[k]).zxid.epoch <= s.nodes[i].current-1 by {
        assert(s.nodes[i].history[k].zxid.epoch <= r.epoch);
    }
}
} // verus!
