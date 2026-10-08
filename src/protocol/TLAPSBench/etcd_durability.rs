//! The benchmark's CommittedIsDurable invariant follows from historical completeness.
use vstd::prelude::*;
use super::etcd::*;
use super::etcd_election as election;
use super::etcd_logs as logs;
use super::etcd_order as order;
use super::etcd_prefixes as prefixes;
use super::etcd_commit_history::{self as history,Decision};
use super::etcd_history_trace as trace;
use super::etcd_decision_owners as owners;
use super::etcd_completeness as completeness;
use super::etcd_transmissions as events;
use super::temporal::Behavior;
verus! {
pub proof fn leader_commit_bound(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires election::safety_spec(b,c),time >= 0,c.servers.contains(i),b[time].nodes[i].role == Role::Leader
    ensures b[time].nodes[i].commit <= b[time].nodes[i].log.len()
{
    trace::valid(b,c,time); let g=trace::at(b,c,time); let n=b[time].nodes[i]; assert(history::node(g,i));
    if n.commit > 0 {
        let d=choose |d: Decision| #![trigger g.decisions.contains(d)] g.decisions.contains(d) && d.term <= n.term && d.log.len() >= n.commit;
        trace::decision_log(b,c,time,d); assert(history::decision_valid(g,c,d));
        if d.term < n.term { completeness::historical_completeness(b,c,time,time,i,d); }
        else { prefixes::old_term_prefix(g.logs,c,i,d.log); }
    }
}
pub proof fn preserve(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires election::safety_spec(b,c),time >= 0,c.servers.contains(i),committed_is_durable(b[time],c)
    ensures b[time+1].nodes[i].role == Role::Leader ==> b[time+1].nodes[i].commit <= b[time+1].nodes[i].disk.log.len()
{
    events::step_valid(b,c,time); trace::valid(b,c,time); let g=trace::at(b,c,time); let a=events::step(b,c,time); let s=b[time]; let u=b[time+1];
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    if u.nodes[i].role == Role::Leader {
        if a == Action::BecomeLeader(i) {
            order::candidate_persisted(s,c,i); leader_commit_bound(b,c,time+1,i);
        } else if a == Action::Ready(i) {
            leader_commit_bound(b,c,time,i);
        } else if a == Action::AdvanceCommit(i) {
            assert forall |d: Decision| g.decisions.contains(d) && d.term < s.nodes[i].term implies #[trigger] logs::prefix_of(d.log,s.nodes[i].log) by {
                completeness::historical_completeness(b,c,time,time,i,d);
            }
            owners::advance_durable_if_lower_decisions_retained(g,c,i);
        }
    }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,time: int)
    requires election::safety_spec(b,c),time >= 0
    ensures committed_is_durable(b[time],c)
    decreases time
{
    if time > 0 {
        safety_at(b,c,time-1);
        assert forall |i: int| #![trigger c.servers.contains(i)] c.servers.contains(i) && b[time].nodes[i].role == Role::Leader implies b[time].nodes[i].commit <= b[time].nodes[i].disk.log.len() by {
            preserve(b,c,time-1,i);
        }
    }
}
pub proof fn committed_is_durable_correct(b: Behavior<LState>,c: Constants)
    requires election::safety_spec(b,c)
    ensures forall |time: int| time >= 0 ==> #[trigger] committed_is_durable(b[time],c)
{
    assert forall |time: int| time >= 0 implies #[trigger] committed_is_durable(b[time],c) by { safety_at(b,c,time); }
}
} // verus!
