//! A prefix of a direct decision survives after it has been acknowledged.
use vstd::prelude::*;
use super::etcd::*;
use super::etcd_election as election;
use super::etcd_logs as logs;
use super::etcd_origins as origins;
use super::etcd_transmissions as events;
use super::etcd_commit_history::{self as history,Decision};
use super::etcd_history_trace as trace;
use super::etcd_leader_trace as leaders;
use super::etcd_election_prefixes as packets;
use super::etcd_completeness as completeness;
use super::etcd_retention as retention;
use super::etcd_ack_prefixes as acks;
use super::temporal::Behavior;
verus! {
pub proof fn packet_compatible(b: Behavior<LState>,c: Constants,horizon: int,time: int,d: Decision,m: Message)
    requires election::safety_spec(b,c),0 <= time <= horizon,trace::at(b,c,horizon).decisions.contains(d),
        b[time].messages.count(m) > 0,m.body is AppendRequest,d.term <= m.term
    ensures retention::packet(d.log,m)
{
    if m.term == d.term { packets::same_term_packet(b,c,horizon,time,d,m); }
    else {
        let create=leaders::request_origin(b,c,time,m);
        completeness::historical_completeness(b,c,horizon,create,m.source,d);
        assert(logs::segment(m,b[create].nodes[m.source].log) && retention::compatible(d.log,b[create].nodes[m.source].log));
    }
}
pub proof fn smaller_packet(h: Seq<nat>,d: Seq<nat>,m: Message)
    requires logs::prefix_of(h,d),retention::packet(d,m)
    ensures retention::packet(h,m)
{
    let v=choose |v: Seq<nat>| logs::segment(m,v) && #[trigger] retention::compatible(d,v);
    if logs::prefix_of(d,v) { logs::prefix_transitive(h,d,v); }
    else { packets::common_prefix(h,v,d); }
    assert(logs::segment(m,v) && retention::compatible(h,v));
}
pub proof fn applicable(b: Behavior<LState>,c: Constants,horizon: int,time: int,d: Decision,h: Seq<nat>,i: int,bound: nat)
    requires election::safety_spec(b,c),0 <= time <= horizon,trace::at(b,c,horizon).decisions.contains(d),
        logs::prefix_of(h,d.log),d.term <= b[time].nodes[i].term
    ensures retention::applicable(b[time],i,h,bound)
{
    assert forall |m: Message| #[trigger] b[time].messages.count(m) > 0 && m.dest == i && m.term == b[time].nodes[i].term
        && m.term <= bound && m.body is AppendRequest implies retention::packet(h,m) by {
        packet_compatible(b,c,horizon,time,d,m); smaller_packet(h,d.log,m);
    }
}
pub proof fn acknowledgment_retained(b: Behavior<LState>,c: Constants,horizon: int,d: Decision,h: Seq<nat>,
    start: int,release: int,end: int,m: Message)
    requires election::safety_spec(b,c),0 <= start <= release < end <= horizon,trace::at(b,c,horizon).decisions.contains(d),
        logs::prefix_of(h,d.log),logs::prefix_of(h,b[start].nodes[m.source].log),d.term <= m.term,
        events::step(b,c,release) == Action::Ready(m.source),
        forall |r: int| start <= r <= release ==> #[trigger] b[r].pending.count(m) > 0
    ensures logs::prefix_of(h,b[end].nodes[m.source].log),logs::prefix_of(h,b[end].nodes[m.source].disk.log)
{
    let i=m.source; let bound=b[end].nodes[i].term;
    election::safety_at(b,c,start); assert(b[start].pending.count(m) > 0); assert(election::pending_inv(b[start],c,m));
    assert forall |r: int| start <= r < end implies #[trigger] retention::applicable(b[r],i,h,bound) by {
        if r <= release {
            assert(b[r].pending.count(m) > 0); origins::safety_at(b,c,r); assert(origins::pending_terms(b[r],m));
        } else { assert(b[release].pending.count(m) > 0); events::released_term(b,c,m,release,r); }
        applicable(b,c,horizon,r,d,h,i,bound);
    }
    retention::pending_interval(b,c,i,h,bound,start,release,m); events::step_valid(b,c,release); reveal(apply);
    assert(retention::live(b[release+1],i,h,bound) && retention::durable(b[release+1],i,h,bound));
    retention::durable_interval(b,c,i,h,bound,release+1,end); election::safety_at(b,c,end); assert(election::node_inv(b[end],c,i));
}
pub proof fn decision_ack(b: Behavior<LState>,c: Constants,horizon: int,d: Decision,j: int) -> (w: (int,int,int,Message))
    requires election::safety_spec(b,c),horizon >= 0,trace::at(b,c,horizon).decisions.contains(d),d.quorum.contains(j)
    ensures 0 <= w.0 < w.1 < w.2 < horizon,w.3.source == j,w.3.term == d.term,
        events::step(b,c,w.1) == Action::Ready(j),logs::prefix_of(d.log,b[w.0+1].nodes[j].log),
        forall |r: int| w.0 < r <= w.1 ==> #[trigger] b[r].pending.count(w.3) > 0
{
    trace::valid(b,c,horizon); assert(history::decision_valid(trace::at(b,c,horizon),c,d));
    let decided=trace::decision_origin(b,c,horizon,d); let k=d.log.len() as int;
    assert(c.servers.contains(j)); assert(b[decided].nodes[d.leader].matched[j] >= k);
    assert(b[decided].nodes[d.leader].log[k-1] == d.term);
    assert forall |old: Decision| trace::at(b,c,decided).decisions.contains(old) && old.term < b[decided].nodes[d.leader].term
        implies #[trigger] logs::prefix_of(old.log,b[decided].nodes[d.leader].log) by {
        completeness::historical_completeness(b,c,decided,decided,d.leader,old);
    }
    acks::acknowledgment_prefix(b,c,decided,d.leader,j,k)
}
pub proof fn quorum_retained(b: Behavior<LState>,c: Constants,time: int,d: Decision)
    requires election::safety_spec(b,c),time >= 0,trace::at(b,c,time).decisions.contains(d)
    ensures forall |j: int| d.quorum.contains(j) ==> #[trigger] logs::prefix_of(d.log,b[time].nodes[j].log) && logs::prefix_of(d.log,b[time].nodes[j].disk.log)
{
    trace::valid(b,c,time); assert(history::decision_valid(trace::at(b,c,time),c,d));
    assert forall |j: int| d.quorum.contains(j) implies #[trigger] logs::prefix_of(d.log,b[time].nodes[j].log) && logs::prefix_of(d.log,b[time].nodes[j].disk.log) by {
        let w=decision_ack(b,c,time,d,j); assert(logs::prefix_of(d.log,d.log));
        acknowledgment_retained(b,c,time,d,d.log,w.0+1,w.1,time,w.3);
    }
}
} // verus!
