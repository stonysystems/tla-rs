//! Prefix compatibility between a direct decision and a later election.
use vstd::prelude::*;
use super::etcd::*;
use super::etcd_election as election;
use super::etcd_origins as origins;
use super::etcd_logs as logs;
use super::etcd_sent as sent;
use super::etcd_order as order;
use super::etcd_commit_history::{self as history,Decision};
use super::etcd_history_trace as trace;
use super::etcd_leader_trace as leaders;
use super::etcd_transmissions as events;
use super::etcd_retention as retention;
use super::etcd_vote_witness as votes;
use super::temporal::Behavior;
verus! {
pub open spec fn complete_below(b: Behavior<LState>,c: Constants,horizon: int,term: nat) -> bool {
    forall |time: int,i: int,d: Decision| 0 <= time <= horizon && c.servers.contains(i)
        && b[time].nodes[i].role == Role::Leader && d.term < b[time].nodes[i].term < term
        && trace::at(b,c,horizon).decisions.contains(d) ==> #[trigger] logs::prefix_of(d.log,b[time].nodes[i].log)
}
pub proof fn common_prefix(a: Seq<nat>,b: Seq<nat>,h: Seq<nat>)
    requires logs::prefix_of(a,h),logs::prefix_of(b,h)
    ensures retention::compatible(a,b)
{
    if a.len() <= b.len() {
        assert forall |k: int| 0 <= k < a.len() implies #[trigger] a[k] == #[trigger] b[k] by { assert(a[k] == h[k]); assert(b[k] == h[k]); }
    } else {
        assert forall |k: int| 0 <= k < b.len() implies #[trigger] b[k] == #[trigger] a[k] by { assert(a[k] == h[k]); assert(b[k] == h[k]); }
    }
}
pub proof fn historical_authority(b: Behavior<LState>,c: Constants,lo: int,hi: int,t: nat,i: int)
    requires election::safety_spec(b,c),0 <= lo <= hi,origins::certificate(b[lo],c,t,i)
    ensures origins::certificate(b[hi],c,t,i)
{ events::votes_monotone(b,c,lo,hi); origins::certificate_monotone(b[lo],b[hi],c,t,i); }
pub proof fn same_term_packet(b: Behavior<LState>,c: Constants,horizon: int,time: int,d: Decision,m: Message)
    requires election::safety_spec(b,c),0 <= time <= horizon,trace::at(b,c,horizon).decisions.contains(d),
        b[time].messages.count(m) > 0,m.body is AppendRequest,m.term == d.term
    ensures retention::packet(d.log,m)
{
    trace::valid(b,c,horizon); assert(history::decision_valid(trace::at(b,c,horizon),c,d));
    let created=leaders::request_origin(b,c,time,m); let decided=trace::decision_origin(b,c,horizon,d);
    origins::safety_at(b,c,created); origins::leader_persisted(b[created],c,m.source);
    historical_authority(b,c,created,horizon,m.term,m.source);
    origins::unique_certificate(b[horizon],c,d.term,m.source,d.leader);
    events::step_valid(b,c,decided); reveal(enabled); reveal(apply);
    assert(b[decided].nodes[d.leader].role == Role::Leader && b[decided].nodes[d.leader].term == d.term);
    assert(logs::prefix_of(d.log,b[decided].nodes[d.leader].log));
    if created <= decided {
        leaders::continuous(b,c,d.leader,created,decided);
        common_prefix(d.log,b[created].nodes[d.leader].log,b[decided].nodes[d.leader].log);
    } else {
        leaders::continuous(b,c,d.leader,decided,created);
        logs::prefix_transitive(d.log,b[decided].nodes[d.leader].log,b[created].nodes[d.leader].log);
    }
    assert(logs::segment(m,b[created].nodes[m.source].log) && retention::compatible(d.log,b[created].nodes[m.source].log));
}
pub proof fn no_election_term_packet(b: Behavior<LState>,c: Constants,elect: int,time: int,i: int,m: Message)
    requires election::safety_spec(b,c),0 <= time <= elect,c.servers.contains(i),events::step(b,c,elect) == Action::BecomeLeader(i),
        b[time].messages.count(m) > 0,m.body is AppendRequest,m.term == b[elect].nodes[i].term
    ensures false
{
    events::step_valid(b,c,elect); reveal(enabled); reveal(apply);
    origins::safety_at(b,c,elect+1); origins::leader_persisted(b[elect+1],c,i);
    sent::safety_at(b,c,time); assert(sent::authority(b[time],c,m));
    historical_authority(b,c,time,elect+1,m.term,m.source);
    origins::unique_certificate(b[elect+1],c,m.term,i,m.source);
    votes::persisted_candidate_interval(b,c,i,m.term,time,elect); assert(false);
}
pub proof fn packet_before_election(b: Behavior<LState>,c: Constants,horizon: int,elect: int,time: int,i: int,d: Decision,m: Message)
    requires election::safety_spec(b,c),0 <= time <= elect <= horizon,c.servers.contains(i),events::step(b,c,elect) == Action::BecomeLeader(i),
        trace::at(b,c,horizon).decisions.contains(d),d.term < b[elect].nodes[i].term,
        complete_below(b,c,horizon,b[elect].nodes[i].term),
        b[time].messages.count(m) > 0,m.body is AppendRequest,d.term <= m.term <= b[elect].nodes[i].term
    ensures retention::packet(d.log,m)
{
    if m.term == b[elect].nodes[i].term { no_election_term_packet(b,c,elect,time,i,m); }
    else if m.term == d.term { same_term_packet(b,c,horizon,time,d,m); }
    else {
        let created=leaders::request_origin(b,c,time,m);
        assert(logs::prefix_of(d.log,b[created].nodes[m.source].log));
        assert(logs::segment(m,b[created].nodes[m.source].log) && retention::compatible(d.log,b[created].nodes[m.source].log));
    }
}
pub proof fn applicable_before_vote(b: Behavior<LState>,c: Constants,horizon: int,elect: int,i: int,d: Decision,
    start: int,release: int,grant: int,m: Message)
    requires election::safety_spec(b,c),0 <= elect <= horizon,c.servers.contains(i),events::step(b,c,elect) == Action::BecomeLeader(i),
        trace::at(b,c,horizon).decisions.contains(d),d.term < b[elect].nodes[i].term,complete_below(b,c,horizon,b[elect].nodes[i].term),
        0 <= start <= release,start <= grant < elect,m.term == d.term,events::step(b,c,release) == Action::Ready(m.source),
        forall |r: int| start <= r <= release ==> #[trigger] b[r].pending.count(m) > 0
    ensures forall |r: int| start <= r < grant ==> #[trigger] retention::applicable(b[r],m.source,d.log,b[elect].nodes[i].term)
{
    assert forall |r: int| start <= r < grant implies #[trigger] retention::applicable(b[r],m.source,d.log,b[elect].nodes[i].term) by {
        if r <= release {
            assert(b[r].pending.count(m) > 0); origins::safety_at(b,c,r); assert(origins::pending_terms(b[r],m));
        } else { assert(b[release].pending.count(m) > 0); events::released_term(b,c,m,release,r); }
        assert(d.term <= b[r].nodes[m.source].term);
        assert forall |p: Message| #[trigger] b[r].messages.count(p) > 0 && p.dest == m.source && p.term == b[r].nodes[m.source].term
            && p.term <= b[elect].nodes[i].term && p.body is AppendRequest implies retention::packet(d.log,p) by {
            packet_before_election(b,c,horizon,elect,r,i,d,p);
        }
    }
}
} // verus!
