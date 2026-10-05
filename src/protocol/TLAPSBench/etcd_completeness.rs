//! Historical leader completeness, proved by induction on the election term.
//! A decision's term is the term of its committing leader, not the entry term
//! used by the benchmark's separate, refuted LeaderCompleteness target.
use vstd::prelude::*;
use super::etcd::{*,sub};
use super::etcd_election as election;
use super::etcd_logs as logs;
use super::etcd_order as order;
use super::etcd_candidates as candidates;
use super::etcd_prefixes as prefixes;
use super::etcd_commit_history::{self as history,Decision};
use super::etcd_history_trace as trace;
use super::etcd_transmissions as events;
use super::etcd_vote_witness as votes;
use super::etcd_match_witness as matches;
use super::etcd_ack_prefixes as acks;
use super::etcd_election_prefixes::{self as packets,complete_below};
use super::etcd_retention as retention;
use super::temporal::Behavior;
verus! {
pub proof fn historical_prefixes(b: Behavior<LState>,c: Constants,horizon: int,d: Decision,t: nat)
    requires election::safety_spec(b,c),horizon >= 0,trace::at(b,c,horizon).decisions.contains(d),complete_below(b,c,horizon,t)
    ensures forall |h: Seq<nat>| trace::at(b,c,horizon).logs.created.contains(h) && d.term < last_term(h) < t ==> #[trigger] logs::prefix_of(d.log,h)
{
    assert forall |h: Seq<nat>| trace::at(b,c,horizon).logs.created.contains(h) && d.term < last_term(h) < t implies #[trigger] logs::prefix_of(d.log,h) by {
        assert(h.len() > 0); let w=trace::created_origin(b,c,horizon,h);
        events::step_valid(b,c,w.0); reveal(apply);
        assert(b[w.0+1].nodes[w.1].role == Role::Leader && b[w.0+1].nodes[w.1].term == last_term(h));
        assert(logs::prefix_of(d.log,b[w.0+1].nodes[w.1].log));
    }
}
pub proof fn candidate_retains(b: Behavior<LState>,c: Constants,horizon: int,elect: int,i: int,d: Decision)
    requires election::safety_spec(b,c),0 <= elect < horizon,c.servers.contains(i),events::step(b,c,elect) == Action::BecomeLeader(i),
        trace::at(b,c,horizon).decisions.contains(d),d.term < b[elect].nodes[i].term,complete_below(b,c,horizon,b[elect].nodes[i].term)
    ensures logs::prefix_of(d.log,b[elect].nodes[i].log)
{
    let t=b[elect].nodes[i].term; trace::valid(b,c,horizon); events::step_valid(b,c,elect); reveal(enabled);
    election::safety_at(b,c,elect); assert(election::node_inv(b[elect],c,i));
    assert(history::decision_valid(trace::at(b,c,horizon),c,d));
    let decision=trace::decision_origin(b,c,horizon,d); let k=d.log.len() as int;
    let j=election::majorities_intersect(d.quorum,b[elect].nodes[i].granted,c);
    assert(c.servers.contains(j)); assert(b[decision].nodes[d.leader].matched[j] >= k);
    assert forall |old: Decision| trace::at(b,c,decision).decisions.contains(old) && old.term < b[decision].nodes[d.leader].term
        implies #[trigger] logs::prefix_of(old.log,b[decision].nodes[d.leader].log) by {
        trace::monotone(b,c,decision,horizon);
        assert(logs::prefix_of(old.log,b[decision].nodes[d.leader].log));
    }
    assert(b[decision].nodes[d.leader].log[k-1] == d.term);
    let w=acks::acknowledgment_prefix(b,c,decision,d.leader,j,k);
    assert(d.log == sub(b[decision].nodes[d.leader].log,1,k));
    let ballot=Ballot { voter: j,term: t,candidate: i };
    assert(b[elect].votes.contains(ballot)); let vr=events::vote_origin(b,c,elect,ballot);
    let grant=events::pending_origin(b,c,vr.0,vr.1);
    events::creation_precedes_grant(b,c,w.0,grant,vr.0,w.3,vr.1);
    votes::grant_comparison(b,c,elect,ballot,grant,vr.0,vr.1);
    packets::applicable_before_vote(b,c,horizon,elect,i,d,w.0+1,w.1,grant,w.3);
    retention::acknowledgment_to_vote(b,c,j,d.log,t,w.0+1,w.1,grant,w.3);
    trace::live_log(b,c,elect,i); trace::monotone(b,c,elect,horizon); trace::decision_log(b,c,horizon,d);
    let g=trace::at(b,c,horizon).logs;
    assert(logs::prefix_of(d.log,d.log)); assert(logs::represented(g,d.log));
    assert(logs::prefix_of(b[elect].nodes[i].log,b[elect].nodes[i].log)); assert(logs::represented(g,b[elect].nodes[i].log));
    order::safety_at(b,c,grant); assert(order::node_order(b[grant].nodes[j]));
    candidates::safety_at(b,c,elect); assert(candidates::candidate(b[elect].nodes[i]));
    historical_prefixes(b,c,horizon,d,t);
    prefixes::up_to_date_retains(g,c,d.log,b[grant].nodes[j].log,b[elect].nodes[i].log,t);
}
pub proof fn leader_retains(b: Behavior<LState>,c: Constants,horizon: int,time: int,i: int,d: Decision)
    requires election::safety_spec(b,c),0 <= time <= horizon,c.servers.contains(i),b[time].nodes[i].role == Role::Leader,
        trace::at(b,c,horizon).decisions.contains(d),d.term < b[time].nodes[i].term,complete_below(b,c,horizon,b[time].nodes[i].term)
    ensures logs::prefix_of(d.log,b[time].nodes[i].log)
{
    let e=matches::epoch_start(b,c,time,i); candidate_retains(b,c,horizon,e,i,d);
    events::step_valid(b,c,e); reveal(apply);
    matches::leader_log_interval(b,c,i,b[time].nodes[i].term,e+1,time);
    logs::prefix_transitive(d.log,b[e+1].nodes[i].log,b[time].nodes[i].log);
}
pub proof fn complete_by_term(b: Behavior<LState>,c: Constants,horizon: int,bound: nat)
    requires election::safety_spec(b,c),horizon >= 0
    ensures complete_below(b,c,horizon,bound)
    decreases bound
{
    if bound > 0 {
        complete_by_term(b,c,horizon,(bound-1) as nat);
        assert forall |time: int,i: int,d: Decision| 0 <= time <= horizon && c.servers.contains(i)
            && b[time].nodes[i].role == Role::Leader && d.term < b[time].nodes[i].term < bound
            && trace::at(b,c,horizon).decisions.contains(d) implies #[trigger] logs::prefix_of(d.log,b[time].nodes[i].log) by {
            if b[time].nodes[i].term < bound-1 { assert(logs::prefix_of(d.log,b[time].nodes[i].log)); }
            else { leader_retains(b,c,horizon,time,i,d); }
        }
    }
}
pub proof fn historical_completeness(b: Behavior<LState>,c: Constants,horizon: int,time: int,i: int,d: Decision)
    requires election::safety_spec(b,c),0 <= time <= horizon,c.servers.contains(i),b[time].nodes[i].role == Role::Leader,
        trace::at(b,c,horizon).decisions.contains(d),d.term < b[time].nodes[i].term
    ensures logs::prefix_of(d.log,b[time].nodes[i].log)
{ complete_by_term(b,c,horizon,b[time].nodes[i].term+1); }
} // verus!
