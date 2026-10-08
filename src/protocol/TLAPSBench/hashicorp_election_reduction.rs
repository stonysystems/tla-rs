//! The full log-matching goal follows from the historical election-safety goal.
//! The election-safety premise is explicit and is still open for dynamic configs.
use vstd::prelude::*;
use super::hashicorp::{*,sub};
use super::hashicorp_config as configs;
use super::hashicorp_history::{self as history,step};
use super::hashicorp_election_trace as elections;
use super::hashicorp_vote_witness::{self as witness,trace};
use super::hashicorp_certificates as certificates;
use super::hashicorp_prefixes as prefixes;
use super::temporal::Behavior;
verus! {
pub proof fn election_history(b: Behavior<LState>,c: Constants,lo: int,hi: int)
    requires configs::safety_spec(b,c),0 <= lo <= hi
    ensures b[lo].elections.subset_of(b[hi].elections)
    decreases hi-lo
{
    if lo < hi { let p=hi-1; election_history(b,c,lo,p); history::step_valid(b,c,p); }
}
pub proof fn current_election(b: Behavior<LState>,c: Constants,time: int,i: int) -> (e: Event)
    requires configs::safety_spec(b,c),time >= 0,c.servers.contains(i),b[time].nodes[i].role == Role::Leader
    ensures b[time].elections.contains(e),e.server == i,e.term == b[time].nodes[i].term,prefix(e.entries,b[time].nodes[i].log)
    decreases time
{
    if time == 0 { assert(false); Event { server: i,term: 0,entries: Seq::empty() } }
    else {
        let p=time-1; history::step_valid(b,c,p); let a=step(b,c,p);
        if b[p].nodes[i].role == Role::Leader && b[p].nodes[i].term == b[time].nodes[i].term {
            let e=current_election(b,c,p,i); history::continuous(b,c,i,p,time);
            assert(sub(b[time].nodes[i].log,1,e.entries.len() as int) =~= e.entries);
            e
        } else {
            reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
            assert(a == Action::BecomeLeader(i)); let e=Event { server: i,term: b[time].nodes[i].term,entries: b[time].nodes[i].log };
            broadcast use Set::lemma_map_contains;
            let changed=c.servers.filter(|j: int| b[p].nodes[j].role != Role::Leader && b[time].nodes[j].role == Role::Leader);
            assert(changed.contains(i)); assert(changed.map(|j: int| Event { server: j,term: b[time].nodes[j].term,entries: b[time].nodes[j].log }).contains(e));
            assert(sub(e.entries,1,e.entries.len() as int) =~= e.entries); e
        }
    }
}
pub proof fn unique_from_election_safety(b: Behavior<LState>,c: Constants,horizon: int,bound: nat)
    requires configs::safety_spec(b,c),horizon >= 0,election_safety(b[horizon])
    ensures prefixes::unique_below(b,c,horizon,bound)
{
    assert forall |left: int,right: int,i: int,j: int| 0 <= left <= horizon && 0 <= right <= horizon
        && c.servers.contains(i) && c.servers.contains(j)
        && (#[trigger] b[left].nodes[i]).role == Role::Leader && (#[trigger] b[right].nodes[j]).role == Role::Leader
        && b[left].nodes[i].term == b[right].nodes[j].term && b[left].nodes[i].term < bound implies i == j by {
        let a=current_election(b,c,left,i); let d=current_election(b,c,right,j);
        election_history(b,c,left,horizon); election_history(b,c,right,horizon);
        assert(b[horizon].elections.contains(a) && b[horizon].elections.contains(d));
    }
}
pub proof fn log_matching_from_election_safety(b: Behavior<LState>,c: Constants,time: int)
    requires configs::safety_spec(b,c),time >= 0,election_safety(b[time])
    ensures log_matching(b[time],c)
{
    assert forall |i: int,j: int,k: int| #![trigger c.servers.contains(i), sub(b[time].nodes[j].log,1,k)] #![trigger c.servers.contains(j), sub(b[time].nodes[i].log,1,k)] c.servers.contains(i) && c.servers.contains(j)
        && 1 <= k <= b[time].nodes[i].log.len() && k <= b[time].nodes[j].log.len()
        && b[time].nodes[i].log[k-1].term == b[time].nodes[j].log[k-1].term implies
        sub(b[time].nodes[i].log,1,k) == sub(b[time].nodes[j].log,1,k) by {
        let bound=b[time].nodes[i].log[k-1].term+1; unique_from_election_safety(b,c,time,bound);
        prefixes::log_matching_below(b,c,time,bound,time,time,i,j,k-1);
    }
}
pub proof fn first_term_election_safety(b: Behavior<LState>,c: Constants,time: int,a: Event,d: Event)
    requires configs::safety_spec(b,c),time >= 0,b[time].elections.contains(a),b[time].elections.contains(d),a.term == 1,d.term == 1
    ensures a.server == d.server
{
    elections::election_log(b,c,time,a); elections::election_log(b,c,time,d);
    if a.entries.len() > 0 { assert(0 < a.entries[0].term < 1); assert(false); }
    if d.entries.len() > 0 { assert(0 < d.entries[0].term < 1); assert(false); }
    witness::trace_valid(b,c,time); let g=trace(b,c,time);
    assert(certificates::certificate(g,c,a)); assert(certificates::certificate(g,c,d));
    assert(certificates::configuration(a,c) == c.servers && certificates::configuration(d,c) == c.servers);
    certificates::adjacent_configurations(g,c,a,d);
}
} // verus!
