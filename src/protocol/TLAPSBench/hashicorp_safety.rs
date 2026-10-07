//! Full safety by nested induction over terms and election order.
//! Each inner induction proves completeness for already elected leaders in the
//! current term. The outer induction then establishes uniqueness and completeness.
use vstd::prelude::*;
use super::hashicorp::*;
use super::hashicorp_config as configs;
use super::hashicorp_prefixes as prefixes;
use super::hashicorp_election_reduction as leaders;
use super::hashicorp_eligibility::{self as eligibility,eligible,prior_complete};
use super::hashicorp_eligible_safety::{self as eligible_safety,complete};
use super::hashicorp_retention::{self as retention,decision,decided,complete_below};
use super::hashicorp_safety_reduction as reduction;
use super::temporal::Behavior;
verus! {
pub open spec fn elections_complete(b: Behavior<LState>,c: Constants,horizon: int,term: nat,cut: int) -> bool {
    forall |e: Event| (#[trigger] b[cut].elections.contains(e)) && e.term == term ==> eligible(b,c,horizon,e) && complete(b,c,horizon,e)
}
pub proof fn prior_from_elections(b: Behavior<LState>,c: Constants,horizon: int,term: nat,cut: int)
    requires configs::safety_spec(b,c),0 <= cut <= horizon,elections_complete(b,c,horizon,term,cut)
    ensures prior_complete(b,c,horizon,term,cut+1)
{
    assert forall |at: int,i: int,time: int,j: int| 0 <= at < horizon && 0 <= time < cut+1
        && decision(b,c,at,i) && c.servers.contains(j) && (#[trigger] b[time].nodes[j]).role == Role::Leader
        && b[time].nodes[j].term == term && (#[trigger] b[at].nodes[i]).term < term
        implies prefix(decided(b,at,i),b[time].nodes[j].log) by {
        let e=leaders::current_election(b,c,time,j); leaders::election_history(b,c,time,cut);
        assert(b[cut].elections.contains(e)); assert(complete(b,c,horizon,e));
        assert(prefix(decided(b,at,i),e.entries)); retention::transitive(decided(b,at,i),e.entries,b[time].nodes[j].log);
    }
}
pub proof fn elections_at(b: Behavior<LState>,c: Constants,horizon: int,term: nat,cut: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,term),complete_below(b,c,horizon,term),0 <= cut <= horizon
    ensures elections_complete(b,c,horizon,term,cut),prior_complete(b,c,horizon,term,cut+1)
    decreases cut
{
    if cut > 0 {
        let p=cut-1; elections_at(b,c,horizon,term,p); assert(prior_complete(b,c,horizon,term,p));
        leaders::election_history(b,c,cut,horizon);
        assert forall |e: Event| (#[trigger] b[cut].elections.contains(e)) && e.term == term implies eligible(b,c,horizon,e) && complete(b,c,horizon,e) by {
            if b[p].elections.contains(e) { assert(eligible(b,c,horizon,e) && complete(b,c,horizon,e)); }
            else {
                eligibility::eligible_election(b,c,horizon,p,e); assert(b[horizon].elections.contains(e));
                eligible_safety::complete_eligible(b,c,horizon,e);
            }
        }
    }
    assert(elections_complete(b,c,horizon,term,cut)); prior_from_elections(b,c,horizon,term,cut);
}
pub proof fn extend_unique(b: Behavior<LState>,c: Constants,horizon: int,term: nat)
    requires configs::safety_spec(b,c),horizon >= 0,prefixes::unique_below(b,c,horizon,term),complete_below(b,c,horizon,term),
        elections_complete(b,c,horizon,term,horizon)
    ensures prefixes::unique_below(b,c,horizon,term+1)
{
    assert forall |left: int,right: int,i: int,j: int| 0 <= left <= horizon && 0 <= right <= horizon
        && c.servers.contains(i) && c.servers.contains(j)
        && (#[trigger] b[left].nodes[i]).role == Role::Leader && (#[trigger] b[right].nodes[j]).role == Role::Leader
        && b[left].nodes[i].term == b[right].nodes[j].term && b[left].nodes[i].term < term+1 implies i == j by {
        if b[left].nodes[i].term < term { assert(i == j); }
        else {
            let a=leaders::current_election(b,c,left,i); let d=leaders::current_election(b,c,right,j);
            leaders::election_history(b,c,left,horizon); leaders::election_history(b,c,right,horizon);
            assert(b[horizon].elections.contains(a) && b[horizon].elections.contains(d));
            assert(eligible(b,c,horizon,a) && eligible(b,c,horizon,d));
            eligible_safety::unique_eligible(b,c,horizon,a,d);
        }
    }
}
pub proof fn extend_complete(b: Behavior<LState>,c: Constants,horizon: int,term: nat)
    requires complete_below(b,c,horizon,term),prior_complete(b,c,horizon,term,horizon+1)
    ensures complete_below(b,c,horizon,term+1)
{
    assert forall |at: int,i: int,time: int,j: int| 0 <= at < horizon && 0 <= time <= horizon
        && decision(b,c,at,i) && c.servers.contains(j) && (#[trigger] b[time].nodes[j]).role == Role::Leader
        && (#[trigger] b[at].nodes[i]).term < b[time].nodes[j].term < term+1
        implies prefix(decided(b,at,i),b[time].nodes[j].log) by {
        if b[time].nodes[j].term < term { assert(prefix(decided(b,at,i),b[time].nodes[j].log)); }
        else { assert(b[time].nodes[j].term == term); }
    }
}
pub proof fn core_at(b: Behavior<LState>,c: Constants,horizon: int,bound: nat)
    requires configs::safety_spec(b,c),horizon >= 0
    ensures prefixes::unique_below(b,c,horizon,bound),complete_below(b,c,horizon,bound)
    decreases bound
{
    if bound > 0 {
        let term=(bound-1) as nat; core_at(b,c,horizon,term); elections_at(b,c,horizon,term,horizon);
        extend_unique(b,c,horizon,term); extend_complete(b,c,horizon,term);
    }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,time: int)
    requires configs::safety_spec(b,c),time >= 0
    ensures election_safety(b[time]),log_matching(b[time],c),leader_completeness(b[time]),state_machine_safety(b[time]),committed_preserved(b[time])
{
    let bound=reduction::term_bound(b,c,time); core_at(b,c,time,bound); reduction::benchmark_reduction(b,c,time,bound);
}
pub proof fn benchmark_safety(b: Behavior<LState>,c: Constants)
    requires configs::safety_spec(b,c)
    ensures forall |time: int| time >= 0 ==> #[trigger] election_safety(b[time]),
        forall |time: int| time >= 0 ==> #[trigger] log_matching(b[time],c),
        forall |time: int| time >= 0 ==> #[trigger] leader_completeness(b[time]),
        forall |time: int| time >= 0 ==> #[trigger] state_machine_safety(b[time]),
        forall |time: int| time >= 0 ==> #[trigger] committed_preserved(b[time])
{
    assert forall |time: int| time >= 0 implies #[trigger] election_safety(b[time]) by { safety_at(b,c,time); }
    assert forall |time: int| time >= 0 implies #[trigger] log_matching(b[time],c) by { safety_at(b,c,time); }
    assert forall |time: int| time >= 0 implies #[trigger] leader_completeness(b[time]) by { safety_at(b,c,time); }
    assert forall |time: int| time >= 0 implies #[trigger] state_machine_safety(b[time]) by { safety_at(b,c,time); }
    assert forall |time: int| time >= 0 implies #[trigger] committed_preserved(b[time]) by { safety_at(b,c,time); }
}
} // verus!
