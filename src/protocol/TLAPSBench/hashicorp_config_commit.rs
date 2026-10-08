//! Configuration proposals are backed by a current-term commit in their parent
//! configuration, under the explicit hypotheses of the term induction.
use vstd::prelude::*;
use super::hashicorp::{*,sub};
use super::hashicorp_config as configs;
use super::hashicorp_types as types;
use super::hashicorp_order as order;
use super::hashicorp_history::{self as history,step};
use super::hashicorp_commits as commits;
use super::hashicorp_prefixes as prefixes;
use super::hashicorp_retention::{self as retention,complete_below,decision,decided};
use super::hashicorp_commit_trace as trace;
use super::temporal::Behavior;
verus! {
pub open spec fn node(n: LServer) -> bool {
    n.role == Role::Leader ==> forall |k: int| 0 <= k < n.log.len() && (#[trigger] n.log[k]).term == n.term
        ==> n.committed_config_index <= max(n.commit as int,k+1)
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires configs::inductive(s,c),types::inductive(s,c),order::node(s.nodes[i]),node(s.nodes[i]),enabled(s,c,a),c.servers.contains(i)
    ensures node(apply(s,c,a).nodes[i])
{
    let n=s.nodes[i]; let u=apply(s,c,a).nodes[i]; assert(configs::node_inv(n)); configs::config_positions(n.log);
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
    if a == Action::AdvanceCommit(i) { commits::maximum_correct(agree_indices(n,i,c)); }
    assert forall |k: int| u.role == Role::Leader && 0 <= k < u.log.len() && (#[trigger] u.log[k]).term == u.term
        implies u.committed_config_index <= max(u.commit as int,k+1) by {
        if a == Action::BecomeLeader(i) {
            assert(n.log[k].term <= n.log[n.log.len()-1].term); assert(false);
        } else if k < n.log.len() {
            assert(n.role == Role::Leader && n.log[k].term == n.term);
            assert(n.committed_config_index <= max(n.commit as int,k+1));
        } else { assert(k == n.log.len()); }
    }
}
pub proof fn bounds_at(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires configs::safety_spec(b,c),time >= 0,c.servers.contains(i)
    ensures node(b[time].nodes[i])
    decreases time
{
    if time > 0 {
        let p=time-1; bounds_at(b,c,p,i); history::step_valid(b,c,p); configs::safety_at(b,c,p); let g=order::safety_at(b,c,p);
        assert(order::node(g.state.nodes[i])); preserve_node(b[p],c,step(b,c,p),i);
    }
}
pub proof fn commit_marks_config(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires configs::safety_spec(b,c),time >= 0,decision(b,c,time,i)
    ensures b[time+1].nodes[i].committed_config_index <= b[time+1].nodes[i].commit
{
    commits::decision_certificate(b,c,time,i); bounds_at(b,c,time,i); let n=b[time].nodes[i]; let index=b[time+1].nodes[i].commit as int;
    assert(n.log[index-1].term == n.term); assert(n.committed_config_index <= max(n.commit as int,index));
    history::step_valid(b,c,time); reveal(protocol_apply);
}
pub proof fn leader_commit_step(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires configs::safety_spec(b,c),time >= 0,c.servers.contains(i),b[time].nodes[i].role == Role::Leader,b[time+1].nodes[i].role == Role::Leader
    ensures b[time].nodes[i].commit <= b[time+1].nodes[i].commit
{
    history::step_valid(b,c,time); let a=step(b,c,time);
    if a == Action::AdvanceCommit(i) { commits::decision_certificate(b,c,time,i); }
    else { reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive); }
}
pub proof fn leader_commit_interval(b: Behavior<LState>,c: Constants,lo: int,hi: int,i: int)
    requires configs::safety_spec(b,c),0 <= lo <= hi,c.servers.contains(i),b[lo].nodes[i].role == Role::Leader,b[hi].nodes[i].role == Role::Leader,
        b[lo].nodes[i].term == b[hi].nodes[i].term
    ensures b[lo].nodes[i].commit <= b[hi].nodes[i].commit
    decreases hi-lo
{
    if lo < hi {
        let p=hi-1; history::continuous(b,c,i,lo,hi); assert(b[p].nodes[i].role == Role::Leader && b[p].nodes[i].term == b[lo].nodes[i].term);
        leader_commit_interval(b,c,lo,p,i); leader_commit_step(b,c,p,i);
    }
}
pub proof fn metadata_step(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires configs::safety_spec(b,c),time >= 0,c.servers.contains(i),b[time].nodes[i].role == Role::Leader,b[time+1].nodes[i].role == Role::Leader,
        b[time].nodes[i].commit == b[time+1].nodes[i].commit
    ensures b[time].nodes[i].committed_config_index == b[time+1].nodes[i].committed_config_index,
        b[time].nodes[i].latest_config_index <= b[time+1].nodes[i].latest_config_index,
        b[time+1].nodes[i].latest_config_index <= b[time].nodes[i].log.len() ==>
            b[time+1].nodes[i].latest_config == b[time].nodes[i].latest_config && b[time+1].nodes[i].latest_config_index == b[time].nodes[i].latest_config_index
{
    history::step_valid(b,c,time); let a=step(b,c,time); configs::safety_at(b,c,time); assert(configs::node_inv(b[time].nodes[i]));
    configs::config_positions(b[time].nodes[i].log);
    if a == Action::AdvanceCommit(i) { commits::decision_certificate(b,c,time,i); assert(false); }
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
}
pub proof fn metadata_interval(b: Behavior<LState>,c: Constants,lo: int,hi: int,i: int)
    requires configs::safety_spec(b,c),0 <= lo <= hi,c.servers.contains(i),b[lo].nodes[i].role == Role::Leader,b[hi].nodes[i].role == Role::Leader,
        b[lo].nodes[i].term == b[hi].nodes[i].term,b[lo].nodes[i].commit == b[hi].nodes[i].commit
    ensures b[lo].nodes[i].committed_config_index == b[hi].nodes[i].committed_config_index,
        b[lo].nodes[i].latest_config_index <= b[hi].nodes[i].latest_config_index,
        b[hi].nodes[i].latest_config_index <= b[lo].nodes[i].log.len() ==>
            b[hi].nodes[i].latest_config == b[lo].nodes[i].latest_config && b[hi].nodes[i].latest_config_index == b[lo].nodes[i].latest_config_index
    decreases hi-lo
{
    if lo < hi {
        let p=hi-1; history::continuous(b,c,i,lo,hi); assert(b[p].nodes[i].role == Role::Leader && b[p].nodes[i].term == b[lo].nodes[i].term);
        leader_commit_interval(b,c,lo,p,i); leader_commit_step(b,c,p,i); assert(b[p].nodes[i].commit == b[lo].nodes[i].commit);
        metadata_interval(b,c,lo,p,i); metadata_step(b,c,p,i); history::continuous(b,c,i,lo,p);
    }
}
pub proof fn proposal_certificate(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,time: int,i: int,member: int) -> (at: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),complete_below(b,c,horizon,bound),
        0 <= time <= horizon,step(b,c,time) == (Action::ProposeConfig { i,member }),b[time].nodes[i].term < bound
    ensures 0 <= at < time,decision(b,c,at,i),b[at].nodes[i].term == b[time].nodes[i].term,
        b[time].nodes[i].latest_config == b[at].nodes[i].latest_config,
        b[time].nodes[i].latest_config_index <= b[time].nodes[i].commit <= b[time].nodes[i].log.len(),
        b[time].nodes[i].commit == b[at+1].nodes[i].commit,
        sub(b[time].nodes[i].log,1,b[time].nodes[i].commit as int) == decided(b,at,i),
        quorum(commits::voters(b[at].nodes[i],c,i,b[time].nodes[i].commit as int),b[time].nodes[i].latest_config)
{
    let at=trace::proposal_decision(b,c,horizon,bound,time,i,member); commits::decision_certificate(b,c,at,i); history::step_valid(b,c,time); reveal(enabled);
    history::continuous(b,c,i,at,time); assert(b[at+1].nodes[i].role == Role::Leader && b[at+1].nodes[i].term == b[time].nodes[i].term);
    leader_commit_interval(b,c,at+1,time,i); assert(b[at+1].nodes[i].commit == b[time].nodes[i].commit);
    commit_marks_config(b,c,at,i); metadata_interval(b,c,at+1,time,i);
    assert(b[time].nodes[i].latest_config_index <= b[at+1].nodes[i].log.len());
    history::step_valid(b,c,at); reveal(protocol_apply);
    assert(sub(b[time].nodes[i].log,1,b[time].nodes[i].commit as int) == decided(b,at,i));
    at
}
} // verus!
