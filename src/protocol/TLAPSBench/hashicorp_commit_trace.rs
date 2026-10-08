//! Commit metadata is backed by actual leader decisions below a term bound.
//! Leader uniqueness and direct-decision completeness are explicit hypotheses.
use vstd::prelude::*;
use super::hashicorp::{*,sub};
use super::hashicorp_config as configs;
use super::hashicorp_types as types;
use super::hashicorp_order as order;
use super::hashicorp_history::{self as history,step};
use super::hashicorp_replication as replication;
use super::hashicorp_prefixes as prefixes;
use super::hashicorp_commits as commits;
use super::hashicorp_retention::{self as retention,decision,decided,complete_below};
use super::temporal::Behavior;
verus! {
pub proof fn accepted_prefix(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,time: int,m: Message) -> (sent: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),0 <= time < horizon,
        step(b,c,time) == (Action::Receive { m,how: Receive::AcceptAppend }),m.body is AppendRequest,
        m.body->AppendRequest_mode == Mode::Replicate,m.term < bound
    ensures 0 <= sent < time,c.servers.contains(m.source),c.servers.contains(m.dest),
        b[sent].nodes[m.source].role == Role::Leader,b[sent].nodes[m.source].term == m.term,
        m.body->AppendRequest_commit <= b[sent].nodes[m.source].commit,
        prefix(b[sent].nodes[m.source].log,b[time+1].nodes[m.dest].log)
{
    history::step_valid(b,c,time); reveal(enabled); reveal(receive_enabled); reveal(protocol_apply); reveal(receive);
    let sent=replication::request_bound(b,c,time,m); let source=b[sent].nodes[m.source].log; let stored=b[time+1].nodes[m.dest].log;
    let prev=m.body->AppendRequest_prev; let entries=m.body->AppendRequest_entries;
    types::safety_at(b,c,time); assert(types::message(m,c));
    replication::merge_length(b[time].nodes[m.dest].log,prev,entries);
    if source.len() > 0 {
        let k=source.len() as int-1;
        if entries.len() > 0 { replication::merged_terms(b[time].nodes[m.dest].log,prev,entries,entries.len() as int-1); assert(entries[entries.len()-1] == source[k]); }
        else { reveal(merge); assert(stored == b[time].nodes[m.dest].log); }
        let g=order::safety_at(b,c,sent); assert(order::node(g.state.nodes[m.source])); assert(source[k].term <= m.term);
        assert(stored[k].term == source[k].term);
        prefixes::log_matching_below(b,c,horizon,bound,sent,time+1,m.source,m.dest,k);
    }
    assert(sub(source,1,source.len() as int) =~= source);
    if source.len() == 0 { assert(sub(stored,1,0) =~= source); }
    sent
}
pub open spec fn covered(b: Behavior<LState>,c: Constants,time: int,i: int,at: int,j: int) -> bool {
    0 <= at < time && decision(b,c,at,j) && c.servers.contains(j) && b[at].nodes[j].term <= b[time].nodes[i].term
    && prefix(sub(b[time].nodes[i].log,1,b[time].nodes[i].commit as int),decided(b,at,j))
}
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub proof fn coverage_at(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,time: int,i: int) -> (origin: (int,int))
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),complete_below(b,c,horizon,bound),
        0 <= time <= horizon,c.servers.contains(i),b[time].nodes[i].term < bound
    ensures b[time].nodes[i].commit <= b[time].nodes[i].log.len(),
        b[time].nodes[i].commit > 0 ==> covered(b,c,time,i,origin.0,origin.1)
    decreases time
{
    if b[time].nodes[i].commit == 0 { (0,i) }
    else if time == 0 { assert(false); (0,i) }
    else {
        let p=time-1; history::step_valid(b,c,p); let a=step(b,c,p); let n=b[p].nodes[i]; let u=b[time].nodes[i];
        history::term_role_interval(b,c,i,p,time);
        if a == Action::AdvanceCommit(i) {
            commits::decision_certificate(b,c,p,i); retention::reflexive(decided(b,p,i)); (p,i)
        } else if u.commit > n.commit {
            reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
            assert(a is Receive); let m=a->Receive_m;
            assert(m.dest == i && a->Receive_how == Receive::AcceptAppend && m.body is AppendRequest);
            let basic=replication::request_bound(b,c,p,m);
            assert(m.body->AppendRequest_mode == Mode::Replicate);
            let sent=accepted_prefix(b,c,horizon,bound,p,m); let source=b[sent].nodes[m.source];
            let old=coverage_at(b,c,horizon,bound,sent,m.source);
            assert(source.commit > 0 && u.commit <= source.commit);
            assert(covered(b,c,sent,m.source,old.0,old.1));
            assert(sub(u.log,1,u.commit as int) =~= sub(source.log,1,u.commit as int));
            assert(sub(sub(source.log,1,source.commit as int),1,u.commit as int) =~= sub(source.log,1,u.commit as int));
            retention::transitive(sub(u.log,1,u.commit as int),sub(source.log,1,source.commit as int),decided(b,old.0,old.1));
            old
        } else {
            assert(n.commit > 0); let old=coverage_at(b,c,horizon,bound,p,i);
            let d=decided(b,old.0,old.1); let h=sub(d,1,n.commit as int);
            assert(h == sub(n.log,1,n.commit as int)); assert(prefix(h,n.log));
            retention::preserve(b,c,horizon,bound,p,i,old.0,old.1,n.commit as int);
            reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
            assert(u.commit == n.commit); assert(sub(u.log,1,u.commit as int) == h); assert(prefix(h,d));
            old
        }
    }
}
pub proof fn proposal_decision(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,time: int,i: int,member: int) -> (at: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),complete_below(b,c,horizon,bound),
        0 <= time <= horizon,step(b,c,time) == (Action::ProposeConfig { i,member }),b[time].nodes[i].term < bound
    ensures 0 <= at < time,decision(b,c,at,i),b[at].nodes[i].term == b[time].nodes[i].term,
        b[time].nodes[i].commit <= b[time].nodes[i].log.len(),
        prefix(sub(b[time].nodes[i].log,1,b[time].nodes[i].commit as int),decided(b,at,i))
{
    history::step_valid(b,c,time); reveal(enabled);
    let origin=coverage_at(b,c,horizon,bound,time,i); let at=origin.0; let writer=origin.1; let n=b[time].nodes[i];
    assert(covered(b,c,time,i,at,writer)); commits::decision_certificate(b,c,at,writer);
    let g=order::safety_at(b,c,at); assert(order::node(g.state.nodes[writer]));
    let h=sub(n.log,1,n.commit as int); let d=decided(b,at,writer); let k=n.commit as int-1;
    assert(h.len() == n.commit); assert(h == sub(d,1,h.len() as int)); assert(h[k] == d[k]);
    assert(n.log[n.commit-1] == decided(b,at,writer)[n.commit-1]);
    assert(decided(b,at,writer)[n.commit-1] == b[at].nodes[writer].log[n.commit-1]);
    assert(b[at].nodes[writer].log[n.commit-1].term <= b[at].nodes[writer].term);
    assert(b[at].nodes[writer].term == n.term); assert(writer == i); at
}
} // verus!
