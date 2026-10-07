//! One canonical passive history along a behavior, with origins for its records.
use vstd::prelude::*;
use super::etcd::*;
use super::etcd_election as election;
use super::etcd_origins as origins;
use super::etcd_logs as logs;
use super::etcd_prefixes as prefixes;
use super::etcd_decision_owners as owners;
use super::etcd_commit_history::{self as history,ProofState,Decision,state};
use super::etcd_transmissions as events;
use super::temporal::Behavior;
verus! {
pub open spec fn at(b: Behavior<LState>,c: Constants,k: int) -> ProofState
    decreases k
{
    if k <= 0 { history::initial_proof(c) }
    else { history::advance(at(b,c,k-1),c,events::step(b,c,k-1)) }
}
pub proof fn valid(b: Behavior<LState>,c: Constants,k: int)
    requires election::safety_spec(b,c),k >= 0
    ensures state(at(b,c,k)) == b[k],owners::inductive(at(b,c,k),c),prefixes::inductive(at(b,c,k).logs,c)
    decreases k
{
    if k == 0 { owners::initial_inductive(c); prefixes::initial_inductive(c); }
    else {
        valid(b,c,k-1); events::step_valid(b,c,k-1);
        owners::preserve(at(b,c,k-1),c,events::step(b,c,k-1));
        prefixes::preserve(at(b,c,k-1).logs,c,events::step(b,c,k-1));
    }
}
pub proof fn monotone(b: Behavior<LState>,c: Constants,lo: int,hi: int)
    requires 0 <= lo <= hi
    ensures at(b,c,lo).decisions.subset_of(at(b,c,hi).decisions),at(b,c,lo).logs.created.subset_of(at(b,c,hi).logs.created)
    decreases hi-lo
{
    if hi > lo {
        monotone(b,c,lo,hi-1);
        assert(at(b,c,hi-1).decisions.subset_of(at(b,c,hi).decisions));
        assert(at(b,c,hi-1).logs.created.subset_of(at(b,c,hi).logs.created));
    }
}
pub proof fn decision_origin(b: Behavior<LState>,c: Constants,k: int,d: Decision) -> (j: int)
    requires election::safety_spec(b,c),k >= 0,at(b,c,k).decisions.contains(d)
    ensures 0 <= j < k,events::step(b,c,j) == Action::AdvanceCommit(d.leader),
        b[j+1].nodes[d.leader].commit > b[j].nodes[d.leader].commit,
        d == history::record(b[j],c,d.leader,b[j+1].nodes[d.leader].commit),
        at(b,c,j+1).decisions.contains(d),c.servers.contains(d.leader),b[j].nodes[d.leader].role == Role::Leader,
        b[j].nodes[d.leader].term == d.term,d.log.len() == b[j+1].nodes[d.leader].commit,
        0 < d.log.len() <= b[j].nodes[d.leader].log.len(),logs::prefix_of(d.log,b[j].nodes[d.leader].log)
    decreases k
{
    if k == 0 { assert(false); arbitrary() }
    else {
        let p=k-1;
        if at(b,c,p).decisions.contains(d) { decision_origin(b,c,p,d) }
        else {
            valid(b,c,p); events::step_valid(b,c,p); let a=events::step(b,c,p);
            if let Action::AdvanceCommit(i) = a {
                reveal(enabled); reveal(apply); let n=b[p].nodes[i];
                assert(!agreed_indices(n,c).is_empty()); origins::maximum_correct(agreed_indices(n,c));
            } else { assert(false); }
            p
        }
    }
}
pub proof fn created_origin(b: Behavior<LState>,c: Constants,k: int,h: Seq<nat>) -> (w: (int,int))
    requires election::safety_spec(b,c),k >= 0,at(b,c,k).logs.created.contains(h),h.len() > 0
    ensures 0 <= w.0 < k,events::step(b,c,w.0) == Action::ClientRequest(w.1),
        h == b[w.0+1].nodes[w.1].log,b[w.0].nodes[w.1].role == Role::Leader,
        h.last() == b[w.0].nodes[w.1].term,c.servers.contains(w.1)
    decreases k
{
    if k == 0 { assert(false); arbitrary() }
    else {
        let p=k-1;
        if at(b,c,p).logs.created.contains(h) { created_origin(b,c,p,h) }
        else {
            valid(b,c,p); events::step_valid(b,c,p); let a=events::step(b,c,p);
            reveal(enabled); reveal(apply);
            if let Action::ClientRequest(i) = a { (p,i) } else { assert(false); arbitrary() }
        }
    }
}
pub proof fn live_log(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires election::safety_spec(b,c),time >= 0,c.servers.contains(i)
    ensures at(b,c,time).logs.created.contains(b[time].nodes[i].log),at(b,c,time).logs.created.contains(b[time].nodes[i].disk.log)
{
    valid(b,c,time); let g=at(b,c,time).logs;
    assert(logs::represented(g,b[time].nodes[i].log)); prefixes::represented_is_created(g,b[time].nodes[i].log);
    assert(logs::represented(g,b[time].nodes[i].disk.log)); prefixes::represented_is_created(g,b[time].nodes[i].disk.log);
}
pub proof fn decision_log(b: Behavior<LState>,c: Constants,time: int,d: Decision)
    requires election::safety_spec(b,c),time >= 0,at(b,c,time).decisions.contains(d)
    ensures at(b,c,time).logs.created.contains(d.log)
{
    valid(b,c,time); assert(history::decision_valid(at(b,c,time),c,d));
    prefixes::represented_is_created(at(b,c,time).logs,d.log);
}
} // verus!
