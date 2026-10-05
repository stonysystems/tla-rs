//! Passive history of direct leader decisions and the causal origin of commit counters.
//! Records describe actual AdvanceCommit steps; no action reads the history.
use vstd::prelude::*;
use super::etcd::{*,sub};
use super::etcd_election as election;
use super::etcd_origins as origins;
use super::etcd_logs as logs;
use super::etcd_order as order;
use super::etcd_acknowledgments as acks;
use super::temporal::Behavior;
verus! {
pub struct Decision { pub leader: int,pub term: nat,pub log: Seq<nat>,pub quorum: Set<int> }
pub struct ProofState { pub logs: logs::ProofState,pub decisions: Set<Decision> }
pub open spec fn state(g: ProofState) -> LState { g.logs.state }
pub open spec fn record(s: LState,c: Constants,i: int,k: nat) -> Decision {
    Decision { leader: i,term: s.nodes[i].term,log: sub(s.nodes[i].log,1,k as int),
        quorum: c.voters.filter(|j: int| s.nodes[i].matched[j] >= k) }
}
pub open spec fn has_commit(g: ProofState,t: nat,k: nat) -> bool {
    k == 0 || exists |d: Decision| g.decisions.contains(d) && d.term <= t && d.log.len() >= k
}
pub open spec fn decision_valid(g: ProofState,c: Constants,d: Decision) -> bool {
    d.log.len() > 0 && d.log.last() == d.term && d.term > 0 && quorum(d.quorum,c)
    && order::ordered(d.log) && order::bounded(d.log,d.term)
    && origins::owner(state(g),c,d.term,d.log.len() as int,d.leader)
    && logs::represented(g.logs,d.log)
}
pub open spec fn node(g: ProofState,i: int) -> bool {
    has_commit(g,state(g).nodes[i].term,state(g).nodes[i].commit)
    && has_commit(g,state(g).nodes[i].disk.term,state(g).nodes[i].disk.commit)
}
pub open spec fn message(g: ProofState,m: Message) -> bool {
    match m.body { Body::AppendRequest { commit,.. } => has_commit(g,m.term,commit),_ => true }
}
pub open spec fn inductive(g: ProofState,c: Constants) -> bool {
    acks::inductive(state(g),c) && logs::inductive(g.logs,c)
    && (forall |d: Decision| g.decisions.contains(d) ==> #[trigger] decision_valid(g,c,d))
    && (forall |i: int| c.servers.contains(i) ==> #[trigger] node(g,i))
    && (forall |m: Message| #[trigger] state(g).pending.count(m) > 0 ==> message(g,m))
    && (forall |m: Message| #[trigger] state(g).messages.count(m) > 0 ==> message(g,m))
}
pub open spec fn initial_proof(c: Constants) -> ProofState {
    ProofState { logs: logs::initial_proof(c),decisions: Set::empty() }
}
pub open spec fn advance(g: ProofState,c: Constants,a: Action) -> ProofState {
    let s=state(g); let u=apply(s,c,a);
    ProofState { logs: logs::advance(g.logs,c,a),decisions: match a {
        Action::AdvanceCommit(i) => if u.nodes[i].commit > s.nodes[i].commit { g.decisions.insert(record(s,c,i,u.nodes[i].commit)) } else { g.decisions },
        _ => g.decisions,
    } }
}
pub proof fn initial_inductive(c: Constants)
    requires valid_constants(c)
    ensures inductive(initial_proof(c),c)
{
    acks::initial_inductive(c); logs::initial_inductive(c);
    broadcast use vstd::multiset::group_multiset_axioms;
}
pub proof fn commit_monotone(g: ProofState,u: ProofState,t: nat,k: nat,t2: nat,k2: nat)
    requires g.decisions.subset_of(u.decisions),has_commit(g,t,k),t <= t2,k2 <= k
    ensures has_commit(u,t2,k2)
{
    if k2 > 0 {
        let d=choose |d: Decision| g.decisions.contains(d) && d.term <= t && d.log.len() >= k;
        assert(u.decisions.contains(d));
    }
}
pub proof fn new_decision(g: ProofState,c: Constants,i: int)
    requires inductive(g,c),enabled(state(g),c,Action::AdvanceCommit(i)),
        apply(state(g),c,Action::AdvanceCommit(i)).nodes[i].commit > state(g).nodes[i].commit
    ensures decision_valid(advance(g,c,Action::AdvanceCommit(i)),c,record(state(g),c,i,apply(state(g),c,Action::AdvanceCommit(i)).nodes[i].commit))
{
    let s=state(g); let a=Action::AdvanceCommit(i); let u=advance(g,c,a); let n=s.nodes[i];
    reveal(enabled); reveal(apply); let k=state(u).nodes[i].commit; let agreed=agreed_indices(n,c);
    assert(!agreed.is_empty()); origins::maximum_correct(agreed);
    assert(k == maximum(agreed)); assert(1 <= k <= n.log.len()); assert(n.log[k-1] == n.term);
    let d=record(s,c,i,k); assert(quorum(d.quorum,c));
    assert(order::node_order(n)); origins::leader_persisted(s,c,i);
    assert(origins::owner(s,c,n.term,k as int,i)); origins::preserve_owner(s,c,a,n.term,k as int,i);
    let h=logs::representing(g.logs,n.log);
    assert(logs::prefix_of(d.log,n.log)); logs::prefix_transitive(d.log,n.log,h);
    assert(u.logs.created.contains(h));
    assert(order::ordered(d.log)); assert(order::bounded(d.log,d.term));
}
pub proof fn preserve_decision(g: ProofState,c: Constants,a: Action,d: Decision)
    requires inductive(g,c),enabled(state(g),c,a),advance(g,c,a).decisions.contains(d)
    ensures decision_valid(advance(g,c,a),c,d)
{
    let s=state(g); let u=advance(g,c,a);
    if g.decisions.contains(d) {
        assert(decision_valid(g,c,d)); origins::preserve_owner(s,c,a,d.term,d.log.len() as int,d.leader);
        let h=logs::representing(g.logs,d.log); assert(u.logs.created.contains(h));
    } else if let Action::AdvanceCommit(i) = a { new_decision(g,c,i); }
}
pub proof fn preserve_node(g: ProofState,c: Constants,a: Action,i: int)
    requires inductive(g,c),enabled(state(g),c,a),c.servers.contains(i)
    ensures node(advance(g,c,a),i)
{
    let s=state(g); let u=advance(g,c,a); let n=s.nodes[i]; let v=state(u).nodes[i];
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    assert(node(g,i)); assert(g.decisions.subset_of(u.decisions)); assert(election::node_inv(s,c,i));
    if a == Action::Restart(i) {
        commit_monotone(g,u,n.disk.term,n.disk.commit,v.term,v.commit);
    } else if a == Action::AdvanceCommit(i) && v.commit > n.commit {
        let d=record(s,c,i,v.commit); assert(u.decisions.contains(d));
        assert(!agreed_indices(n,c).is_empty()); origins::maximum_correct(agreed_indices(n,c));
        assert(d.log.len() == v.commit); assert(has_commit(u,v.term,v.commit));
    } else if let Action::Receive { m,how } = a {
        assert(message(g,m));
        if how == Receive::AppendDone && m.dest == i && v.commit > n.commit {
            let commit=m.body->AppendRequest_commit;
            commit_monotone(g,u,m.term,commit,v.term,v.commit);
        } else { commit_monotone(g,u,n.term,n.commit,v.term,v.commit); }
    } else { commit_monotone(g,u,n.term,n.commit,v.term,v.commit); }
    if a == Action::Ready(i) { commit_monotone(g,u,n.term,n.commit,v.disk.term,v.disk.commit); }
    else { commit_monotone(g,u,n.disk.term,n.disk.commit,v.disk.term,v.disk.commit); }
}
pub proof fn preserve_message(g: ProofState,c: Constants,a: Action,m: Message)
    requires inductive(g,c),enabled(state(g),c,a),state(advance(g,c,a)).pending.count(m) > 0 || state(advance(g,c,a)).messages.count(m) > 0
    ensures message(advance(g,c,a),m)
{
    let s=state(g); let u=advance(g,c,a);
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    assert(g.decisions.subset_of(u.decisions));
    if let Body::AppendRequest { commit,.. } = m.body {
        if s.pending.count(m) > 0 || s.messages.count(m) > 0 {
            assert(message(g,m)); commit_monotone(g,u,m.term,commit,m.term,commit);
        } else {
            assert(node(g,m.source)); let n=s.nodes[m.source];
            commit_monotone(g,u,n.term,n.commit,m.term,commit);
        }
    }
}
pub proof fn preserve(g: ProofState,c: Constants,a: Action)
    requires inductive(g,c),enabled(state(g),c,a)
    ensures inductive(advance(g,c,a),c)
{
    acks::preserve(state(g),c,a); logs::preserve_inductive(g.logs,c,a); let u=advance(g,c,a);
    assert forall |d: Decision| u.decisions.contains(d) implies #[trigger] decision_valid(u,c,d) by { preserve_decision(g,c,a,d); }
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u,i) by { preserve_node(g,c,a,i); }
    assert forall |m: Message| #[trigger] state(u).pending.count(m) > 0 implies message(u,m) by { preserve_message(g,c,a,m); }
    assert forall |m: Message| #[trigger] state(u).messages.count(m) > 0 implies message(u,m) by { preserve_message(g,c,a,m); }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,k: int) -> (g: ProofState)
    requires election::safety_spec(b,c),k >= 0
    ensures state(g) == b[k],inductive(g,c)
    decreases k
{
    if k == 0 { initial_inductive(c); initial_proof(c) }
    else {
        let old=safety_at(b,c,k-1); let i=k-1; assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        preserve(old,c,a); advance(old,c,a)
    }
}
} // verus!
