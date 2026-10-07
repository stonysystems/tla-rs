//! The reachable wait graph has no pre-existing cycle.
use vstd::prelude::*;
use super::cahill::*;
use super::cahill_support as support;
use super::cahill_history as history;
use super::cahill_locks as locks;
use super::cahill_wait_graph as graph;
use super::cahill_wait_edges::{self as waits,edges,next_wait,waiting};
use super::temporal::Behavior;
verus! {
pub proof fn acquire(s: LState,c: Constants,t: int,k: int)
    requires support::inductive(s,c),locks::exclusive(s,c),graph::acyclic(edges(s,c)),c.txns.contains(t),active(s.history).contains(t),c.keys.contains(k)
    ensures graph::acyclic(edges(super::cahill::acquire(s,c,t,k),c))
{
    support::acquire_preserves(s,c,t,k); let u=super::cahill::acquire(s,c,t,k); reveal(super::cahill::acquire);
    history::append(s.history,Event { txn: t,op: Op::Write(k) }); history::append(s.history,Event { txn: t,op: Op::Abort(Reason::WriteConflict) });
    assert(next_wait(u,c,t) == None);
    assert forall |x: int| #[trigger] next_wait(u,c,x) is Some implies next_wait(s,c,x) == next_wait(u,c,x) || next_wait(u,c,x) == Some(t) by {
        let key=u.txns[x].waiting.unwrap(); let owner=next_wait(u,c,x).unwrap(); waits::owner_member(u,key,owner);
        if owner != t { assert(c.txns.contains(owner)); assert(s.txns[owner].xlocks.contains(key)); locks::owner_correct(s,c,key,owner); }
    }
    graph::sink_extension(edges(s,c),edges(u,c),t);
}
pub proof fn abort_cycle(s: LState,c: Constants,t: int,k: int,v: int)
    requires support::inductive(s,c),locks::exclusive(s,c),graph::acyclic(edges(s,c)),
        enabled(s,c,Action::Write { txn: t,key: k,victim: v }),writers_since(s,t,k).is_empty(),locked(s,c,k),deadlocked(s,c,t,k)
    ensures graph::acyclic(edges(apply(s,c,Action::Write { txn: t,key: k,victim: v }),c))
{
    let a=Action::Write { txn: t,key: k,victim: v }; let u=apply(s,c,a); let d=waiting(s,t,k);
    reveal(enabled); reveal(apply); support::preserve(s,c,a); waits::waiting_support(s,c,t,k); waits::changed(s,c,t,k);
    history::append(s.history,Event { txn: v,op: Op::Abort(Reason::Deadlock) }); support::victim_active(s,c,t,k,v);
    assert(locks::retains(d,u,c));
    assert forall |x: int| #[trigger] next_wait(u,c,x) is Some implies active(d.history).contains(x) && u.txns[x].waiting == d.txns[x].waiting by {}
    waits::retained(d,u,c); assert(next_wait(u,c,v) == None);
    let q=choose |q: Seq<int>| deadlock_path(s,c,t,k,q); waits::path_equivalent(s,c,t,k,q); assert(q.contains(t)); assert(q.contains(v));
    graph::abort_member(edges(s,c),edges(d,c),edges(u,c),t,q,v);
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::inductive(s,c),locks::exclusive(s,c),graph::acyclic(edges(s,c)),enabled(s,c,a)
    ensures graph::acyclic(edges(apply(s,c,a),c))
{
    support::preserve(s,c,a); let u=apply(s,c,a); reveal(enabled); reveal(apply); reveal(commit); reveal(read);
    match a {
        Action::Finish(t) => { assert(support::node(s,c,t)); acquire(s,c,t,s.txns[t].waiting.unwrap()); },
        Action::Write { txn: t,key: k,victim: v } => {
            if !writers_since(s,t,k).is_empty() {
                history::append(s.history,Event { txn: t,op: Op::Abort(Reason::FirstCommitter) }); assert(locks::retains(s,u,c));
                assert forall |x: int| #[trigger] next_wait(u,c,x) is Some implies active(s.history).contains(x) && u.txns[x].waiting == s.txns[x].waiting by {}
                waits::retained(s,u,c); graph::subgraph_acyclic(edges(s,c),edges(u,c));
            } else if !locked(s,c,k) { acquire(s,c,t,k); }
            else if !deadlocked(s,c,t,k) { waits::no_return(s,c,t,k); }
            else { abort_cycle(s,c,t,k,v); }
        },
        _ => {
            match a {
                Action::Begin(t) => { assert(support::node(s,c,t)); history::append(s.history,Event { txn: t,op: Op::Begin }); },
                Action::Abort(t) => { history::append(s.history,Event { txn: t,op: Op::Abort(Reason::Voluntary) }); },
                Action::Commit(t) => { support::finite_losers(s,c,t); history::commit_batch(s.history,t,losers(s,c,t)); history::append(s.history,Event { txn: t,op: Op::Abort(Reason::CommitConflict) }); },
                Action::Read(t,k) => { let v=choose |v: int| version(s,t,k).contains(v); history::append(s.history,Event { txn: t,op: Op::Read { key: k,version: v } }); history::append(s.history,Event { txn: t,op: Op::Abort(Reason::ReadConflict) }); },
                _ => {},
            }
            assert(locks::retains(s,u,c));
            assert forall |x: int| #[trigger] next_wait(u,c,x) is Some implies active(s.history).contains(x) && u.txns[x].waiting == s.txns[x].waiting by {}
            waits::retained(s,u,c); graph::subgraph_acyclic(edges(s,c),edges(u,c));
        },
    }
}
pub proof fn initial_acyclic(c: Constants)
    ensures graph::acyclic(edges(initial(c),c))
{
    assert forall |p: Seq<int>| !#[trigger] graph::cycle(edges(initial(c),c),p) by {
        if graph::cycle(edges(initial(c),c),p) { graph::successor(edges(initial(c),c),p,0); }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires support::safety_spec(b,c),time >= 0
    ensures graph::acyclic(edges(b[time],c))
    decreases time
{
    if time == 0 { initial_acyclic(c); }
    else { at(b,c,time-1); support::at(b,c,time-1); locks::at(b,c,time-1); let a=support::step(b,c,time-1); preserve(b[time-1],c,a); }
}
} // verus!
