//! Locks and waiters belong to finite active histories even with infinite identifier domains.
use vstd::prelude::*;
use super::cahill::*;
use super::cahill_history as history;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures, vstd::set::Set::lemma_map_contains };
pub open spec fn node(s: LState,c: Constants,t: int) -> bool {
    let n=s.txns[t];
    (n.waiting is Some ==> active(s.history).contains(t) && c.keys.contains(n.waiting.unwrap()))
    && (!n.xlocks.is_empty() ==> active(s.history).contains(t))
    && (!n.siread.is_empty() ==> all(s.history).contains(t) && !aborted(s.history).contains(t))
    && n.xlocks.to_iset().subset_of(c.keys) && n.siread.to_iset().subset_of(c.keys)
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    s.txns.dom() == c.txns && all(s.history).to_iset().subset_of(c.txns)
    && forall |t: int| c.txns.contains(t) ==> #[trigger] node(s,c,t)
}
pub open spec fn waiting_set(s: LState,c: Constants) -> ISet<int> { c.txns.filter(|r: int| s.txns[r].waiting is Some) }
pub open spec fn loser_set(s: LState,c: Constants,t: int) -> ISet<int> {
    c.txns.filter(|r: int| s.txns[r].waiting is Some && s.txns[t].xlocks.contains(s.txns[r].waiting.unwrap()))
}
pub proof fn finite_losers(s: LState,c: Constants,t: int)
    requires inductive(s,c),c.txns.contains(t)
    ensures waiting_set(s,c).finite(),loser_set(s,c,t).finite(),loser_set(s,c,t).to_set() is Some,
        losers(s,c,t).to_iset() =~= loser_set(s,c,t),losers(s,c,t).subset_of(active(s.history)),public(s,t) ==> !losers(s,c,t).contains(t)
{
    let a=active(s.history).to_iset();
    assert(waiting_set(s,c).subset_of(a)) by { assert forall |r: int| waiting_set(s,c).contains(r) implies a.contains(r) by { assert(node(s,c,r)); } }
    vstd::iset_lib::lemma_iset_subset_finite(a,waiting_set(s,c));
    assert(loser_set(s,c,t).subset_of(waiting_set(s,c))); vstd::iset_lib::lemma_iset_subset_finite(waiting_set(s,c),loser_set(s,c,t));
}
pub proof fn initial_inductive(c: Constants)
    ensures inductive(initial(c),c)
{
    assert(initial(c).txns.dom() =~= c.txns);
    assert forall |r: int| c.txns.contains(r) implies #[trigger] node(initial(c),c,r) by {}
    assert(initial(c).history.to_set() =~= Set::<Event>::empty()); assert(all(initial(c).history) =~= Set::<int>::empty());
}
pub proof fn victim_active(s: LState,c: Constants,t: int,k: int,v: int)
    requires deadlocked(s,c,t,k),deadlock_victim(s,c,t,k,v)
    ensures active(s.history).contains(v)
{
    let p=choose |p: Seq<int>| deadlock_path(s,c,t,k,p); let at=choose |at: int| 0 <= at < p.len() && p[at] == v;
    if at < p.len()-1 { assert(wait_edge(s,c,t,k,p[at],p[at+1])); }
    else { assert(p[at] == p.last()); }
}
pub proof fn abort_preserves(s: LState,c: Constants,t: int,reason: Reason)
    requires inductive(s,c),c.txns.contains(t)
    ensures inductive(abort(s,t,reason),c)
{
    history::append(s.history,Event { txn: t,op: Op::Abort(reason) }); let u=abort(s,t,reason);
    assert forall |r: int| c.txns.contains(r) implies #[trigger] node(u,c,r) by { assert(node(s,c,r)); }
    assert(u.txns.dom() =~= c.txns); assert(all(u.history).to_iset().subset_of(c.txns));
}
pub proof fn acquire_preserves(s: LState,c: Constants,t: int,k: int)
    requires inductive(s,c),c.txns.contains(t),active(s.history).contains(t),c.keys.contains(k)
    ensures inductive(acquire(s,c,t,k),c)
{
    reveal(acquire); history::append(s.history,Event { txn: t,op: Op::Write(k) }); abort_preserves(s,c,t,Reason::WriteConflict); let u=acquire(s,c,t,k);
    assert forall |r: int| c.txns.contains(r) implies #[trigger] node(u,c,r) by { assert(node(s,c,r)); }
    assert(u.txns.dom() =~= c.txns); assert(all(u.history).to_iset().subset_of(c.txns));
}
pub proof fn commit_preserves(s: LState,c: Constants,t: int)
    requires inductive(s,c),c.txns.contains(t),public(s,t)
    ensures inductive(commit(s,c,t),c)
{
    reveal(commit); finite_losers(s,c,t); history::commit_batch(s.history,t,losers(s,c,t)); abort_preserves(s,c,t,Reason::CommitConflict); let u=commit(s,c,t);
    assert forall |r: int| c.txns.contains(r) implies #[trigger] node(u,c,r) by { assert(node(s,c,r)); }
    assert(u.txns.dom() =~= c.txns); assert(all(u.history).to_iset().subset_of(c.txns));
}
pub proof fn read_preserves(s: LState,c: Constants,t: int,k: int)
    requires inductive(s,c),c.txns.contains(t),active(s.history).contains(t),c.keys.contains(k),!version(s,t,k).is_empty()
    ensures inductive(read(s,c,t,k),c)
{
    reveal(read); let v=choose |v: int| version(s,t,k).contains(v);
    history::append(s.history,Event { txn: t,op: Op::Read { key: k,version: v } }); abort_preserves(s,c,t,Reason::ReadConflict); let u=read(s,c,t,k);
    assert forall |r: int| c.txns.contains(r) implies #[trigger] node(u,c,r) by { assert(node(s,c,r)); }
    assert(u.txns.dom() =~= c.txns); assert(all(u.history).to_iset().subset_of(c.txns));
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    reveal(enabled); reveal(apply); let u=apply(s,c,a);
    match a {
        Action::Stutter => {},
        Action::Begin(t) => { history::append(s.history,Event { txn: t,op: Op::Begin }); assert forall |r: int| c.txns.contains(r) implies #[trigger] node(u,c,r) by { assert(node(s,c,r)); } },
        Action::Commit(t) => { commit_preserves(s,c,t); },
        Action::Abort(t) => { abort_preserves(s,c,t,Reason::Voluntary); },
        Action::Read(t,k) => { read_preserves(s,c,t,k); },
        Action::Finish(t) => { assert(node(s,c,t)); acquire_preserves(s,c,t,s.txns[t].waiting.unwrap()); },
        Action::Write { txn: t,key: k,victim: v } => {
            if !writers_since(s,t,k).is_empty() { abort_preserves(s,c,t,Reason::FirstCommitter); }
            else if !locked(s,c,k) { acquire_preserves(s,c,t,k); }
            else if !deadlocked(s,c,t,k) { assert forall |r: int| c.txns.contains(r) implies #[trigger] node(u,c,r) by { assert(node(s,c,r)); } }
            else {
                victim_active(s,c,t,k,v); assert(c.txns.contains(v)); abort_preserves(s,c,v,Reason::Deadlock);
                history::append(s.history,Event { txn: v,op: Op::Abort(Reason::Deadlock) });
                assert forall |r: int| c.txns.contains(r) implies #[trigger] node(u,c,r) by { assert(node(s,c,r)); }
            }
        },
    }
    assert(u.txns.dom() =~= c.txns); assert(all(u.history).to_iset().subset_of(c.txns));
    assert forall |r: int| c.txns.contains(r) implies #[trigger] node(u,c,r) by {
        assert(node(s,c,r));
        if let Action::Write { txn: t,key: k,victim: v }=a {
            if !writers_since(s,t,k).is_empty() { assert(node(abort(s,t,Reason::FirstCommitter),c,r)); }
        }
    }
}
pub open spec fn safety_spec(b: Behavior<LState>,c: Constants) -> bool {
    b[0] == initial(c) && (forall |time: int| time >= 0 ==> b.dom().contains(time))
    && forall |time: int| time >= 0 ==> #[trigger] next(b[time],b[time+1],c)
}
pub proof fn step(b: Behavior<LState>,c: Constants,time: int) -> (a: Action)
    requires safety_spec(b,c),time >= 0
    ensures enabled(b[time],c,a),b[time+1] == apply(b[time],c,a)
{
    assert(next(b[time],b[time+1],c)); reveal(next); choose |a: Action| #[trigger] enabled(b[time],c,a) && b[time+1] == apply(b[time],c,a)
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires safety_spec(b,c),time >= 0
    ensures inductive(b[time],c)
    decreases time
{
    if time == 0 { initial_inductive(c); }
    else { at(b,c,time-1); let a=step(b,c,time-1); preserve(b[time-1],c,a); }
}
pub proof fn finite_abort_set(b: Behavior<LState>,c: Constants,time: int,t: int)
    requires safety_spec(b,c),time >= 0,c.txns.contains(t)
    ensures loser_set(b[time],c,t).finite(),loser_set(b[time],c,t).to_set() is Some,
        losers(b[time],c,t).to_iset() =~= loser_set(b[time],c,t)
{
    at(b,c,time); finite_losers(b[time],c,t);
}
} // verus!
