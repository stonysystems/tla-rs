//! A committed transaction cannot acquire both conflict flags, even after commit.
use vstd::prelude::*;
use super::cahill::*;
use super::cahill_history as history;
use super::cahill_support as support;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures, vstd::set::Set::lemma_map_contains };
pub open spec fn safe(s: LState,c: Constants) -> bool {
    forall |t: int| c.txns.contains(t) && committed(s.history).contains(t)
        ==> !(#[trigger] s.txns[t].incoming && s.txns[t].outgoing)
}
pub proof fn abort_safe(s: LState,c: Constants,t: int,reason: Reason)
    requires safe(s,c)
    ensures safe(abort(s,t,reason),c)
{
    history::append(s.history,Event { txn: t,op: Op::Abort(reason) });
}
pub proof fn read_safe(s: LState,c: Constants,t: int,k: int)
    requires support::inductive(s,c),safe(s,c),c.txns.contains(t),active(s.history).contains(t),!version(s,t,k).is_empty()
    ensures safe(read(s,c,t,k),c)
{
    reveal(read); let v=choose |v: int| version(s,t,k).contains(v);
    history::append(s.history,Event { txn: t,op: Op::Read { key: k,version: v } });
    abort_safe(s,c,t,Reason::ReadConflict);
    let u=read(s,c,t,k);
    assert forall |r: int| c.txns.contains(r) && committed(u.history).contains(r)
        implies !(#[trigger] u.txns[r].incoming && u.txns[r].outgoing) by {
        assert(support::node(s,c,r));
        if newer_versions(s,t,k).contains(r) && s.txns[r].outgoing {
            assert(exists |w: int| newer_versions(s,t,k).contains(w) && committed(s.history).contains(w) && s.txns[w].outgoing);
        }
    }
}
pub proof fn acquire_safe(s: LState,c: Constants,t: int,k: int)
    requires safe(s,c),c.txns.contains(t),active(s.history).contains(t)
    ensures safe(acquire(s,c,t,k),c)
{
    reveal(acquire); history::append(s.history,Event { txn: t,op: Op::Write(k) });
    abort_safe(s,c,t,Reason::WriteConflict);
    let u=acquire(s,c,t,k);
    assert forall |r: int| c.txns.contains(r) && committed(u.history).contains(r)
        implies !(#[trigger] u.txns[r].incoming && u.txns[r].outgoing) by {
        if concurrent_readers(s,c,t,k).contains(r) {
            assert(exists |r: int| concurrent_readers(s,c,t,k).contains(r) && (committed(s.history).contains(r) || s.txns[r].incoming));
        }
    }
}
pub proof fn commit_safe(s: LState,c: Constants,t: int)
    requires support::inductive(s,c),safe(s,c),c.txns.contains(t),public(s,t)
    ensures safe(commit(s,c,t),c)
{
    reveal(commit); support::finite_losers(s,c,t); history::commit_batch(s.history,t,losers(s,c,t));
    abort_safe(s,c,t,Reason::CommitConflict);
    let u=commit(s,c,t);
    assert forall |r: int| c.txns.contains(r) && committed(u.history).contains(r)
        implies !(#[trigger] u.txns[r].incoming && u.txns[r].outgoing) by {}
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::inductive(s,c),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    reveal(enabled); reveal(apply);
    match a {
        Action::Stutter => {},
        Action::Begin(t) => { history::append(s.history,Event { txn: t,op: Op::Begin }); },
        Action::Commit(t) => { commit_safe(s,c,t); },
        Action::Abort(t) => { abort_safe(s,c,t,Reason::Voluntary); },
        Action::Read(t,k) => { read_safe(s,c,t,k); },
        Action::Finish(t) => { assert(support::node(s,c,t)); acquire_safe(s,c,t,s.txns[t].waiting.unwrap()); },
        Action::Write { txn: t,key: k,victim: v } => {
            if !writers_since(s,t,k).is_empty() { abort_safe(s,c,t,Reason::FirstCommitter); }
            else if !locked(s,c,k) { acquire_safe(s,c,t,k); }
            else if !deadlocked(s,c,t,k) {}
            else { abort_safe(s,c,v,Reason::Deadlock); }
        },
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires support::safety_spec(b,c),time >= 0
    ensures safe(b[time],c)
    decreases time
{
    if time == 0 { assert(b[time].history.to_set() =~= Set::<Event>::empty()); }
    else { at(b,c,time-1); support::at(b,c,time-1); let a=support::step(b,c,time-1); preserve(b[time-1],c,a); }
}
} // verus!
