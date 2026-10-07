//! Locks precisely record successful accesses until their specified release.
use vstd::prelude::*;
use super::cahill::*;
use super::cahill_history as history;
use super::cahill_keys as keys_math;
use super::cahill_support as support;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures, vstd::set::Set::lemma_map_contains };
pub open spec fn node(s: LState,t: int) -> bool {
    s.txns[t].xlocks == (if active(s.history).contains(t) { keys(s.history,t,false) } else { Set::empty() })
    && s.txns[t].siread == (if aborted(s.history).contains(t) { Set::empty() } else { keys(s.history,t,true) })
}
pub open spec fn exact(s: LState,c: Constants) -> bool {
    forall |t: int| c.txns.contains(t) ==> #[trigger] node(s,t)
}
pub proof fn abort_exact(s: LState,c: Constants,t: int,reason: Reason)
    requires exact(s,c)
    ensures exact(abort(s,t,reason),c)
{
    let e=Event { txn: t,op: Op::Abort(reason) }; history::append(s.history,e); let u=abort(s,t,reason);
    assert forall |r: int| c.txns.contains(r) implies #[trigger] node(u,r) by {
        assert(node(s,r)); keys_math::append(s.history,e,r,true); keys_math::append(s.history,e,r,false);
    }
}
pub proof fn acquire_exact(s: LState,c: Constants,t: int,k: int)
    requires exact(s,c),active(s.history).contains(t)
    ensures exact(acquire(s,c,t,k),c)
{
    reveal(acquire); let e=Event { txn: t,op: Op::Write(k) }; history::append(s.history,e);
    abort_exact(s,c,t,Reason::WriteConflict); let u=acquire(s,c,t,k);
    assert forall |r: int| c.txns.contains(r) implies #[trigger] node(u,r) by {
        assert(node(s,r)); keys_math::append(s.history,e,r,true); keys_math::append(s.history,e,r,false);
    }
}
pub proof fn read_exact(s: LState,c: Constants,t: int,k: int)
    requires exact(s,c),active(s.history).contains(t),!version(s,t,k).is_empty()
    ensures exact(read(s,c,t,k),c)
{
    reveal(read); let v=choose |v: int| version(s,t,k).contains(v);
    let e=Event { txn: t,op: Op::Read { key: k,version: v } }; history::append(s.history,e);
    abort_exact(s,c,t,Reason::ReadConflict); let u=read(s,c,t,k);
    assert forall |r: int| c.txns.contains(r) implies #[trigger] node(u,r) by {
        assert(node(s,r)); keys_math::append(s.history,e,r,true); keys_math::append(s.history,e,r,false);
    }
}
pub proof fn commit_exact(s: LState,c: Constants,t: int)
    requires support::inductive(s,c),exact(s,c),c.txns.contains(t),public(s,t)
    ensures exact(commit(s,c,t),c)
{
    reveal(commit); support::finite_losers(s,c,t); history::commit_batch(s.history,t,losers(s,c,t));
    abort_exact(s,c,t,Reason::CommitConflict); let u=commit(s,c,t); let e=Event { txn: t,op: Op::Commit };
    assert forall |r: int| c.txns.contains(r) implies #[trigger] node(u,r) by {
        assert(node(s,r)); keys_math::append(s.history,e,r,true); keys_math::append(s.history,e,r,false);
        keys_math::batch(s.history.push(e),losers(s,c,t),r,true); keys_math::batch(s.history.push(e),losers(s,c,t),r,false);
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::inductive(s,c),exact(s,c),enabled(s,c,a)
    ensures exact(apply(s,c,a),c)
{
    reveal(enabled); reveal(apply); let u=apply(s,c,a);
    match a {
        Action::Stutter => {},
        Action::Begin(t) => {
            let e=Event { txn: t,op: Op::Begin }; history::append(s.history,e);
            assert forall |r: int| c.txns.contains(r) implies #[trigger] node(u,r) by {
                assert(node(s,r)); keys_math::append(s.history,e,r,true); keys_math::append(s.history,e,r,false);
                if r == t { keys_math::absent(s.history,t,false); }
            }
        },
        Action::Commit(t) => { commit_exact(s,c,t); },
        Action::Abort(t) => { abort_exact(s,c,t,Reason::Voluntary); },
        Action::Read(t,k) => { read_exact(s,c,t,k); },
        Action::Finish(t) => { assert(support::node(s,c,t)); acquire_exact(s,c,t,s.txns[t].waiting.unwrap()); },
        Action::Write { txn: t,key: k,victim: v } => {
            if !writers_since(s,t,k).is_empty() { abort_exact(s,c,t,Reason::FirstCommitter); }
            else if !locked(s,c,k) { acquire_exact(s,c,t,k); }
            else if !deadlocked(s,c,t,k) {}
            else { abort_exact(s,c,v,Reason::Deadlock); }
        },
    }
    assert forall |r: int| c.txns.contains(r) implies #[trigger] node(u,r) by {
        assert(node(s,r));
        if let Action::Write { txn: t,key: k,victim: v }=a {
            if !writers_since(s,t,k).is_empty() { assert(node(abort(s,t,Reason::FirstCommitter),r)); }
            else if locked(s,c,k) && deadlocked(s,c,t,k) { assert(node(abort(s,v,Reason::Deadlock),r)); }
        }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires support::safety_spec(b,c),time >= 0
    ensures exact(b[time],c)
    decreases time
{
    if time == 0 {
        let h=b[0].history; assert(h.to_set() =~= Set::<Event>::empty());
        assert forall |r: int| c.txns.contains(r) implies #[trigger] node(b[0],r) by {
            keys_math::absent(h,r,true); keys_math::absent(h,r,false);
        }
    } else { at(b,c,time-1); support::at(b,c,time-1); let a=support::step(b,c,time-1); preserve(b[time-1],c,a); }
}
} // verus!
