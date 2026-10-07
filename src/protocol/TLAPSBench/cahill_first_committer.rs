//! A held or awaited write lock has no committed writer since the transaction began.
use vstd::prelude::*;
use super::cahill::*;
use super::cahill_history as history;
use super::cahill_keys as keys_math;
use super::cahill_support as support;
use super::cahill_records as records;
use super::cahill_locks as locks;
use super::cahill_lifecycle as lifecycle;
use super::cahill_history_order as order;
use super::cahill_recent as recent;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures, vstd::set::Set::lemma_map_contains };
pub open spec fn protected(s: LState,t: int,k: int) -> bool { s.txns[t].xlocks.contains(k) || s.txns[t].waiting == Some(k) }
pub open spec fn safe(s: LState,c: Constants) -> bool {
    forall |t: int,k: int| c.txns.contains(t) && #[trigger] protected(s,t,k) ==> writers_since(s,t,k).is_empty()
}
pub proof fn commit_safe(s: LState,c: Constants,t: int)
    requires support::inductive(s,c),records::exact(s,c),locks::exclusive(s,c),lifecycle::valid(s.history),safe(s,c),c.txns.contains(t),public(s,t)
    ensures safe(commit(s,c,t),c)
{
    reveal(commit); let u=commit(s,c,t); let q=losers(s,c,t); let e=Event { txn: t,op: Op::Commit };
    support::finite_losers(s,c,t); history::commit_batch(s.history,t,q); history::append(s.history,Event { txn: t,op: Op::Abort(Reason::CommitConflict) });
    reveal(enabled); assert(enabled(s,c,Action::Commit(t))); lifecycle::preserve(s,c,Action::Commit(t));
    order::step_prefix(s,c,Action::Commit(t)); reveal(apply);
    assert(records::node(s,t)); keys_math::append(s.history,e,t,false); keys_math::batch(s.history.push(e),q,t,false);
    assert forall |r: int,k: int| c.txns.contains(r) && #[trigger] protected(u,r,k) implies writers_since(u,r,k).is_empty() by {
        assert(support::node(s,c,r)); assert(protected(s,r,k));
        if s.txns[t].incoming && s.txns[t].outgoing { recent::unchanged(s,u,r,k); }
        else {
            recent::new_committer(s,u,r,k,t);
            if keys(s.history,t,false).contains(k) {
                assert(s.txns[t].xlocks.contains(k));
                if s.txns[r].waiting == Some(k) { assert(q.contains(r)); }
                else { assert(s.txns[r].xlocks.contains(k)); assert(r == t); }
            }
        }
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::inductive(s,c),records::exact(s,c),locks::exclusive(s,c),lifecycle::valid(s.history),safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    let u=apply(s,c,a); lifecycle::preserve(s,c,a); order::step_prefix(s,c,a);
    reveal(enabled); reveal(apply); reveal(read); reveal(acquire);
    match a {
        Action::Commit(t) => { commit_safe(s,c,t); },
        _ => {
            match a {
                Action::Begin(t) => { history::append(s.history,Event { txn: t,op: Op::Begin }); },
                Action::Abort(t) => { history::append(s.history,Event { txn: t,op: Op::Abort(Reason::Voluntary) }); },
                Action::Read(t,k) => {
                    let v=choose |v: int| version(s,t,k).contains(v);
                    history::append(s.history,Event { txn: t,op: Op::Read { key: k,version: v } });
                    history::append(s.history,Event { txn: t,op: Op::Abort(Reason::ReadConflict) });
                },
                Action::Finish(t) => {
                    let k=s.txns[t].waiting.unwrap(); history::append(s.history,Event { txn: t,op: Op::Write(k) });
                    history::append(s.history,Event { txn: t,op: Op::Abort(Reason::WriteConflict) });
                },
                Action::Write { txn: t,key: k,victim: v } => {
                    history::append(s.history,Event { txn: t,op: Op::Write(k) });
                    history::append(s.history,Event { txn: t,op: Op::Abort(Reason::WriteConflict) });
                    history::append(s.history,Event { txn: t,op: Op::Abort(Reason::FirstCommitter) });
                    history::append(s.history,Event { txn: v,op: Op::Abort(Reason::Deadlock) });
                },
                _ => {},
            }
            assert(committed(u.history) == committed(s.history));
            assert forall |r: int,k: int| c.txns.contains(r) && #[trigger] protected(u,r,k) implies writers_since(u,r,k).is_empty() by {
                assert(support::node(s,c,r));
                match a {
                    Action::Begin(t) => { assert(r != t); },
                    Action::Finish(t) => { if r == t { assert(protected(s,t,k)); } },
                    Action::Write { txn: t,key: key,victim: v } => {
                        if r == t && !protected(s,r,k) { assert(k == key && writers_since(s,t,k).is_empty()); }
                    },
                    _ => {},
                }
                assert(protected(s,r,k) || writers_since(s,r,k).is_empty());
                assert(all(s.history).contains(r)); assert(writers_since(s,r,k).is_empty()); recent::unchanged(s,u,r,k);
            }
        },
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires support::safety_spec(b,c),time >= 0
    ensures safe(b[time],c)
    decreases time
{
    if time > 0 {
        at(b,c,time-1); support::at(b,c,time-1); records::at(b,c,time-1); locks::at(b,c,time-1); lifecycle::at(b,c,time-1);
        let a=support::step(b,c,time-1); preserve(b[time-1],c,a);
    }
}
} // verus!
