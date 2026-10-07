//! Conflict flags persist for transactions that have not aborted.
use vstd::prelude::*;
use super::cahill::*;
use super::cahill_history as history;
use super::cahill_support as support;
verus! {
broadcast use { vstd::imap::group_imap_lemmas, vstd::iset_lib::group_iset_lib_default, vstd::set_lib::group_set_lib_default };
pub open spec fn node(s: LState,u: LState,t: int) -> bool {
    !aborted(u.history).contains(t) ==> (s.txns[t].incoming ==> u.txns[t].incoming) && (s.txns[t].outgoing ==> u.txns[t].outgoing)
}
pub open spec fn retained(s: LState,u: LState,c: Constants) -> bool {
    forall |t: int| c.txns.contains(t) ==> #[trigger] node(s,u,t)
}
pub proof fn abort_retained(s: LState,c: Constants,t: int,reason: Reason)
    ensures retained(s,abort(s,t,reason),c)
{
    history::append(s.history,Event { txn: t,op: Op::Abort(reason) });
}
pub proof fn acquire_retained(s: LState,c: Constants,t: int,k: int)
    ensures retained(s,acquire(s,c,t,k),c)
{
    reveal(acquire); abort_retained(s,c,t,Reason::WriteConflict);
}
pub proof fn read_retained(s: LState,c: Constants,t: int,k: int)
    ensures retained(s,read(s,c,t,k),c)
{
    reveal(read); abort_retained(s,c,t,Reason::ReadConflict);
}
pub proof fn commit_retained(s: LState,c: Constants,t: int)
    ensures retained(s,commit(s,c,t),c)
{
    reveal(commit); abort_retained(s,c,t,Reason::CommitConflict);
    history::batch(losers(s,c,t)); history::concat(s.history.push(Event { txn: t,op: Op::Commit }),aborts(losers(s,c,t)));
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    ensures retained(s,apply(s,c,a),c)
{
    reveal(apply);
    match a {
        Action::Commit(t) => { commit_retained(s,c,t); },
        Action::Abort(t) => { abort_retained(s,c,t,Reason::Voluntary); },
        Action::Read(t,k) => { read_retained(s,c,t,k); },
        Action::Finish(t) => { acquire_retained(s,c,t,s.txns[t].waiting.unwrap()); },
        Action::Write { txn: t,key: k,victim: v } => {
            abort_retained(s,c,t,Reason::FirstCommitter); acquire_retained(s,c,t,k); abort_retained(s,c,v,Reason::Deadlock);
        },
        _ => {},
    }
    assert forall |r: int| c.txns.contains(r) implies #[trigger] node(s,apply(s,c,a),r) by {
        match a {
            Action::Commit(t) => { assert(node(s,commit(s,c,t),r)); },
            Action::Abort(t) => { assert(node(s,abort(s,t,Reason::Voluntary),r)); },
            Action::Read(t,k) => { assert(node(s,read(s,c,t,k),r)); },
            Action::Finish(t) => { assert(node(s,acquire(s,c,t,s.txns[t].waiting.unwrap()),r)); },
            Action::Write { txn: t,key: k,victim: v } => {
                assert(node(s,abort(s,t,Reason::FirstCommitter),r)); assert(node(s,acquire(s,c,t,k),r)); assert(node(s,abort(s,v,Reason::Deadlock),r));
            },
            _ => {},
        }
    }
}
} // verus!
