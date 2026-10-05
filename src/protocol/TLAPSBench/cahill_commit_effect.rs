//! Exactly one action can add a committed transaction to the history.
use vstd::prelude::*;
use super::cahill::*;
use super::cahill_history as history;
use super::cahill_support as support;
verus! {
pub open spec fn added(s: LState,a: Action) -> Option<int> {
    match a { Action::Commit(t) => if s.txns[t].incoming && s.txns[t].outgoing { None } else { Some(t) },_ => None }
}
pub proof fn summary(s: LState,c: Constants,a: Action)
    requires support::inductive(s,c),enabled(s,c,a)
    ensures committed(apply(s,c,a).history) == match added(s,a) { Some(t) => committed(s.history).insert(t),None => committed(s.history) },
        added(s,a) is Some ==> c.txns.contains(added(s,a).unwrap()) && public(s,added(s,a).unwrap())
{
    reveal(enabled); reveal(apply); reveal(commit); reveal(read); reveal(acquire);
    match a {
        Action::Begin(t) => { history::append(s.history,Event { txn: t,op: Op::Begin }); },
        Action::Abort(t) => { history::append(s.history,Event { txn: t,op: Op::Abort(Reason::Voluntary) }); },
        Action::Commit(t) => {
            support::finite_losers(s,c,t); history::commit_batch(s.history,t,losers(s,c,t));
            history::append(s.history,Event { txn: t,op: Op::Abort(Reason::CommitConflict) });
        },
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
            history::append(s.history,Event { txn: t,op: Op::Write(k) }); history::append(s.history,Event { txn: t,op: Op::Abort(Reason::WriteConflict) });
            history::append(s.history,Event { txn: t,op: Op::Abort(Reason::FirstCommitter) }); history::append(s.history,Event { txn: v,op: Op::Abort(Reason::Deadlock) });
        },
        _ => {},
    }
}
pub proof fn keys_unchanged(s: LState,c: Constants,a: Action,t: int,read: bool)
    requires added(s,a) is Some
    ensures keys(apply(s,c,a).history,t,read) == keys(s.history,t,read)
{
    reveal(apply); reveal(commit);
    if let Action::Commit(w)=a {
        let e=Event { txn: w,op: Op::Commit }; super::cahill_keys::append(s.history,e,t,read);
        super::cahill_keys::batch(s.history.push(e),losers(s,c,w),t,read);
    }
}
} // verus!
