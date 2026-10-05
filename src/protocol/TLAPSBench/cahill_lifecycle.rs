//! Every event starts a fresh transaction or belongs to a transaction still active.
use vstd::prelude::*;
use super::cahill::*;
use super::cahill_history as history;
use super::cahill_support as support;
use super::temporal::Behavior;
verus! {
pub open spec fn permitted(h: Seq<Event>,e: Event) -> bool {
    if e.op == Op::Begin { !all(h).contains(e.txn) } else { active(h).contains(e.txn) }
}
pub open spec fn valid(h: Seq<Event>) -> bool
    decreases h.len()
{
    h.len() == 0 || valid(h.drop_last()) && permitted(h.drop_last(),h.last())
}
pub proof fn append(h: Seq<Event>,e: Event)
    requires valid(h),permitted(h,e)
    ensures valid(h.push(e))
{
    assert(h.push(e).drop_last() =~= h); assert(h.push(e).last() == e);
}
pub proof fn abort_batch(h: Seq<Event>,q: Set<int>)
    requires valid(h),q.subset_of(active(h))
    ensures valid(h+aborts(q))
    decreases q.len()
{
    if q.is_empty() { assert(h+aborts(q) =~= h); }
    else {
        let t=choose |t: int| q.contains(t); let e=Event { txn: t,op: Op::Abort(Reason::FirstCommitter) };
        append(h,e); history::append(h,e); assert(q.remove(t).subset_of(active(h.push(e)))); abort_batch(h.push(e),q.remove(t));
        assert(h+aborts(q) =~= h.push(e)+aborts(q.remove(t)));
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::inductive(s,c),valid(s.history),enabled(s,c,a)
    ensures valid(apply(s,c,a).history)
{
    reveal(enabled); reveal(apply); reveal(commit); reveal(read); reveal(acquire);
    match a {
        Action::Stutter => {},
        Action::Begin(t) => { append(s.history,Event { txn: t,op: Op::Begin }); },
        Action::Abort(t) => { append(s.history,Event { txn: t,op: Op::Abort(Reason::Voluntary) }); },
        Action::Commit(t) => {
            append(s.history,Event { txn: t,op: Op::Abort(Reason::CommitConflict) });
            support::finite_losers(s,c,t); let e=Event { txn: t,op: Op::Commit }; append(s.history,e); history::append(s.history,e);
            assert(losers(s,c,t).subset_of(active(s.history.push(e)))); abort_batch(s.history.push(e),losers(s,c,t));
        },
        Action::Read(t,k) => {
            let v=choose |v: int| version(s,t,k).contains(v); append(s.history,Event { txn: t,op: Op::Read { key: k,version: v } });
            append(s.history,Event { txn: t,op: Op::Abort(Reason::ReadConflict) });
        },
        Action::Finish(t) => {
            assert(support::node(s,c,t)); let k=s.txns[t].waiting.unwrap(); append(s.history,Event { txn: t,op: Op::Write(k) });
            append(s.history,Event { txn: t,op: Op::Abort(Reason::WriteConflict) });
        },
        Action::Write { txn: t,key: k,victim: v } => {
            append(s.history,Event { txn: t,op: Op::Abort(Reason::FirstCommitter) }); append(s.history,Event { txn: t,op: Op::Abort(Reason::WriteConflict) });
            append(s.history,Event { txn: t,op: Op::Write(k) });
            if writers_since(s,t,k).is_empty() && locked(s,c,k) && deadlocked(s,c,t,k) {
                support::victim_active(s,c,t,k,v); append(s.history,Event { txn: v,op: Op::Abort(Reason::Deadlock) });
            }
        },
    }
}
pub proof fn prefix_valid(h: Seq<Event>,n: int)
    requires valid(h),0 <= n <= h.len()
    ensures valid(h.take(n))
    decreases h.len()-n
{
    if n == h.len() { assert(h.take(n) =~= h); }
    else { prefix_valid(h.drop_last(),n); assert(h.drop_last().take(n) =~= h.take(n)); }
}
pub proof fn event_member(h: Seq<Event>,k: int)
    requires 0 <= k < h.len()
    ensures all(h).contains(h[k].txn)
{
    h.to_set_ensures(); assert(h.to_set().contains(h[k])); h.to_set().lemma_map_contains(|e: Event| e.txn,h[k].txn);
}
pub proof fn unique_begin(h: Seq<Event>,t: int) -> (at: int)
    requires valid(h),all(h).contains(t)
    ensures 0 <= at < h.len(),h[at] == (Event { txn: t,op: Op::Begin }),
        forall |k: int| 0 <= k < h.len() && (#[trigger] h[k]).txn == t ==> at <= k,
        forall |k: int| 0 <= k < h.len() && #[trigger] h[k] == (Event { txn: t,op: Op::Begin }) ==> k == at
    decreases h.len()
{
    if h.len() == 0 { assert(h.to_set() =~= Set::<Event>::empty()); assert(false); 0 }
    else {
        let d=h.drop_last(); let e=h.last(); let last=h.len() as int-1; assert(h =~= d.push(e)); history::append(d,e);
        if all(d).contains(t) {
            let at=unique_begin(d,t); assert(h[at] == d[at]);
            if e.txn == t { assert(e.op != Op::Begin); }
            assert forall |k: int| 0 <= k < h.len() && (#[trigger] h[k]).txn == t implies at <= k by { if k < d.len() { assert(d[k] == h[k]); } }
            assert forall |k: int| 0 <= k < h.len() && #[trigger] h[k] == (Event { txn: t,op: Op::Begin }) implies k == at by { if k < d.len() { assert(d[k] == h[k]); } }
            at
        } else {
            assert(e.txn == t && e.op == Op::Begin);
            assert forall |k: int| 0 <= k < h.len() && (#[trigger] h[k]).txn == t implies k == last by { if k < d.len() { event_member(d,k); assert(false); } }
            last
        }
    }
}
pub proof fn start_position(h: Seq<Event>,t: int)
    requires valid(h),all(h).contains(t)
    ensures 1 <= start(h,t) <= h.len(),h[start(h,t)-1] == (Event { txn: t,op: Op::Begin }),
        position(h,Event { txn: t,op: Op::Begin }) == start(h,t)
{
    let at=unique_begin(h,t); assert(h.contains(Event { txn: t,op: Op::Begin }));
    let pos=at+1; assert(h[pos-1] == (Event { txn: t,op: Op::Begin }));
    let chosen=choose |k: int| 1 <= k <= h.len() && #[trigger] h[k-1] == Event { txn: t,op: Op::Begin };
    assert(chosen == pos);
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires support::safety_spec(b,c),time >= 0
    ensures valid(b[time].history)
    decreases time
{
    if time > 0 { at(b,c,time-1); support::at(b,c,time-1); let a=support::step(b,c,time-1); preserve(b[time-1],c,a); }
}
} // verus!
