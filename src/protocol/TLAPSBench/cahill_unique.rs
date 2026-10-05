//! Each transaction reads and writes a key at most once in its event history.
use vstd::prelude::*;
use super::cahill::*;
use super::cahill_keys as keys_math;
use super::cahill_support as support;
use super::cahill_records as records;
use super::cahill_lifecycle as lifecycle;
use super::cahill_history_order as order;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures, vstd::set::Set::lemma_map_contains };
pub open spec fn fresh(h: Seq<Event>,e: Event) -> bool {
    (!(e.op is Read) && !(e.op is Write)) || !keys(h,e.txn,e.op is Read).contains(keys_math::key(e))
}
pub open spec fn valid(h: Seq<Event>) -> bool
    decreases h.len()
{
    h.len() == 0 || valid(h.drop_last()) && fresh(h.drop_last(),h.last())
}
pub proof fn append(h: Seq<Event>,e: Event)
    requires valid(h),fresh(h,e)
    ensures valid(h.push(e))
{
    assert(h.push(e).drop_last() =~= h); assert(h.push(e).last() == e);
}
pub proof fn batch(h: Seq<Event>,q: Set<int>)
    requires valid(h)
    ensures valid(h+aborts(q))
    decreases q.len()
{
    if q.is_empty() { assert(h+aborts(q) =~= h); }
    else {
        let t=choose |t: int| q.contains(t); let e=Event { txn: t,op: Op::Abort(Reason::FirstCommitter) };
        append(h,e); batch(h.push(e),q.remove(t)); assert(h+aborts(q) =~= h.push(e)+aborts(q.remove(t)));
    }
}
pub proof fn acquire_valid(s: LState,c: Constants,t: int,k: int)
    requires valid(s.history),records::exact(s,c),c.txns.contains(t),active(s.history).contains(t),!s.txns[t].xlocks.contains(k)
    ensures valid(acquire(s,c,t,k).history)
{
    reveal(acquire); assert(records::node(s,t)); append(s.history,Event { txn: t,op: Op::Write(k) });
    append(s.history,Event { txn: t,op: Op::Abort(Reason::WriteConflict) });
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires support::inductive(s,c),records::exact(s,c),valid(s.history),enabled(s,c,a)
    ensures valid(apply(s,c,a).history)
{
    reveal(enabled); reveal(apply); reveal(commit); reveal(read);
    match a {
        Action::Stutter => {},
        Action::Begin(t) => { append(s.history,Event { txn: t,op: Op::Begin }); },
        Action::Abort(t) => { append(s.history,Event { txn: t,op: Op::Abort(Reason::Voluntary) }); },
        Action::Commit(t) => {
            append(s.history,Event { txn: t,op: Op::Abort(Reason::CommitConflict) });
            let e=Event { txn: t,op: Op::Commit }; append(s.history,e); batch(s.history.push(e),losers(s,c,t));
        },
        Action::Read(t,k) => {
            let v=choose |v: int| version(s,t,k).contains(v); append(s.history,Event { txn: t,op: Op::Read { key: k,version: v } });
            append(s.history,Event { txn: t,op: Op::Abort(Reason::ReadConflict) });
        },
        Action::Finish(t) => {
            assert(support::node(s,c,t)); let k=s.txns[t].waiting.unwrap();
            assert(!s.txns[t].xlocks.contains(k)); acquire_valid(s,c,t,k);
        },
        Action::Write { txn: t,key: k,victim: v } => {
            append(s.history,Event { txn: t,op: Op::Abort(Reason::FirstCommitter) });
            acquire_valid(s,c,t,k); append(s.history,Event { txn: v,op: Op::Abort(Reason::Deadlock) });
        },
    }
}
pub proof fn prefix(h: Seq<Event>,n: int)
    requires valid(h),0 <= n <= h.len()
    ensures valid(h.take(n))
    decreases h.len()-n
{
    if n == h.len() { assert(h.take(n) =~= h); }
    else { prefix(h.drop_last(),n); assert(h.drop_last().take(n) =~= h.take(n)); }
}
pub proof fn accesses(h: Seq<Event>,i: int,j: int)
    requires valid(h),0 <= i < j < h.len(),h[i].txn == h[j].txn,
        h[i].op is Read && h[j].op is Read || h[i].op is Write && h[j].op is Write
    ensures keys_math::key(h[i]) != keys_math::key(h[j])
{
    prefix(h,j+1); assert(h.take(j+1).drop_last() =~= h.take(j)); assert(h.take(j+1).last() == h[j]);
    keys_math::member(h.take(j),h[j].txn,h[j].op is Read,keys_math::key(h[i])); assert(h.take(j)[i] == h[i]);
}
pub proof fn no_duplicates(h: Seq<Event>)
    requires valid(h),lifecycle::valid(h)
    ensures h.no_duplicates()
{
    assert forall |i: int,j: int| 0 <= i < j < h.len() implies h[i] != h[j] by {
        if h[i] == h[j] {
            order::ordered(h,i,j);
            match h[j].op {
                Op::Begin | Op::Commit | Op::Abort(_) => {},
                _ => { accesses(h,i,j); },
            }
        }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,time: int)
    requires support::safety_spec(b,c),time >= 0
    ensures valid(b[time].history),b[time].history.no_duplicates()
    decreases time
{
    if time > 0 {
        at(b,c,time-1); support::at(b,c,time-1); records::at(b,c,time-1);
        let a=support::step(b,c,time-1); preserve(b[time-1],c,a);
    }
    lifecycle::at(b,c,time); no_duplicates(b[time].history);
}
} // verus!
