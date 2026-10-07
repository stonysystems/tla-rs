//! Finite history summaries and the exact effect of an atomic batch of aborts.
use vstd::prelude::*;
use super::cahill::*;
verus! {
broadcast use { vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures, vstd::set::Set::lemma_map_contains };
pub proof fn concat(a: Seq<Event>,d: Seq<Event>)
    ensures all(a+d) =~= all(a).union(all(d)),committed(a+d) =~= committed(a).union(committed(d)),aborted(a+d) =~= aborted(a).union(aborted(d))
{
    assert((a+d).to_set() =~= a.to_set().union(d.to_set()));
    assert forall |t: int| all(a+d).contains(t) <==> all(a).union(all(d)).contains(t) by {
        if all(a+d).contains(t) { let e=choose |e: Event| (a+d).to_set().contains(e) && e.txn == t; }
        if all(a).contains(t) { let e=choose |e: Event| a.to_set().contains(e) && e.txn == t; assert((a+d).to_set().contains(e)); }
        if all(d).contains(t) { let e=choose |e: Event| d.to_set().contains(e) && e.txn == t; assert((a+d).to_set().contains(e)); }
    }
    assert forall |t: int| committed(a+d).contains(t) <==> committed(a).union(committed(d)).contains(t) by {
        if committed(a+d).contains(t) { let e=choose |e: Event| (a+d).to_set().contains(e) && e.op == Op::Commit && e.txn == t; if a.to_set().contains(e) { assert(a.to_set().filter(|e: Event| e.op == Op::Commit).contains(e)); } else { assert(d.to_set().filter(|e: Event| e.op == Op::Commit).contains(e)); } }
        if committed(a).contains(t) { let e=choose |e: Event| a.to_set().contains(e) && e.op == Op::Commit && e.txn == t; assert((a+d).to_set().filter(|e: Event| e.op == Op::Commit).contains(e)); }
        if committed(d).contains(t) { let e=choose |e: Event| d.to_set().contains(e) && e.op == Op::Commit && e.txn == t; assert((a+d).to_set().filter(|e: Event| e.op == Op::Commit).contains(e)); }
    }
    assert forall |t: int| aborted(a+d).contains(t) <==> aborted(a).union(aborted(d)).contains(t) by {
        if aborted(a+d).contains(t) { let e=choose |e: Event| (a+d).to_set().contains(e) && e.op is Abort && e.txn == t; if a.to_set().contains(e) { assert(a.to_set().filter(|e: Event| e.op is Abort).contains(e)); } else { assert(d.to_set().filter(|e: Event| e.op is Abort).contains(e)); } }
        if aborted(a).contains(t) { let e=choose |e: Event| a.to_set().contains(e) && e.op is Abort && e.txn == t; assert((a+d).to_set().filter(|e: Event| e.op is Abort).contains(e)); }
        if aborted(d).contains(t) { let e=choose |e: Event| d.to_set().contains(e) && e.op is Abort && e.txn == t; assert((a+d).to_set().filter(|e: Event| e.op is Abort).contains(e)); }
    }
}
pub proof fn singleton(e: Event)
    ensures all(seq![e]) =~= set![e.txn],committed(seq![e]) =~= (if e.op == Op::Commit { set![e.txn] } else { Set::empty() }),
        aborted(seq![e]) =~= (if e.op is Abort { set![e.txn] } else { Set::empty() })
{
    assert(seq![e].to_set() =~= set![e]);
    assert(seq![e].to_set().contains(e));
    if e.op == Op::Commit { assert(seq![e].to_set().filter(|e: Event| e.op == Op::Commit).contains(e)); }
    if e.op is Abort { assert(seq![e].to_set().filter(|e: Event| e.op is Abort).contains(e)); }
}
pub proof fn append(h: Seq<Event>,e: Event)
    ensures all(h.push(e)) =~= all(h).insert(e.txn),
        committed(h.push(e)) =~= (if e.op == Op::Commit { committed(h).insert(e.txn) } else { committed(h) }),
        aborted(h.push(e)) =~= (if e.op is Abort { aborted(h).insert(e.txn) } else { aborted(h) })
{
    concat(h,seq![e]); singleton(e); assert(h.push(e) =~= h+seq![e]);
}
pub proof fn batch(q: Set<int>)
    ensures aborts(q).len() == q.len(),all(aborts(q)) =~= q,aborted(aborts(q)) =~= q,committed(aborts(q)) =~= Set::<int>::empty(),
        forall |p: int| 0 <= p < aborts(q).len() ==> (#[trigger] aborts(q)[p]).op == Op::Abort(Reason::FirstCommitter)
    decreases q.len()
{
    if q.is_empty() { assert(aborts(q).to_set() =~= Set::<Event>::empty()); }
    else {
        let t=choose |t: int| q.contains(t); let e=Event { txn: t,op: Op::Abort(Reason::FirstCommitter) };
        batch(q.remove(t)); singleton(e); concat(seq![e],aborts(q.remove(t)));
        assert(set![t].union(q.remove(t)) =~= q);
        assert forall |p: int| 0 <= p < aborts(q).len() implies (#[trigger] aborts(q)[p]).op == Op::Abort(Reason::FirstCommitter) by {
            if p > 0 { assert(aborts(q)[p] == aborts(q.remove(t))[p-1]); }
        }
    }
}
pub proof fn commit_batch(h: Seq<Event>,t: int,q: Set<int>)
    requires q.subset_of(active(h)),active(h).contains(t),!q.contains(t)
    ensures all(h.push(Event { txn: t,op: Op::Commit })+aborts(q)) =~= all(h),
        committed(h.push(Event { txn: t,op: Op::Commit })+aborts(q)) =~= committed(h).insert(t),
        aborted(h.push(Event { txn: t,op: Op::Commit })+aborts(q)) =~= aborted(h).union(q),
        active(h.push(Event { txn: t,op: Op::Commit })+aborts(q)) =~= active(h).remove(t).difference(q)
{
    append(h,Event { txn: t,op: Op::Commit }); batch(q); concat(h.push(Event { txn: t,op: Op::Commit }),aborts(q));
}
} // verus!
