//! Read/write key summaries are unchanged by begin, commit, and abort records.
use vstd::prelude::*;
use super::cahill::*;
verus! {
broadcast use { vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures, vstd::set::Set::lemma_map_contains };
pub open spec fn access(e: Event,t: int,read: bool) -> bool {
    e.txn == t && if read { e.op is Read } else { e.op is Write }
}
pub open spec fn key(e: Event) -> int { match e.op { Op::Read { key,.. } => key,Op::Write(k) => k,_ => 0 } }
pub proof fn member(h: Seq<Event>,t: int,read: bool,k: int)
    ensures keys(h,t,read).contains(k) <==> exists |i: int| 0 <= i < h.len() && access(#[trigger] h[i],t,read) && key(h[i]) == k
{
    let q=h.to_set().filter(|e: Event| e.txn == t && if read { e.op is Read } else { e.op is Write });
    let f=|e: Event| match e.op { Op::Read { key,.. } => key,Op::Write(k) => k,_ => 0 };
    q.lemma_map_contains(f,k);
    if keys(h,t,read).contains(k) {
        let e=choose |e: Event| q.contains(e) && f(e) == k;
        assert(h.to_set().contains(e));
        let i=choose |i: int| 0 <= i < h.len() && h[i] == e;
        assert(access(h[i],t,read) && key(h[i]) == k);
    }
    if exists |i: int| 0 <= i < h.len() && access(#[trigger] h[i],t,read) && key(h[i]) == k {
        let i=choose |i: int| 0 <= i < h.len() && access(#[trigger] h[i],t,read) && key(h[i]) == k;
        assert(q.contains(h[i])); assert(f(h[i]) == k);
    }
}
pub proof fn concat(h: Seq<Event>,d: Seq<Event>,t: int,read: bool)
    ensures keys(h+d,t,read) =~= keys(h,t,read).union(keys(d,t,read))
{
    assert forall |k: int| keys(h+d,t,read).contains(k) <==> keys(h,t,read).union(keys(d,t,read)).contains(k) by {
        member(h+d,t,read,k); member(h,t,read,k); member(d,t,read,k);
        if keys(h+d,t,read).contains(k) {
            let i=choose |i: int| 0 <= i < (h+d).len() && access(#[trigger] (h+d)[i],t,read) && key((h+d)[i]) == k;
            if i < h.len() { assert((h+d)[i] == h[i]); } else { assert((h+d)[i] == d[i-h.len()]); }
        }
        if keys(h,t,read).contains(k) {
            let i=choose |i: int| 0 <= i < h.len() && access(#[trigger] h[i],t,read) && key(h[i]) == k;
            assert((h+d)[i] == h[i]);
        }
        if keys(d,t,read).contains(k) {
            let i=choose |i: int| 0 <= i < d.len() && access(#[trigger] d[i],t,read) && key(d[i]) == k;
            assert((h+d)[i+h.len()] == d[i]);
        }
    }
}
pub proof fn append(h: Seq<Event>,e: Event,t: int,read: bool)
    ensures keys(h.push(e),t,read) =~= (if access(e,t,read) { keys(h,t,read).insert(key(e)) } else { keys(h,t,read) })
{
    concat(h,seq![e],t,read); assert(h.push(e) =~= h+seq![e]);
    assert forall |k: int| keys(seq![e],t,read).contains(k) <==> access(e,t,read) && key(e) == k by { member(seq![e],t,read,k); assert(seq![e][0] == e); }
}
pub proof fn batch(h: Seq<Event>,q: Set<int>,t: int,read: bool)
    ensures keys(h+aborts(q),t,read) =~= keys(h,t,read)
{
    super::cahill_history::batch(q); concat(h,aborts(q),t,read);
    assert forall |k: int| !keys(aborts(q),t,read).contains(k) by { member(aborts(q),t,read,k); }
}
pub proof fn absent(h: Seq<Event>,t: int,read: bool)
    requires !all(h).contains(t)
    ensures keys(h,t,read).is_empty()
{
    assert forall |k: int| !keys(h,t,read).contains(k) by {
        member(h,t,read,k);
        if keys(h,t,read).contains(k) {
            let i=choose |i: int| 0 <= i < h.len() && access(#[trigger] h[i],t,read) && key(h[i]) == k;
            super::cahill_lifecycle::event_member(h,i);
        }
    }
}
pub proof fn member_all(h: Seq<Event>,t: int,read: bool,k: int)
    requires keys(h,t,read).contains(k)
    ensures all(h).contains(t)
{
    member(h,t,read,k);
    let i=choose |i: int| 0 <= i < h.len() && access(#[trigger] h[i],t,read) && key(h[i]) == k;
    super::cahill_lifecycle::event_member(h,i);
}
} // verus!
