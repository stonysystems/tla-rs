//! Filtering a history preserves the relative order of retained unique events.
use vstd::prelude::*;
use super::cahill::*;
verus! {
broadcast use { vstd::seq_lib::group_seq_properties, vstd::seq_lib::group_filter_ensures };
pub proof fn found(h: Seq<Event>,e: Event)
    ensures (position(h,e) != -1 <==> h.contains(e)),h.contains(e) ==> 1 <= position(h,e) <= h.len() && h[position(h,e)-1] == e
{
    if h.contains(e) {
        let i=choose |i: int| 0 <= i < h.len() && h[i] == e; assert(h[i+1-1] == e);
    }
}
pub proof fn index(h: Seq<Event>,i: int)
    requires h.no_duplicates(),0 <= i < h.len()
    ensures position(h,h[i]) == i+1
{
    assert(h.contains(h[i])); found(h,h[i]);
}
pub proof fn prefix(h: Seq<Event>,d: Seq<Event>,e: Event)
    requires h.is_prefix_of(d),d.no_duplicates(),h.contains(e)
    ensures position(h,e) == position(d,e)
{
    found(h,e); let i=position(h,e)-1; assert(d[i] == h[i]); index(d,i);
}
pub proof fn filter_unique(h: Seq<Event>,p: spec_fn(Event) -> bool)
    requires h.no_duplicates()
    ensures h.filter(p).no_duplicates()
    decreases h.len()
{
    reveal(Seq::filter);
    if h.len() > 0 {
        let d=h.drop_last(); assert(d.no_duplicates()); filter_unique(d,p);
        if d.filter(p).contains(h.last()) { d.lemma_filter_contains_rev(p,h.last()); assert(d.contains(h.last())); }
        assert forall |i: int,j: int| 0 <= i < j < h.filter(p).len() implies h.filter(p)[i] != h.filter(p)[j] by {
            if p(h.last()) && j == h.filter(p).len()-1 {
                assert(d.filter(p).contains(h.filter(p)[i]));
            } else { assert(h.filter(p)[i] == d.filter(p)[i]); assert(h.filter(p)[j] == d.filter(p)[j]); }
        }
    }
}
pub proof fn filter_position(h: Seq<Event>,p: spec_fn(Event) -> bool,i: int)
    requires h.no_duplicates(),0 <= i < h.len(),p(h[i])
    ensures position(h.filter(p),h[i]) == h.take(i).filter(p).len()+1
{
    let front=h.take(i).push(h[i]); let tail=h.skip(i+1);
    assert(h =~= front+tail); h.take(i).lemma_filter_push(h[i],p);
    Seq::filter_distributes_over_add(front,tail,p);
    let n=h.take(i).filter(p).len() as int; assert(h.filter(p)[n] == h[i]);
    filter_unique(h,p); index(h.filter(p),n);
}
pub proof fn filter_order(h: Seq<Event>,p: spec_fn(Event) -> bool,e: Event,d: Event)
    requires h.no_duplicates(),h.contains(e),h.contains(d),p(e),p(d)
    ensures h.filter(p).contains(e),h.filter(p).contains(d),
        (position(h,e) < position(h,d) <==> position(h.filter(p),e) < position(h.filter(p),d))
{
    found(h,e); found(h,d); let i=position(h,e)-1; let j=position(h,d)-1;
    h.lemma_filter_contains(p,i); h.lemma_filter_contains(p,j);
    filter_position(h,p,i); filter_position(h,p,j);
    if i < j {
        let a=h.take(i).push(h[i]); let rest=h.subrange(i+1,j);
        assert(h.take(j) =~= a+rest); Seq::filter_distributes_over_add(a,rest,p); h.take(i).lemma_filter_push(h[i],p);
    } else if j < i {
        let a=h.take(j).push(h[j]); let rest=h.subrange(j+1,i);
        assert(h.take(i) =~= a+rest); Seq::filter_distributes_over_add(a,rest,p); h.take(j).lemma_filter_push(h[j],p);
    }
}
pub proof fn filtered_keys(h: Seq<Event>,p: spec_fn(Event) -> bool,t: int,read: bool)
    requires forall |e: Event| e.txn == t ==> p(e)
    ensures keys(h.filter(p),t,read) =~= keys(h,t,read)
{
    assert forall |k: int| keys(h.filter(p),t,read).contains(k) <==> keys(h,t,read).contains(k) by {
        super::cahill_keys::member(h,t,read,k); super::cahill_keys::member(h.filter(p),t,read,k);
        if keys(h,t,read).contains(k) {
            let i=choose |i: int| 0 <= i < h.len() && super::cahill_keys::access(#[trigger] h[i],t,read) && super::cahill_keys::key(h[i]) == k;
            h.lemma_filter_contains(p,i); let j=choose |j: int| 0 <= j < h.filter(p).len() && h.filter(p)[j] == h[i];
        }
        if keys(h.filter(p),t,read).contains(k) {
            let j=choose |j: int| 0 <= j < h.filter(p).len() && super::cahill_keys::access(#[trigger] h.filter(p)[j],t,read) && super::cahill_keys::key(h.filter(p)[j]) == k;
            assert(h.filter(p).contains(h.filter(p)[j])); h.lemma_filter_contains_rev(p,h.filter(p)[j]);
            let i=choose |i: int| 0 <= i < h.len() && h[i] == h.filter(p)[j];
        }
    }
}
} // verus!
