//! Logical replay of FIFO messages on log contents, with no protocol transitions added.
use vstd::prelude::*;
use super::zab::{*,equal};
use super::zab_log_math as math;
use super::zab_leader_logs::{self as leader,epoch_prefix,prefix};
use super::zab_proposal_logs as proposals;
verus! {
pub open spec fn effect(h: Seq<Txn>,m: Message) -> Seq<Txn> {
    match m {
        Message::NewLeader(_,copy) => copy,
        Message::Propose(z,v) => if next_zxid(last(h),z) { h.push(Txn { zxid: z,value: v,ack: Set::empty(),epoch: z.epoch }) } else { h },
        _ => h,
    }
}
pub open spec fn replay(h: Seq<Txn>,q: Seq<Message>) -> Seq<Txn>
    decreases q.len()
{ if q.len() == 0 { h } else { replay(effect(h,q[0]),q.drop_first()) } }
pub open spec fn count(h: Seq<Txn>,e: int) -> int { if last(h).epoch == e { last(h).counter } else { 0 } }
pub proof fn append(h: Seq<Txn>,q: Seq<Message>,m: Message)
    ensures replay(h,q.push(m)) == effect(replay(h,q),m)
    decreases q.len()
{
    reveal_with_fuel(replay,2);
    if q.len() > 0 {
        assert(q.push(m).drop_first() =~= q.drop_first().push(m)); append(effect(h,q[0]),q.drop_first(),m);
    } else { assert(q.push(m)[0] == m); assert(q.push(m).drop_first() =~= Seq::<Message>::empty()); }
}
pub proof fn split(h: Seq<Txn>,q: Seq<Message>,k: int)
    requires 0 <= k <= q.len()
    ensures replay(h,q) == replay(replay(h,q.take(k)),q.skip(k))
    decreases k
{
    if k > 0 {
        assert(q.take(k).drop_first() =~= q.drop_first().take(k-1)); assert(q.drop_first().skip(k-1) =~= q.skip(k));
        split(effect(h,q[0]),q.drop_first(),k-1);
    } else { assert(q.skip(k) =~= q); assert(q.take(k) =~= Seq::<Message>::empty()); }
}
pub proof fn take_step(h: Seq<Txn>,q: Seq<Message>,p: int)
    requires q.len() > 0,0 <= p < q.len()
    ensures replay(effect(h,q[0]),q.drop_first().take(p)) == replay(h,q.take(p+1))
{
    assert(q.take(p+1)[0] == q[0]); assert(q.take(p+1).drop_first() =~= q.drop_first().take(p));
}
pub proof fn snapshot(h: Seq<Txn>,q: Seq<Message>,p: int,e: int,copy: Seq<Txn>)
    requires 0 <= p < q.len(),q[p] == Message::NewLeader(e,copy)
    ensures replay(h,q) == replay(copy,q.skip(p+1))
{
    split(h,q,p+1); assert(q.take(p+1) =~= q.take(p).push(q[p])); append(h,q.take(p),q[p]);
}
pub open spec fn fits(reference: Seq<Txn>,e: int,m: Message) -> bool {
    match m {
        Message::NewLeader(epoch,copy) => epoch == e && math::shape(copy) && epoch_prefix(copy,reference,e),
        Message::Propose(z,v) => z.epoch == e && proposals::contains(reference,z,v),
        _ => true,
    }
}
pub open spec fn fits_queue(reference: Seq<Txn>,e: int,q: Seq<Message>) -> bool {
    forall |p: int| 0 <= p < q.len() ==> #[trigger] fits(reference,e,q[p])
}
pub proof fn suffix(reference: Seq<Txn>,e: int,q: Seq<Message>,k: int)
    requires fits_queue(reference,e,q),0 <= k <= q.len()
    ensures fits_queue(reference,e,q.skip(k))
{
    assert forall |p: int| 0 <= p < q.skip(k).len() implies #[trigger] fits(reference,e,q.skip(k)[p]) by { assert(fits(reference,e,q[p+k])); }
}
pub proof fn effect_prefix(h: Seq<Txn>,reference: Seq<Txn>,e: int,m: Message)
    requires math::shape(h),math::shape(reference),epoch_prefix(h,reference,e),fits(reference,e,m)
    ensures math::shape(effect(h,m)),epoch_prefix(effect(h,m),reference,e)
{
    if let Message::Propose(z,v)=m {
        if next_zxid(last(h),z) {
            let p=choose |p: int| #![trigger reference[p]] 0 <= p < reference.len() && reference[p].zxid == z && reference[p].value == v;
            let t=Txn { zxid: z,value: v,ack: Set::empty(),epoch: z.epoch };
            leader::append_prefix(h,reference,e,p,t); math::append(h,t);
        }
    }
}
pub proof fn replay_prefix(h: Seq<Txn>,reference: Seq<Txn>,e: int,q: Seq<Message>)
    requires math::shape(h),math::shape(reference),epoch_prefix(h,reference,e),fits_queue(reference,e,q)
    ensures math::shape(replay(h,q)),epoch_prefix(replay(h,q),reference,e)
    decreases q.len()
{
    if q.len() > 0 {
        effect_prefix(h,reference,e,q[0]); suffix(reference,e,q,1); assert(q.skip(1) =~= q.drop_first());
        replay_prefix(effect(h,q[0]),reference,e,q.drop_first());
    }
}
pub proof fn bounded_prefix(a: Seq<Txn>,d: Seq<Txn>,e: int)
    requires prefix(a,d),math::bounded(d,e)
    ensures math::bounded(a,e)
{
    assert forall |p: int| 0 <= p < a.len() implies (#[trigger] a[p]).zxid.epoch <= e by { assert(equal(a[p],d[p])); }
}
pub proof fn next_counter(h: Seq<Txn>,e: int,sent: int,v: int)
    requires math::shape(h),math::bounded(h,e),0 <= sent <= count(h,e)
    ensures count(effect(h,Message::Propose(Zxid { epoch: e,counter: sent+1 },v)),e) >= sent+1
{
    assert(h[h.len() as int-1].zxid.epoch <= e); assert(h[h.len() as int-1].zxid.counter > 0);
}
} // verus!
