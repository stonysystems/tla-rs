//! Client linearizability and speculative execution consistency.
//! A returned fast response certifies the complete execution prefix, not just
//! the command or its slot. Failed speculation produces no completed response.
use vstd::prelude::*;
use super::reconciliation as r;
use super::super::ConsensusSafety::state_machine as a;
verus! {
pub struct Reply<R> { pub view:int, pub log:Seq<int>, pub value:R, pub time:int }
pub struct Clients<R> { pub calls:Map<int,int>, pub replies:Map<int,Reply<R>> }
pub open spec fn clients_ok<A,R>(s:r::History,c:r::Config,m:a::Machine<A,R>,h:Clients<R>) -> bool {
    forall|x:int| h.replies.dom().contains(x) ==> {
        let reply=h.replies[x];
        &&& r::certified(s,c,reply.view,reply.log)
        &&& reply.log.len()>0 && reply.log.last()==x
        &&& reply.value==a::result(m,reply.log,reply.log.len() as int-1)
        &&& reply.log.to_set().subset_of(h.calls.dom())
        &&& forall|y:int| reply.log.contains(y) ==> h.calls[y] < reply.time
    }
}
pub open spec fn linearization<A,R>(m:a::Machine<A,R>,h:Clients<R>,log:Seq<int>) -> bool {
    &&& log.no_duplicates() && log.to_set().subset_of(h.calls.dom())
    &&& h.replies.dom().subset_of(log.to_set())
    &&& forall|i:int| 0 <= i < log.len() && h.replies.dom().contains(log[i])
        ==> h.replies[log[i]].value==a::result(m,log,i)
    &&& forall|i:int,j:int| 0 <= i < log.len() && 0 <= j < log.len()
        && h.replies.dom().contains(log[i]) && h.replies[log[i]].time < h.calls[log[j]] ==> i < j
}
pub proof fn largest_reply<R>(replies:Map<int,Reply<R>>) -> (x:int)
    requires replies.dom()!=Set::<int>::empty(),
    ensures replies.dom().contains(x),
        forall|y:int| replies.dom().contains(y) ==> replies[y].log.len() <= replies[x].log.len(),
    decreases replies.dom().len(),
{
    if replies.dom().len()==0 { replies.dom().lemma_len0_is_empty(); assert(false); }
    assert(replies.dom().len()>0);
    vstd::set::lemma_set_choose_len(replies.dom());
    let x=replies.dom().choose();
    let rest=replies.remove(x);
    assert(rest.dom() =~= replies.dom().remove(x));
    if rest.dom()==Set::<int>::empty() {
        assert forall|y:int| replies.dom().contains(y) implies y==x by {};
        x
    } else {
        let y=largest_reply(rest);
        assert(replies.dom().contains(y));
        if replies[x].log.len() >= replies[y].log.len() {
            assert forall|z:int| replies.dom().contains(z) implies replies[z].log.len() <= replies[x].log.len() by {
                if z!=x { assert(rest.dom().contains(z)); assert(rest[z].log.len() <= rest[y].log.len()); }
            }
            x
        } else {
            assert forall|z:int| replies.dom().contains(z) implies replies[z].log.len() <= replies[y].log.len() by {
                if z!=x { assert(rest.dom().contains(z)); assert(rest[z].log.len() <= rest[y].log.len()); }
            }
            y
        }
    }
}
pub proof fn certified_log_unique(s:r::History,c:r::Config,v:int,log:Seq<int>)
    requires r::config_ok(c),r::well_formed(s,c),r::certified(s,c,v,log),
    ensures log.no_duplicates(),
{
    r::certificate_has_voter(s,c,v,log);
    let n=choose|n:int| c.nodes.contains(n) && r::installed(s,v,n) && r::prefix(log,s.logs[(v,n)]);
    assert(s.logs[(v,n)].no_duplicates());
}
pub proof fn reply_index<R>(h:Clients<R>,log:Seq<int>,x:int,i:int)
    requires h.replies.dom().contains(x),h.replies[x].log.len()>0,h.replies[x].log.last()==x,
        r::prefix(h.replies[x].log,log),log.no_duplicates(),0 <= i < log.len(),log[i]==x,
    ensures i==h.replies[x].log.len() as int-1,
{
    let k=h.replies[x].log.len() as int-1;
    assert(h.replies[x].log[k]==x && log[k]==x);
}
pub proof fn history_linearizable<A,R>(s:r::History,c:r::Config,m:a::Machine<A,R>,h:Clients<R>)
    requires r::config_ok(c),r::well_formed(s,c),clients_ok(s,c,m,h),
    ensures exists|log:Seq<int>| linearization(m,h,log),
{
    if h.replies.dom()==Set::<int>::empty() {
        let log=Seq::<int>::empty();
        assert(log.to_set() =~= Set::<int>::empty());
        assert(linearization(m,h,log));
    } else {
        let x=largest_reply(h.replies); let log=h.replies[x].log;
        certified_log_unique(s,c,h.replies[x].view,log);
        assert forall|y:int| h.replies.dom().contains(y) implies r::prefix(h.replies[y].log,log) by {
            r::certificates_compatible(s,c,h.replies[y].view,h.replies[y].log,h.replies[x].view,log);
            assert(h.replies[y].log.len() <= log.len());
        }
        assert(h.replies.dom().subset_of(log.to_set())) by {
            assert forall|y:int| h.replies.dom().contains(y) implies log.to_set().contains(y) by {
                let i=h.replies[y].log.len() as int-1;
                assert(h.replies[y].log[i]==y && log[i]==y);
                assert(log.contains(y));
            }
        }
        assert forall|i:int| 0 <= i < log.len() && h.replies.dom().contains(log[i])
            implies h.replies[log[i]].value==a::result(m,log,i) by {
            let y=log[i]; reply_index(h,log,y,i);
            a::prefix_result(m,h.replies[y].log,log,i);
        }
        assert forall|i:int,j:int| 0 <= i < log.len() && 0 <= j < log.len()
            && h.replies.dom().contains(log[i]) && h.replies[log[i]].time < h.calls[log[j]] implies i < j by {
            let x=log[i]; let y=log[j]; reply_index(h,log,x,i);
            if j <= i {
                assert(h.replies[x].log[j]==y);
                assert(h.replies[x].log.contains(y));
                assert(h.calls[y] < h.replies[x].time);
            }
        }
        assert(linearization(m,h,log));
    }
}
pub proof fn execution_consistency<A,R>(s:r::History,c:r::Config,m:a::Machine<A,R>,
    v:int,p:Seq<int>,b:int,q:Seq<int>,i:int)
    requires r::config_ok(c),r::well_formed(s,c),r::certified(s,c,v,p),r::certified(s,c,b,q),
        0 <= i < p.len(),i < q.len(),
    ensures p[i]==q[i],a::result(m,p,i)==a::result(m,q,i),
{
    r::certificates_compatible(s,c,v,p,b,q);
    if r::prefix(p,q) { a::prefix_result(m,p,q,i); }
    else { a::prefix_result(m,q,p,i); }
}
} // verus!
