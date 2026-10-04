//! Deterministic execution of a command prefix, including returned values.
use vstd::prelude::*;
verus! {
#[verifier::reject_recursive_types(A)]
pub struct Machine<A,R> { pub initial:A, pub step:spec_fn(A,int)->A, pub output:spec_fn(A,int)->R }
pub open spec fn execute<A,R>(m:Machine<A,R>,log:Seq<int>) -> A
    decreases log.len(),
{
    if log.len()==0 { m.initial }
    else { (m.step)(execute(m,log.drop_last()),log.last()) }
}
pub open spec fn result<A,R>(m:Machine<A,R>,log:Seq<int>,i:int) -> R {
    (m.output)(execute(m,log.subrange(0,i)),log[i])
}
pub open spec fn prefix(a:Seq<int>,b:Seq<int>) -> bool {
    a.len() <= b.len() && forall|i:int| 0 <= i < a.len() ==> a[i]==b[i]
}
pub proof fn prefix_result<A,R>(m:Machine<A,R>,a:Seq<int>,b:Seq<int>,i:int)
    requires prefix(a,b),0 <= i < a.len(),
    ensures result(m,a,i)==result(m,b,i),
{ assert(a.subrange(0,i) =~= b.subrange(0,i)); }
} // verus!
