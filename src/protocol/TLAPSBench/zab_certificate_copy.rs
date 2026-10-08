//! Certificate transfer along equal stored prefixes and monotone observation times.
use vstd::prelude::*;
use super::zab::*;
use super::zab_entry_origins::through;
use super::zab_ack_certificates as acks;
use super::zab_commit_certificates::certified;
use super::temporal::Behavior;
verus! {
pub proof fn copy(b: Behavior<LState>,c: Constants,old: int,time: int,e: int,a: Seq<Txn>,d: Seq<Txn>,k: int)
    requires old <= time,certified(b,c,old,e,a,k),through(a,d,k)
    ensures certified(b,c,time,e,d,k)
{
    let i=choose |i: int| c.servers.contains(i) && exists |q: Set<int>| quorum(q,c)
        && forall |j: int| #![trigger q.contains(j)] q.contains(j) ==> acks::certificate(b,c,old,i,e,a,k,j);
    let q=choose |q: Set<int>| quorum(q,c) && forall |j: int| #![trigger q.contains(j)] q.contains(j) ==> acks::certificate(b,c,old,i,e,a,k,j);
    assert forall |j: int| q.contains(j) implies #[trigger] acks::certificate(b,c,time,i,e,d,k,j) by { acks::copy(b,c,old,time,i,e,a,d,k,j); }
}
} // verus!
