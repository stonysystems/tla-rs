//! A quorum certificate includes a follower whose stored prefix was actually proposed.
use vstd::prelude::*;
use super::zab::{*,equal};
use super::zab_connections as connections;
use super::zab_logs as logs;
use super::zab_ack_certificates as acks;
use super::zab_commit_certificates::certified;
use super::zab_proposal_records as records;
use super::temporal::Behavior;
verus! {
pub proof fn follower_proposed(b: Behavior<LState>,c: Constants,time: int,i: int,j: int,k: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),c.servers.contains(j),i != j,
        b[time].nodes[i].role == Role::Leading,b[time].nodes[i].phase != Phase::Discovery,b[time].nodes[i].current == b[time].nodes[j].current,
        0 <= k < b[time].nodes[j].history.len()
    ensures proposed(b[time],b[time].nodes[j].history[k])
{
    records::at(b,c,time); assert(records::entry(b,time,j,k));
    if !proposed(b[time],b[time].nodes[j].history[k]) {
        let read=choose |read: int| records::owned(b,time,j,b[time].nodes[j].current,read);
        super::zab_elections::unique(b,c,time,i,read,j); assert(false);
    }
}
pub proof fn certificate_proposed(b: Behavior<LState>,c: Constants,time: int,e: int,h: Seq<Txn>,k: int,x: int)
    requires connections::safety_spec(b,c),time >= 0,e > 0,certified(b,c,time,e,h,k),0 <= x <= k
    ensures proposed(b[time],h[x])
{
    let i=choose |i: int| c.servers.contains(i) && exists |q: Set<int>| quorum(q,c)
        && forall |j: int| q.contains(j) ==> acks::certificate(b,c,time,i,e,h,k,j);
    let q=choose |q: Set<int>| quorum(q,c) && forall |j: int| q.contains(j) ==> acks::certificate(b,c,time,i,e,h,k,j);
    assert(!q.is_empty()); let first=choose |j: int| q.contains(j); assert(acks::certificate(b,c,time,i,e,h,k,first));
    let observed=choose |read: int| acks::witness(b,time,i,e,h,k,first,read); logs::at(b,c,observed); logs::facts(b[observed],c,i,i);
    assert(c.servers.len() > 1);
    if q.subset_of(set![i]) { vstd::set_lib::lemma_len_subset(q,set![i]); assert(false); }
    let j=choose |j: int| q.contains(j) && j != i; assert(acks::certificate(b,c,time,i,e,h,k,j));
    let read=choose |read: int| acks::witness(b,time,i,e,h,k,j,read);
    assert(equal(h[x],b[read].nodes[j].history[x])); follower_proposed(b,c,read,i,j,x);
    records::history_monotone(b,c,read,time); records::proposed_copy(b[read],b[time],b[read].nodes[j].history[x],h[x]);
}
pub proof fn committed_proposed(b: Behavior<LState>,c: Constants,time: int,i: int,k: int)
    requires connections::safety_spec(b,c),time >= 0,c.servers.contains(i),0 <= k < b[time].nodes[i].committed.index
    ensures proposed(b[time],b[time].nodes[i].history[k])
{
    super::zab_committed_prefixes::at(b,c,time); assert(super::zab_committed_prefixes::node(b,c,time,i));
    if b[time].nodes[i].committed.index == 1 {
        logs::at(b,c,time); logs::facts(b[time],c,i,i);
        let p=Proposal { source: i,epoch: 0,zxid: boot(),value: 0 }; assert(b[0].proposals.contains(p));
        records::history_monotone(b,c,0,time); assert(b[time].proposals.contains(p));
    } else {
        let e=super::zab_committed_prefixes::certificate_for(b,c,time,i);
        certificate_proposed(b,c,time,e,b[time].nodes[i].history,b[time].nodes[i].committed.index-1,k);
    }
}
pub proof fn integrity_at(b: Behavior<LState>,c: Constants,time: int)
    requires connections::safety_spec(b,c),time >= 0
    ensures integrity(b[time],c)
{
    assert forall |i: int,k: int| c.servers.contains(i) && b[time].nodes[i].role == Role::Following && 1 <= k <= b[time].nodes[i].committed.index
        implies #[trigger] proposed(b[time],b[time].nodes[i].history[k-1]) by { committed_proposed(b,c,time,i,k-1); }
}
pub proof fn benchmark_integrity(b: Behavior<LState>,c: Constants)
    requires connections::safety_spec(b,c)
    ensures forall |time: int| time >= 0 ==> #[trigger] integrity(b[time],c)
{
    assert forall |time: int| time >= 0 implies #[trigger] integrity(b[time],c) by { integrity_at(b,c,time); }
}
} // verus!
