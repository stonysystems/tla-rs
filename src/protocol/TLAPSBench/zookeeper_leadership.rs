//! Historical leaders are unique because completed discovery quorums contain exclusive epoch votes.
use vstd::prelude::*;
use super::zookeeper::*;
use super::zab::{Role,Phase};
use super::zookeeper_support as support;
use super::zookeeper_epoch_votes as votes;
use super::zookeeper_receipt_votes as receipts;
use super::temporal::Behavior;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties };
pub proof fn recorded(b: Behavior<LState>,c: Constants,time: int,epoch: int,i: int) -> (at: int)
    requires support::safety_spec(b,c),time >= 0,1 <= epoch <= c.max_epoch,b[time].epoch_leader[epoch].contains(i)
    ensures 0 <= at <= time,c.servers.contains(i),b[at].election.nodes[i].role == Role::Leading,
        election_finished(b[at],c,i),b[at].nodes[i].accepted == epoch
    decreases time
{
    if time == 0 { assert(false); 0 }
    else {
        let prev=time-1; support::at(b,c,prev); let a=support::step(b,c,prev);
        if b[prev].epoch_leader[epoch].contains(i) { recorded(b,c,prev,epoch,i) }
        else { reveal(apply); reveal(enabled); assert(exists |j: int| a == Action::AckEpoch(i,j)); time }
    }
}
pub proof fn completed_unique(b: Behavior<LState>,c: Constants,left: int,right: int,i: int,j: int)
    requires support::safety_spec(b,c),left >= 0,right >= 0,c.servers.contains(i),c.servers.contains(j),
        b[left].election.nodes[i].role == Role::Leading,b[right].election.nodes[j].role == Role::Leading,
        election_finished(b[left],c,i),election_finished(b[right],c,j),b[left].nodes[i].accepted == b[right].nodes[j].accepted
    ensures i == j
{
    if i != j {
        let pair=set![i,j]; assert(pair.subset_of(c.servers)); vstd::set_lib::lemma_len_subset(pair,c.servers);
        receipts::finished_certificate(b,c,left,i); receipts::finished_certificate(b,c,right,j);
        votes::certified_unique(b,c,left,right,i,j,b[left].nodes[i].accepted);
    }
}
pub proof fn leadership2_at(b: Behavior<LState>,c: Constants,time: int)
    requires support::safety_spec(b,c),time >= 0
    ensures leadership2(b[time],c)
{
    assert forall |epoch: int| 1 <= epoch <= c.max_epoch implies (#[trigger] b[time].epoch_leader[epoch]).len() <= 1 by {
        let q=b[time].epoch_leader[epoch];
        if !q.is_empty() {
            let i=choose |i: int| q.contains(i); let left=recorded(b,c,time,epoch,i);
            assert(q.subset_of(set![i])) by {
                assert forall |j: int| q.contains(j) implies j == i by { let right=recorded(b,c,time,epoch,j); completed_unique(b,c,left,right,i,j); }
            }
            vstd::set_lib::lemma_len_subset(q,set![i]);
        }
    }
}
pub proof fn benchmark_leadership2(b: Behavior<LState>,c: Constants)
    requires support::safety_spec(b,c)
    ensures forall |time: int| time >= 0 ==> #[trigger] leadership2(b[time],c)
{
    assert forall |time: int| time >= 0 implies #[trigger] leadership2(b[time],c) by { leadership2_at(b,c,time); }
}
pub proof fn leadership1_at(b: Behavior<LState>,c: Constants,time: int)
    requires support::safety_spec(b,c),time >= 0
    ensures leadership1(b[time],c)
{
    super::zookeeper_completion::at(b,c,time); support::at(b,c,time); let s=b[time];
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) && s.election.nodes[i].role == Role::Leading && s.election.nodes[j].role == Role::Leading
        && (s.nodes[i].phase == Phase::Synchronization || s.nodes[i].phase == Phase::Broadcast) && (s.nodes[j].phase == Phase::Synchronization || s.nodes[j].phase == Phase::Broadcast)
        && s.nodes[i].accepted == s.nodes[j].accepted implies i == j by {
        assert(super::zookeeper_completion::node(s,c,i)); assert(super::zookeeper_completion::node(s,c,j)); completed_unique(b,c,time,time,i,j);
    }
}
pub proof fn benchmark_leadership1(b: Behavior<LState>,c: Constants)
    requires support::safety_spec(b,c)
    ensures forall |time: int| time >= 0 ==> #[trigger] leadership1(b[time],c)
{
    assert forall |time: int| time >= 0 implies #[trigger] leadership1(b[time],c) by { leadership1_at(b,c,time); }
}
} // verus!
