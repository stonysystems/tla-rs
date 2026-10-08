//! Initial benchmark predicates and a nonstuttering election action.
//! Preservation of the nine benchmark goals remains open.
use vstd::prelude::*;
use super::{zookeeper::*,zk_election as fle};
verus! {
pub proof fn initial_goals(c: Constants)
    requires valid_constants(c)
    ensures leadership1(initial(c),c),leadership2(initial(c),c),prefix_consistency(initial(c),c),
        integrity(initial(c),c),agreement(initial(c),c),total_order(initial(c),c),
        local_primary_order(initial(c),c),global_primary_order(initial(c),c),primary_integrity(initial(c),c)
{}
pub proof fn can_timeout(c: Constants,i: int)
    requires c.servers.contains(i)
    ensures enabled(initial(c),c,Action::Election(fle::Action::Timeout(i)))
{
    reveal(enabled);
    assert forall |j: int| #![trigger c.servers.contains(j)] c.servers.contains(j) implies initial(c).election.msgs[(j,i)].len() == 0 by {
        let row=c.servers.map(|k: int| (j,k));
        c.servers.lemma_map_contains(|k: int| (j,k),(j,i));
        c.servers.lemma_map_contains(|k: int| c.servers.map(|l: int| (k,l)),row);
        c.servers.map(|k: int| c.servers.map(|l: int| (k,l))).lemma_flatten_contains((j,i));
        assert(super::zab::channels(c).contains((j,i)));
    }
}
} // verus!
