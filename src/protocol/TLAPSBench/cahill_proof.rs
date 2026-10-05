//! Initialization and progress witnesses. The full theorem is in cahill_cycle_search.
use vstd::prelude::*;
use super::cahill::*;
verus! {
broadcast use { vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq::Seq::to_set_ensures, vstd::set::Set::lemma_map_contains };
pub proof fn initial_serializable(c: Constants)
    ensures serializable(initial(c),c)
{
    assert(committed(initial(c).history) =~= Set::empty());
    assert forall |p: Seq<int>| !#[trigger] cycle(initial(c).history,c,p) by {
        if cycle(initial(c).history,c,p) {
            assert(dependency(initial(c).history,c,p[0],p[0int+1]));
            assert(false);
        }
    }
}
pub proof fn can_begin(c: Constants,t: int)
    requires c.txns.contains(t)
    ensures enabled(initial(c),c,Action::Begin(t))
{
    reveal(enabled);
    assert(all(initial(c).history) =~= Set::empty());
}
} // verus!
