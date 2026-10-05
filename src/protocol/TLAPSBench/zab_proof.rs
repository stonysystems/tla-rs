//! Initialization checks and a nonstuttering witness for the handwritten Zab model.
use vstd::prelude::*;
use super::zab::*;
verus! {
pub proof fn initial_goals(c: Constants)
    requires valid_constants(c)
    ensures leadership1(initial(c),c),leadership2(initial(c),c),
        prefix_consistency(initial(c),c),integrity(initial(c),c),agreement(initial(c),c),
        total_order(initial(c),c),local_primary_order(initial(c),c),
        global_primary_order(initial(c),c),primary_integrity(initial(c),c)
{}
pub proof fn can_choose_leader()
    ensures enabled(initial(Constants { servers: set![0int,1int,2int],max_epoch: 3,request_value: 1 }),
        Constants { servers: set![0int,1int,2int],max_epoch: 3,request_value: 1 },Action::UpdateLeader(0))
{ reveal(enabled); }
} // verus!
