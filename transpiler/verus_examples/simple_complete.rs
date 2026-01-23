// Complete standalone example for Verus verification
// Contains both spec and exec types in a single file

use vstd::prelude::*;

verus! {

// ============================================================================
// SPEC LAYER: Abstract specification types and predicates
// ============================================================================

// Spec type for node state
pub struct LNode {
    pub held: bool,
    pub epoch: nat,
}

// Init predicate
pub open spec fn NodeInit(s: LNode, start_with_lock: bool) -> bool {
    &&& s.held == start_with_lock
    &&& s.epoch == 0
}

// Grant predicate: release the lock
pub open spec fn NodeGrant(s: LNode, s_: LNode) -> bool {
    if s.held && s.epoch < 0xFFFF_FFFF_FFFF_FFFE {
        &&& !s_.held
        &&& s_.epoch == s.epoch + 1
    } else {
        s_ == s
    }
}

// Accept predicate: acquire the lock
pub open spec fn NodeAccept(s: LNode, s_: LNode, transfer_epoch: nat) -> bool {
    if !s.held && transfer_epoch > s.epoch {
        &&& s_.held
        &&& s_.epoch == transfer_epoch
    } else {
        s_ == s
    }
}

// ============================================================================
// EXEC LAYER: Concrete implementation types and functions
// ============================================================================

// Concrete execution type
pub struct CNode {
    pub held: bool,
    pub epoch: u64,
}

impl CNode {
    pub fn clone_node(&self) -> (result: CNode)
        ensures result@ == self@,
    {
        CNode {
            held: self.held,
            epoch: self.epoch,
        }
    }
}

// View trait: maps concrete type to spec type
impl View for CNode {
    type V = LNode;

    open spec fn view(&self) -> LNode {
        LNode {
            held: self.held,
            epoch: self.epoch as nat,
        }
    }
}

// Init implementation
pub fn c_node_init(start_with_lock: bool) -> (result: CNode)
    ensures
        NodeInit(result@, start_with_lock),
{
    CNode {
        held: start_with_lock,
        epoch: 0,
    }
}

// Grant implementation
pub fn c_node_grant(s: &CNode) -> (result: CNode)
    ensures
        NodeGrant(s@, result@),
{
    if s.held && s.epoch < 0xFFFF_FFFF_FFFF_FFFE {
        CNode {
            held: false,
            epoch: s.epoch + 1,
        }
    } else {
        s.clone_node()
    }
}

// Accept implementation
pub fn c_node_accept(s: &CNode, transfer_epoch: u64) -> (result: CNode)
    ensures
        NodeAccept(s@, result@, transfer_epoch as nat),
{
    if !s.held && transfer_epoch > s.epoch {
        CNode {
            held: true,
            epoch: transfer_epoch,
        }
    } else {
        s.clone_node()
    }
}

} // verus!

fn main() {
    // Simple test of the functions
    let node = c_node_init(true);
    let node2 = c_node_grant(&node);
    let node3 = c_node_accept(&node2, 5);
    println!("Final: held={}, epoch={}", node3.held, node3.epoch);
}
