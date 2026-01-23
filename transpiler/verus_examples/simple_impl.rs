// Auto-generated implementation file
// Pairs with simple_spec.rs for verification

use vstd::prelude::*;

// Include the spec file for the LNode type and spec functions
mod simple_spec;
use simple_spec::*;

verus! {

// Concrete execution type corresponding to LNode
#[derive(Clone)]
pub struct CNode {
    pub held: bool,
    pub epoch: u64,
}

// View trait: maps concrete type to ghost/spec type
impl View for CNode {
    type V = LNode;

    open spec fn view(&self) -> LNode {
        LNode {
            held: self.held,
            epoch: self.epoch as nat,
        }
    }
}

impl CNode {
    // A well-formedness predicate (can be extended as needed)
    pub open spec fn well_formed(&self) -> bool {
        true
    }
}

// ============================================================================
// Auto-generated exec functions
// ============================================================================

pub fn c_node_init(start_with_lock: bool) -> (result: CNode)
    ensures
        NodeInit(result@, start_with_lock),
{
    CNode {
        held: start_with_lock,
        epoch: 0,
    }
}

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
        s.clone()
    }
}

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
        s.clone()
    }
}

} // verus!

fn main() {
    // Simple test of the functions
    let node = c_node_init(true);
    println!("Node initialized: held={}, epoch={}", node.held, node.epoch);

    let node2 = c_node_grant(&node);
    println!("After grant: held={}, epoch={}", node2.held, node2.epoch);

    let node3 = c_node_accept(&node2, 5);
    println!("After accept(5): held={}, epoch={}", node3.held, node3.epoch);
}
