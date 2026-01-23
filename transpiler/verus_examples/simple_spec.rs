// Simple spec file for testing transpiler with modern Verus
// This demonstrates the basic structure of a spec that can be transpiled
use vstd::prelude::*;

verus! {
    // Spec type definition
    pub struct LNode {
        pub held: bool,
        pub epoch: nat,
    }

    // Init predicate: s is output, start_with_lock is input
    pub open spec fn NodeInit(s: LNode, start_with_lock: bool) -> bool {
        &&& s.held == start_with_lock
        &&& s.epoch == 0
    }

    // Grant predicate: s is input, s_ is output
    pub open spec fn NodeGrant(s: LNode, s_: LNode) -> bool {
        if s.held && s.epoch < 0xFFFF_FFFF_FFFF_FFFE {
            &&& !s_.held
            &&& s_.epoch == s.epoch + 1
        } else {
            s_ == s
        }
    }

    // Accept predicate: s is input, s_ is output, transfer_epoch is input
    pub open spec fn NodeAccept(s: LNode, s_: LNode, transfer_epoch: nat) -> bool {
        if !s.held && transfer_epoch > s.epoch {
            &&& s_.held
            &&& s_.epoch == transfer_epoch
        } else {
            s_ == s
        }
    }
}

fn main() {}
