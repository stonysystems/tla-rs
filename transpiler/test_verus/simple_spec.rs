// Simple spec for testing transpiler with modern Verus
use vstd::prelude::*;

verus! {
    pub struct LNode {
        pub held: bool,
        pub epoch: nat,
    }

    pub open spec fn NodeInit(s: LNode, start_with_lock: bool) -> bool {
        &&& s.held == start_with_lock
        &&& s.epoch == 0
    }

    pub open spec fn NodeGrant(s: LNode, s_: LNode) -> bool {
        if s.held && s.epoch < 0xFFFF_FFFF_FFFF_FFFF {
            &&& !s_.held
            &&& s_.epoch == s.epoch + 1
        } else {
            s_ == s
        }
    }

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
