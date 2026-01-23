// Test for spec predicates with quantifiers over sequences
// Tests: forall |i| 0 <= i < seq.len() ==> seq[i] == 0
// This is the pattern used in LAcceptorInit.last_checkpointed_operation

use vstd::prelude::*;
use vstd::seq::*;

verus! {
    // === SPEC TYPES ===

    pub struct LReplicaConstants {
        pub my_index: int,
        pub num_replicas: int,
    }

    pub struct LState {
        pub checkpoints: Seq<int>,
        pub value: int,
    }

    // === SPEC PREDICATE ===
    // Pattern from LAcceptorInit: sequence of given length, all elements 0

    pub open spec fn LStateInit(s: LState, c: LReplicaConstants) -> bool
    {
        &&& s.checkpoints.len() == c.num_replicas
        &&& (forall |idx:int| 0 <= idx < s.checkpoints.len() ==> s.checkpoints[idx] == 0)
        &&& s.value == 0
    }

    // Simplified version - just seq elements all equal to constant
    pub open spec fn AllZeros(s: Seq<int>) -> bool
    {
        forall |i:int| 0 <= i < s.len() ==> s[i] == 0
    }

    // === EXEC TYPES ===

    pub struct CReplicaConstants {
        pub my_index: i64,
        pub num_replicas: i64,
    }

    impl CReplicaConstants {
        pub open spec fn well_formed(&self) -> bool {
            self.num_replicas >= 0
        }
    }

    impl View for CReplicaConstants {
        type V = LReplicaConstants;
        open spec fn view(&self) -> LReplicaConstants {
            LReplicaConstants {
                my_index: self.my_index as int,
                num_replicas: self.num_replicas as int,
            }
        }
    }

    // Simple Vec wrapper with proper view
    pub struct CCheckpoints {
        pub data: Vec<i64>,
    }

    impl CCheckpoints {
        pub open spec fn well_formed(&self) -> bool { true }

        // Create a sequence of zeros of given length
        pub fn zeros(len: usize) -> (result: CCheckpoints)
            ensures
                result@.len() == len,
                AllZeros(result@),
        {
            let mut v = Vec::new();
            let mut i: usize = 0;
            while i < len
                invariant
                    i <= len,
                    v@.len() == i,
                    forall |j:int| 0 <= j < i ==> v@[j] == 0i64,
                decreases len - i
            {
                v.push(0);
                i = i + 1;
            }

            // Prove that int view of i64 zeros is also zeros
            proof {
                assert forall |j:int| 0 <= j < v@.len() implies v@[j] as int == 0 by {
                    assert(v@[j] == 0i64);
                }
            }

            CCheckpoints { data: v }
        }
    }

    impl View for CCheckpoints {
        type V = Seq<int>;
        open spec fn view(&self) -> Seq<int> {
            Seq::new(self.data@.len(), |i: int| self.data@[i] as int)
        }
    }

    pub struct CState {
        pub checkpoints: CCheckpoints,
        pub value: i64,
    }

    impl CState {
        pub open spec fn well_formed(&self) -> bool {
            self.checkpoints.well_formed()
        }
    }

    impl View for CState {
        type V = LState;
        open spec fn view(&self) -> LState {
            LState {
                checkpoints: self.checkpoints@,
                value: self.value as int,
            }
        }
    }

    // === EXEC FUNCTION ===

    pub fn c_state_init(c: &CReplicaConstants) -> (result: CState)
        requires
            c.well_formed(),
            c.num_replicas >= 0,
            c.num_replicas <= usize::MAX as i64,  // Ensure cast is valid
        ensures
            result.well_formed(),
            LStateInit(result@, c@),
    {
        CState {
            checkpoints: CCheckpoints::zeros(c.num_replicas as usize),
            value: 0,
        }
    }
}

fn main() {}
