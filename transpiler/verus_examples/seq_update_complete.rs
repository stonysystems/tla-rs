// Test for spec predicates with seq.update() method
// Tests: s_.field == s.field.update(idx, value)
// This is a pattern used in RSL acceptor.rs LAcceptorProcessHeartbeat

use vstd::prelude::*;
use vstd::seq::*;

verus! {
    // === SPEC TYPES ===

    pub type OperationNumber = int;

    pub struct LState {
        pub checkpoints: Seq<OperationNumber>,
        pub other_field: int,
    }

    // === SPEC PREDICATE ===
    // Pattern from LAcceptorProcessHeartbeat:
    // s_.checkpoints == s.checkpoints.update(idx, new_value)

    pub open spec fn LStateUpdate(
        s: LState,
        s_: LState,
        idx: int,
        new_value: OperationNumber
    ) -> bool
        recommends
            0 <= idx < s.checkpoints.len()
    {
        &&& s_.checkpoints == s.checkpoints.update(idx, new_value)
        &&& s_.other_field == s.other_field
    }

    // === EXEC TYPES ===

    pub struct CState {
        pub checkpoints: Vec<i64>,
        pub other_field: i64,
    }

    impl CState {
        pub open spec fn well_formed(&self) -> bool { true }
    }

    impl View for CState {
        type V = LState;
        open spec fn view(&self) -> LState {
            LState {
                checkpoints: Seq::new(self.checkpoints@.len(), |i: int| self.checkpoints@[i] as int),
                other_field: self.other_field as int,
            }
        }
    }

    // === EXEC FUNCTION ===
    // The exec version updates the Vec at the given index

    pub fn c_state_update(s: &CState, idx: usize, new_value: i64) -> (result: CState)
        requires
            s.well_formed(),
            idx < s.checkpoints@.len(),
        ensures
            result.well_formed(),
            LStateUpdate(s@, result@, idx as int, new_value as int),
    {
        // Create a new Vec with the updated value
        let mut new_checkpoints: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        let len = s.checkpoints.len();

        while i < len
            invariant
                i <= len,
                len == s.checkpoints@.len(),
                new_checkpoints@.len() == i,
                forall |j: int| 0 <= j < i ==> new_checkpoints@[j] == (
                    if j == idx as int { new_value } else { s.checkpoints@[j] }
                ),
            decreases len - i
        {
            if i == idx {
                new_checkpoints.push(new_value);
            } else {
                new_checkpoints.push(s.checkpoints[i]);
            }
            i = i + 1;
        }

        // Prove the update property
        proof {
            // The spec view converts i64 to int via Seq::new
            // We need to show result@.checkpoints == s@.checkpoints.update(idx, new_value)

            // First show the raw Vec has correct values
            assert(new_checkpoints@.len() == s.checkpoints@.len());

            // The spec view of s.checkpoints is Seq::new(..., |i| s.checkpoints@[i] as int)
            // The spec view of result.checkpoints will be Seq::new(..., |i| new_checkpoints@[i] as int)
            // We need: for all j, new_checkpoints@[j] as int == s@.checkpoints.update(idx, new_value)[j]

            let s_spec = Seq::new(s.checkpoints@.len(), |i: int| s.checkpoints@[i] as int);
            let updated_spec = s_spec.update(idx as int, new_value as int);
            let result_spec = Seq::new(new_checkpoints@.len(), |i: int| new_checkpoints@[i] as int);

            assert forall |j: int| 0 <= j < result_spec.len() implies result_spec[j] == updated_spec[j] by {
                if j == idx as int {
                    assert(new_checkpoints@[j] == new_value);
                    assert(result_spec[j] == new_value as int);
                    assert(updated_spec[j] == new_value as int);
                } else {
                    assert(new_checkpoints@[j] == s.checkpoints@[j]);
                    assert(result_spec[j] == s.checkpoints@[j] as int);
                    assert(updated_spec[j] == s_spec[j]);
                    assert(s_spec[j] == s.checkpoints@[j] as int);
                }
            }
            assert(result_spec =~= updated_spec);
        }

        CState {
            checkpoints: new_checkpoints,
            other_field: s.other_field,
        }
    }
}

fn main() {}
