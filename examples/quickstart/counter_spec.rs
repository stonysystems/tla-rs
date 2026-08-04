use vstd::prelude::*;

verus! {
    /// The initial counter value is zero.
    pub open spec fn LInit(value: int) -> bool {
        value == 0
    }

    /// One counter step relates the old value to the new value.
    pub open spec fn LIncrement(value: int, value_: int) -> bool {
        value_ == value + 1
    }
}
