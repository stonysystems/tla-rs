use vstd::prelude::*;

verus! {
    /// The initial counter value is zero.
    // @automan predicate(value: out)
    pub open spec fn LInit(value: int) -> bool {
        value == 0
    }

    /// One counter step relates the old value to the new value.
    // @automan predicate(value: in, value_: out)
    pub open spec fn LIncrement(value: int, value_: int) -> bool {
        value_ == value + 1
    }
}
