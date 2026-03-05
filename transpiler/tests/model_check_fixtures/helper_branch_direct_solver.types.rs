verus! {
    pub struct LState {
        pub value: int,
    }

    pub struct LConstants {
        pub limit: int,
    }

    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        s.value == 0 && c.limit == 1
    }
}
