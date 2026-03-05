verus! {
    pub struct LState {
        pub x: int,
        pub y: bool,
    }

    pub struct LConstants {
        pub target: int,
    }

    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        let updated = LState { x: c.target, ..s };
        &&& updated.x == c.target
        &&& updated.y == s.y
        &&& updated.y
    }
}
