verus! {
    pub struct LState {
        pub x: int,
    }

    pub struct LConstants {
        pub lower: int,
        pub upper: int,
    }

    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        &&& s.x == c.lower
        &&& forall |i: int| (i >= c.lower && i <= c.upper) ==> i >= c.lower
        &&& forall |i: int, j: int| (i >= c.lower && j <= c.upper) ==> i <= j + c.upper
        &&& exists |k: int| k == s.x
        &&& exists |a: int, b: int| a == c.upper && b == s.x
    }
}
