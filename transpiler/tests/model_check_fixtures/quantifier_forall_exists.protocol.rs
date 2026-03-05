verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        &&& s_.x == s.x + 1
        &&& s_.x <= c.upper + 1
    }
}
