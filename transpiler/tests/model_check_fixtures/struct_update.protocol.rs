verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        &&& s_.x == s.x
        &&& s_.y == !s.y
        &&& c.target >= 0
    }
}
