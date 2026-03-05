verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        &&& s_.mode == s.mode
        &&& s_.ok == !s.ok
        &&& c.preferred_a
    }
}
