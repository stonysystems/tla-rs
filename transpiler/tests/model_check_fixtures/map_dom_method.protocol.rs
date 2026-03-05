verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        &&& s_.votes == s.votes
        &&& s_.ok == !s.ok
        &&& c.probe >= 0
    }
}
