verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value == s.value && s.value <= c.limit
    }

    pub open spec fn LInv(s: LState, c: LConstants) -> bool {
        s.value <= c.limit
    }
}
