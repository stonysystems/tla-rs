verus! {
    pub open spec fn LStep(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value <= c.limit
    }

    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s.value == 1 && LStep(s, s_, c)
    }
}
