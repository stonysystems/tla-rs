verus! {
    pub open spec fn LStep(s: LState, s_: LState, c: LConstants) -> bool {
        (s.value == 0 && s_.value == 1 && s_.value <= c.limit)
        || (s.value == 1 && s_.value == 1 && s_.value <= c.limit)
    }

    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        LStep(s, s_, c)
    }
}
