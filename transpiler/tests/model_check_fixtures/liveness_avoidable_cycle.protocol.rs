verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        (s.value == 0 && s_.value == 1 && s_.value <= c.limit)
        || (s.value == 1 && s_.value == 0 && s_.value <= c.limit)
        || (s.value == 0 && s_.value == 2 && s_.value <= c.limit)
        || (s.value == 1 && s_.value == 2 && s_.value <= c.limit)
        || (s.value == 2 && s_.value == 2 && s_.value <= c.limit)
    }

    pub open spec fn LFrom(s: LState, c: LConstants) -> bool {
        s.value == 0 && 0 <= c.limit
    }

    pub open spec fn LTo(s: LState, c: LConstants) -> bool {
        s.value == 2 && 0 <= c.limit
    }
}
