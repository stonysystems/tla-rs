verus! {
    pub struct LState {
        pub votes: Map<int, bool>,
        pub ok: bool,
    }

    pub struct LConstants {
        pub probe: int,
    }

    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        &&& s.votes.contains_key(c.probe)
        &&& s.votes.dom().contains(c.probe)
        &&& s.ok == s.votes.dom().contains(c.probe)
    }
}
