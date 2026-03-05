verus! {
    pub enum LMode {
        A,
        B,
    }

    pub struct LState {
        pub mode: LMode,
        pub ok: bool,
    }

    pub struct LConstants {
        pub preferred_a: bool,
    }

    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        match s.mode {
            LMode::A if c.preferred_a => s.ok,
            LMode::A => !s.ok,
            LMode::B => !s.ok,
        }
    }
}
