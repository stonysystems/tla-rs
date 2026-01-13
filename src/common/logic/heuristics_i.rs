#![allow(unused_imports)]
use super::temporal_s::*;
use crate::common::collections::maps2::*;
use builtin::*;
use builtin_macros::*;
use vstd::{modes::*, prelude::*, seq::*, *};

verus! {
    pub open spec fn TBlast(i:int) -> bool { true }
    ////////////////////
    // LEMMAS
    ////////////////////

    // Conservative heuristics; not complete
    // (e.g. won't prove <>[]A ==> []<>A)
    pub proof fn TemporalAssist()
        ensures  forall |i:int, x:temporal| #![trigger sat(i, always(x))] sat(i, always(x)) =~= (forall |j:int| TLe(i, j) ==> sat(j, x)),
            forall |i:int, x:temporal| #![trigger sat(i, eventual(x))] sat(i, eventual(x)) =~= (exists |j:int| TLe(i, j) && sat(j, x)),
            TLe(0, 0)
    {
        assert forall |i:int, x:temporal| #![trigger sat(i, always(x))] sat(i, always(x)) =~= (forall |j: int| TLe(i, j) ==> sat(j, x)) by
        {
            // reveal always();
            let f = Map::new(|ii: int| ii == ii, |ii: int| forall |j: int| ii <= j ==> sat(j, x));
            calc!{
            (==)
            sat(i, always(x)); {}
            sat(i, stepmap(f)); {}
            f[i];
            }
        }

        assert(forall |i:int, x:temporal| #![trigger sat(i, eventual(x))] sat(i, eventual(x)) =~= (exists |j:int| TLe(i, j) && sat(j, x)));
    }

    // Moderately aggressive heuristics
    pub proof fn TemporalBlast()
    ensures forall |i:int, x:temporal| #![trigger sat(i, always(x))] sat(i, always(x)) =~= (forall |j:int| TLe(i, j) ==> sat(j, x)),
            forall |i:int, x:temporal| #![trigger sat(i, eventual(x))] sat(i, eventual(x)) =~= (exists |j:int| TLe(i, j) && sat(j, x)),
            forall |i:int, j1:int, j2:int| #![trigger TLe(i, j1), TLe(i, j2)] TLe(j1, j2) || TLe(j2, j1),
            TLe(0, 0)
    {
        assert forall |i:int, x:temporal| #![trigger sat(i, always(x))] sat(i, always(x)) =~= (forall |j: int| TLe(i, j) ==> sat(j, x)) by
        {
            // reveal always();
            let f = Map::new(|ii: int| ii == ii, |ii: int| forall |j: int| ii <= j ==> sat(j, x));
            calc!{
            (==)
            sat(i, always(x)); {}
            sat(i, stepmap(f)); {}
            f[i];
            }
        }

        assert(forall |i:int, x:temporal| #![trigger sat(i, eventual(x))] sat(i, eventual(x)) =~= (exists |j:int| TLe(i, j) && sat(j, x)));
    }

    // Most aggressive heuristics; might not terminate
    // (e.g. won't terminate on invalid formula <>[](A || B) ==> <>[]A || <>[]B)
    pub proof fn TemporalFullBlast()
    ensures  forall |i:int, x:temporal| #![trigger sat(i, always(x))] sat(i, always(x)) =~= (forall |j:int| #![trigger sat(j, x)]#![trigger TBlast(j)] TBlast(j) ==> i <= j ==> sat(j, x)),
                forall |i:int, x:temporal| #![trigger sat(i, eventual(x))] sat(i, eventual(x)) =~= (exists |j:int| #![trigger sat(j, x)]#![trigger TBlast(j)] TBlast(j) && i <= j && sat(j, x)),
                TBlast(0),
    {
        assert forall |i:int, x:temporal| #![trigger sat(i, always(x))] sat(i, always(x)) =~= (forall |j: int| TLe(i, j) ==> sat(j, x)) by
        {
            // reveal always();
            let f = Map::new(|ii: int| ii == ii, |ii: int| forall |j: int| ii <= j ==> sat(j, x));
            calc!{
            (==)
            sat(i, always(x)); {}
            sat(i, stepmap(f)); {}
            f[i];
            }
        }

        assert(forall |i:int, x:temporal| #![trigger sat(i, eventual(x))] sat(i, eventual(x)) =~= (exists |j:int| TLe(i, j) && sat(j, x)));
    }
}
