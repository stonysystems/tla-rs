//! Client-level consistency over the ghost operation history (§2.2).
//! Happens-before is session order, fan-out, and a read observing a write whose
//! clock is at most the clock the server returned, closed transitively.
use vstd::prelude::*;
use super::vc::*;
use super::types::*;

verus! {

pub open spec fn actor(e: Event) -> int {
    match e {
        Event::Write { client, .. } => client,
        Event::Read { client, .. } => client,
        Event::Fork { parent, .. } => parent,
    }
}

pub open spec fn session_edge(h: Seq<Event>, i: int, j: int) -> bool {
    actor(h[i]) == actor(h[j]) || (h[i] is Fork && h[i]->Fork_child == actor(h[j]))
}

pub open spec fn observes(h: Seq<Event>, i: int, j: int) -> bool {
    &&& h[i] is Write && h[j] is Read
    &&& h[i]->Write_version.key == h[j]->Read_key
    &&& le(h[i]->Write_version.vc, h[j]->Read_server_vc)
}

/// One happens-before edge from position i to a later position j.
pub open spec fn edge(h: Seq<Event>, i: int, j: int) -> bool {
    0 <= i < j < h.len() && (session_edge(h, i, j) || observes(h, i, j))
}

pub open spec fn hb_path(h: Seq<Event>, p: Seq<int>) -> bool {
    &&& p.len() >= 2
    &&& forall|t: int, u: int| #![trigger p[t], p[u]]
        0 <= t && u == t + 1 && u < p.len() ==> edge(h, p[t], p[u])
}

pub open spec fn hb(h: Seq<Event>, i: int, j: int) -> bool {
    exists|p: Seq<int>| #[trigger] hb_path(h, p) && p[0] == i && p.last() == j
}

/// CC+ (§2.2, clause 3): a read reflects every write to its key that
/// happens before it, directly or transitively.
pub open spec fn causal_visibility(h: Seq<Event>) -> bool {
    forall|i: int, j: int| #[trigger] hb(h, i, j) && h[i] is Write && h[j] is Read
        && h[i]->Write_version.key == h[j]->Read_key
        ==> le(h[i]->Write_version.vc, h[j]->Read_vc)
}

/// Theorem 1 (read your writes).
pub open spec fn read_your_writes(h: Seq<Event>) -> bool {
    forall|i: int, j: int| #![trigger h[i], h[j]] 0 <= i < j < h.len() && h[i] is Write && h[j] is Read
        && actor(h[i]) == actor(h[j]) && h[i]->Write_version.key == h[j]->Read_key
        ==> le(h[i]->Write_version.vc, h[j]->Read_vc)
}

/// Theorem 2 (monotonic reads), for the version the client observes.
pub open spec fn monotonic_reads(h: Seq<Event>) -> bool {
    forall|i: int, j: int| #![trigger h[i], h[j]] 0 <= i < j < h.len() && h[i] is Read && h[j] is Read
        && actor(h[i]) == actor(h[j]) && h[i]->Read_key == h[j]->Read_key
        ==> le(h[i]->Read_vc, h[j]->Read_vc)
}

/// Monotonic reads along happens-before: a read that happens after another
/// read of the same key, in any session, dominates it.
pub open spec fn causal_monotonic_reads(h: Seq<Event>) -> bool {
    forall|i: int, j: int| #[trigger] hb(h, i, j) && h[i] is Read && h[j] is Read
        && h[i]->Read_key == h[j]->Read_key
        ==> le(h[i]->Read_vc, h[j]->Read_vc)
}

/// Theorem 3 (writes follow reads): a reader of the write also observes the
/// version the writer read, or a newer one.
pub open spec fn writes_follow_reads(h: Seq<Event>) -> bool {
    forall|i: int, j: int, k: int, l: int| #![trigger h[i], h[j], h[k], h[l]]
        0 <= i < j < k < l < h.len()
        && h[i] is Read && h[j] is Write && actor(h[i]) == actor(h[j])
        && observes(h, j, k) && h[l] is Read && actor(h[k]) == actor(h[l])
        && h[l]->Read_key == h[i]->Read_key
        ==> le(h[i]->Read_server_vc, h[l]->Read_vc)
}

/// Theorem 4 (monotonic writes).
pub open spec fn monotonic_writes(h: Seq<Event>) -> bool {
    forall|i: int, j: int, k: int, l: int| #![trigger h[i], h[j], h[k], h[l]]
        0 <= i < j < k < l < h.len()
        && h[i] is Write && h[j] is Write && actor(h[i]) == actor(h[j])
        && observes(h, j, k) && h[l] is Read && actor(h[k]) == actor(h[l])
        && h[l]->Read_key == h[i]->Write_version.key
        ==> le(h[i]->Write_version.vc, h[l]->Read_vc)
}

/// Every read returns the initial value with a zero clock, or the value of a
/// write to its key that happens before the read and that its clock dominates.
pub open spec fn reads_valid(h: Seq<Event>) -> bool {
    forall|j: int| #![trigger h[j]] 0 <= j < h.len() && h[j] is Read ==>
        (h[j]->Read_vc == zero(h[j]->Read_vc.len()) && h[j]->Read_value == 0)
        || exists|i: int| #[trigger] hb(h, i, j) && h[i] is Write
            && h[i]->Write_version.key == h[j]->Read_key
            && h[i]->Write_version.value == h[j]->Read_value
            && le(h[i]->Write_version.vc, h[j]->Read_vc)
}

} // verus!
