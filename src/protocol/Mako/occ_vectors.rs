//! The actual version vector is a maximum of shard clock replies and reads.
//! Its component on every written shard equals that shard's fresh clock ticket.
use vstd::prelude::*;
use vstd::imap::IMap as Map;
use super::occ::*;
use super::occ_proof::{inv, authentic, shape};

verus! {
pub open spec fn bounded(c: Config, v: Map<int, nat>, clocks: Map<int, nat>) -> bool {
    v.dom() == zero(c).dom() && forall|sh: int| 0 <= sh < c.shards ==> #[trigger] v[sh] <= clocks[sh]
}
pub open spec fn read_vectors(c: Config, s: State, id: int) -> bool {
    forall|j: int| 0 <= j < s.tx[id].reads.len() ==>
        bounded(c, #[trigger] s.tx[id].reads[j].version.vc, s.clocks)
        && (forall|sh: int| #[trigger] s.tx[id].tickets.dom().contains(sh) ==> s.tx[id].reads[j].version.vc[sh] < s.tx[id].tickets[sh])
}
pub open spec fn vectors(c: Config, s: State) -> bool {
    &&& forall|k: Key| key(c, k) ==> bounded(c, #[trigger] s.data[k].vc, s.clocks)
    &&& forall|id: int| #[trigger] s.tx.dom().contains(id) ==> read_vectors(c, s, id)
    &&& forall|id: int| #[trigger] s.tx.dom().contains(id) && active(s.tx[id]) ==>
        s.tx[id].vc == vector(c, s.tx[id]) && bounded(c, s.tx[id].vc, s.clocks)
        && (forall|sh: int| #[trigger] s.tx[id].tickets.dom().contains(sh) ==> s.tx[id].vc[sh] == s.tx[id].tickets[sh])
}
pub proof fn maximum_bound(rs: Seq<Read>, sh: int, n: nat, bound: nat)
    requires n <= rs.len(), forall|j: int| 0 <= j < n ==> #[trigger] rs[j].version.vc[sh] <= bound
    ensures read_max(rs, sh, n) <= bound
    decreases n
{
    if n > 0 { maximum_bound(rs, sh, (n-1) as nat, bound); }
}
pub proof fn maximum_covers(rs: Seq<Read>, sh: int, n: nat, j: int)
    requires n <= rs.len(), 0 <= j < n
    ensures rs[j].version.vc[sh] <= read_max(rs, sh, n)
    decreases n
{
    if j < n-1 { maximum_covers(rs, sh, (n-1) as nat, j); }
}
pub proof fn computed_vector(c: Config, s: State, id: int)
    requires shape(c, s), vectors(c, s), s.tx.dom().contains(id)
    ensures bounded(c, vector(c, s.tx[id]), s.clocks),
        forall|sh: int| #[trigger] s.tx[id].tickets.dom().contains(sh) ==> vector(c, s.tx[id])[sh] == s.tx[id].tickets[sh]
{
    assert forall|sh: int| 0 <= sh < c.shards implies #[trigger] vector(c, s.tx[id])[sh] <= s.clocks[sh] by {
        assert forall|j: int| 0 <= j < s.tx[id].reads.len() implies #[trigger] s.tx[id].reads[j].version.vc[sh] <= s.clocks[sh] by { }
        maximum_bound(s.tx[id].reads, sh, s.tx[id].reads.len(), s.clocks[sh]);
    }
    assert forall|sh: int| #[trigger] s.tx[id].tickets.dom().contains(sh) implies vector(c, s.tx[id])[sh] == s.tx[id].tickets[sh] by {
        assert forall|j: int| 0 <= j < s.tx[id].reads.len() implies #[trigger] s.tx[id].reads[j].version.vc[sh] <= s.tx[id].tickets[sh] by { }
        maximum_bound(s.tx[id].reads, sh, s.tx[id].reads.len(), s.tx[id].tickets[sh]);
    }
}
pub proof fn ticket_component(c: Config, s: State, k: Key, v: Version)
    requires shape(c, s), vectors(c, s), key(c, k), authentic(c, s, k, v)
    ensures v.ticket == v.vc[k.shard]
{ }
pub proof fn step_vectors(c: Config, s: State, z: State, a: Action)
    requires inv(c, s), step(c, s, z, a) ensures vectors(c, z)
{
    reveal(step);
    if let Action::Check { id } = a { computed_vector(c, s, id); }
    assert forall|k: Key| key(c, k) implies bounded(c, #[trigger] z.data[k].vc, z.clocks) by { }
    assert forall|id: int| #[trigger] z.tx.dom().contains(id) implies read_vectors(c, z, id) by {
        assert forall|j: int| 0 <= j < z.tx[id].reads.len() implies
            bounded(c, #[trigger] z.tx[id].reads[j].version.vc, z.clocks)
            && (forall|sh: int| #[trigger] z.tx[id].tickets.dom().contains(sh) ==> z.tx[id].reads[j].version.vc[sh] < z.tx[id].tickets[sh]) by {
            match a {
                Action::GetClock { id: t, shard: sh } => { if id == t { assert(bounded(c, s.tx[id].reads[j].version.vc, s.clocks)); } },
                _ => {},
            }
        }
    }
    assert forall|id: int| #[trigger] z.tx.dom().contains(id) && active(z.tx[id]) implies
        z.tx[id].vc == vector(c, z.tx[id]) && bounded(c, z.tx[id].vc, z.clocks)
        && (forall|sh: int| #[trigger] z.tx[id].tickets.dom().contains(sh) ==> z.tx[id].vc[sh] == z.tx[id].tickets[sh]) by { }
}
pub proof fn merged_covers_read(c: Config, t: Tx, sh: int, j: int)
    requires 0 <= sh < c.shards, 0 <= j < t.reads.len()
    ensures t.reads[j].version.vc[sh] <= vector(c, t)[sh]
{ maximum_covers(t.reads, sh, t.reads.len(), j); }
/// Dependency vectors follow from the actual maximum computation.
pub proof fn certified_dependency_clock(c: Config, s: State, id: int, d: int, sh: int)
    requires inv(c, s), s.tx.dom().contains(id), s.tx[id].phase is Certified,
        deps(s, id).contains(d), 0 <= sh < c.shards
    ensures s.tx.dom().contains(d), s.tx[d].phase is Certified, s.tx[d].vc[sh] <= s.tx[id].vc[sh],
        s.tx[d].serial < s.tx[id].serial
{
    let j = choose|j: int| 0 <= j < s.tx[id].reads.len() && #[trigger] s.tx[id].reads[j].version.writer == Some(d);
    merged_covers_read(c, s.tx[id], sh, j);
}
} // verus!
