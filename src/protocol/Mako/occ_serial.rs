//! Sequential execution witness for the OCC serial order.
use vstd::prelude::*;
use vstd::iset::ISet as Set;
use super::occ::*;
use super::occ_proof::*;

verus! {
pub open spec fn at(s: State, keep: Set<int>, n: nat) -> Option<int> {
    if exists|id: int| #[trigger] keep.contains(id) && s.tx[id].serial == n {
        Some(choose|id: int| #[trigger] keep.contains(id) && s.tx[id].serial == n)
    } else { None }
}
// Execute retained transactions in increasing serial order. Gaps from aborted
// or rolled-back transactions are no-ops. The function is total for every n.
pub open spec fn execute(c: Config, s: State, keep: Set<int>, k: Key, n: nat) -> int
    decreases n
{
    if n == 0 { c.base[k] }
    else { match at(s, keep, n) {
        Some(id) => if s.tx[id].writes.dom().contains(k) { s.tx[id].writes[k] }
            else { execute(c, s, keep, k, (n-1) as nat) },
        None => execute(c, s, keep, k, (n-1) as nat),
    } }
}
pub proof fn last_writer_value(c: Config, s: State, keep: Set<int>, k: Key, v: Version, n: nat)
    requires serializable(c, s, keep), v.serial <= n,
        (match v.writer {
            None => v.serial == 0 && v.value == c.base[k],
            Some(w) => keep.contains(w) && s.tx[w].serial == v.serial
                && s.tx[w].writes.dom().contains(k) && s.tx[w].writes[k] == v.value,
        }),
        forall|w: int| #[trigger] keep.contains(w) && s.tx[w].writes.dom().contains(k)
            && s.tx[w].serial <= n ==> s.tx[w].serial <= v.serial
    ensures execute(c, s, keep, k, n) == v.value
    decreases n
{
    if n > 0 {
        if v.serial == n {
            if let Some(w) = v.writer {
                assert(exists|id: int| #[trigger] keep.contains(id) && s.tx[id].serial == n);
                let id = choose|id: int| #[trigger] keep.contains(id) && s.tx[id].serial == n;
                assert(id == w);
                assert(at(s, keep, n) == Some(w));
            }
        } else {
            if let Some(w) = at(s, keep, n) { assert(!s.tx[w].writes.dom().contains(k)); }
            last_writer_value(c, s, keep, k, v, (n-1) as nat);
        }
    }
}
/// Each observed read equals ordinary sequential execution immediately before
/// its transaction. This includes any dependency-closed rollback subset.
pub proof fn theorem_sequential_reads(c: Config, s: State, keep: Set<int>, id: int, j: int)
    requires serializable(c, s, keep), keep.contains(id), 0 <= j < s.tx[id].reads.len()
    ensures execute(c, s, keep, s.tx[id].reads[j].key, (s.tx[id].serial-1) as nat) == s.tx[id].reads[j].version.value
{
    last_writer_value(c, s, keep, s.tx[id].reads[j].key, s.tx[id].reads[j].version, (s.tx[id].serial-1) as nat);
}
pub proof fn history_frame(c: Config, h: Seq<State>, i: int, j: int)
    requires behavior(c, h), 0 <= i <= j < h.len()
    ensures h[i].serial <= h[j].serial,
        forall|id: int| #[trigger] h[i].tx.dom().contains(id) ==> h[j].tx.dom().contains(id)
            && (h[i].tx[id].phase is Certified ==> h[j].tx[id] == h[i].tx[id])
    decreases j-i
{
    if i < j {
        history_frame(c, h, i, j-1); behavior_inv(c, h, j-1);
        let p = j-1; assert(next(c, h[p], h[p+1]));
        let a = choose|a: Action| #[trigger] step(c, h[p], h[j], a);
        frame(c, h[p], h[j], a);
    }
}
pub proof fn later_transaction(c: Config, h: Seq<State>, i: int, j: int, id: int)
    requires behavior(c, h), 0 <= i <= j < h.len(), !h[i].tx.dom().contains(id)
    ensures h[j].tx.dom().contains(id) && h[j].tx[id].serial > 0 ==> h[i].serial < h[j].tx[id].serial
    decreases j-i
{
    if i < j {
        later_transaction(c, h, i, j-1, id);
        history_frame(c, h, i, j-1); behavior_inv(c, h, j-1);
        let p = j-1; assert(next(c, h[p], h[p+1]));
        let a = choose|a: Action| #[trigger] step(c, h[p], h[j], a);
        reveal(step);
    }
}
/// Certification precedes final completion. Hence this stronger ordering also
/// respects real time whenever one transaction completes before another opens.
pub proof fn theorem_real_time_order(c: Config, h: Seq<State>, i: int, j: int, before: int, after: int)
    requires behavior(c, h), 0 <= i <= j < h.len(), h[i].tx.dom().contains(before), h[i].tx[before].phase is Certified,
        !h[i].tx.dom().contains(after), h[j].tx.dom().contains(after), h[j].tx[after].phase is Certified
    ensures h[j].tx[before].serial < h[j].tx[after].serial
{
    behavior_inv(c, h, i); behavior_inv(c, h, j);
    history_frame(c, h, i, j); later_transaction(c, h, i, j, after);
}
} // verus!
