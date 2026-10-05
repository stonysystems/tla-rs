use vstd::prelude::*;
use vstd::imap::IMap as Map;
use vstd::iset::ISet as Set;
use super::model::*;
use super::invariants::*;

verus! {

pub proof fn cut_durable(c: Config, s: State, id: int, i: int)
    requires inv(c, s), s.tx.dom().contains(id), s.tx[id].part.dom().contains(i), below_cut(c, s, s.tx[id])
    ensures s.durable.contains((id, i)), s.installed.contains((id, i))
{
    let k = key(s.tx[id], i);
    assert(stream(c, k));
    assert(covered(s.tx[id].vc[i], endpoint(s, k)));
}
pub proof fn partial_install_excluded(c: Config, s: State, id: int, i: int)
    requires inv(c, s), s.tx.dom().contains(id), s.tx[id].part.dom().contains(i),
        !s.installed.contains((id, i)), s.finalized.contains(s.tx[id].epoch)
    ensures doomed(c, s, id)
{
    if below_cut(c, s, s.tx[id]) { cut_durable(c, s, id, i); }
}
pub proof fn dependency_survives(c: Config, s: State, id: int, d: int)
    requires inv(c, s), s.tx.dom().contains(id), s.tx[id].deps.contains(d), below_cut(c, s, s.tx[id])
    ensures below_cut(c, s, s.tx[d])
{
    if s.tx[id].epoch == s.tx[d].epoch {
        assert forall|k: Stream| stream(c, k) && k.epoch == s.tx[d].epoch implies
            covered(s.tx[d].vc[k.shard], #[trigger] endpoint(s, k)) by {
            assert(s.tx[d].vc[k.shard] <= s.tx[id].vc[k.shard]);
        }
    }
}
pub proof fn rollback_dependency(c: Config, s: State, id: int, d: int)
    requires inv(c, s), s.tx.dom().contains(id), s.tx[id].deps.contains(d), doomed(c, s, d)
    ensures doomed(c, s, id), s.tx[id].epoch == s.tx[d].epoch
{
    if below_cut(c, s, s.tx[id]) { dependency_survives(c, s, id, d); }
}
pub open spec fn dep_path(s: State, p: Seq<int>) -> bool {
    p.len() > 0 && (forall|j: int| 0 <= j < p.len() ==> s.tx.dom().contains(#[trigger] p[j]))
        && (forall|j: int| 0 <= j < p.len() - 1 ==> #[trigger] s.tx[p[j + 1]].deps.contains(p[j]))
}
pub proof fn rollback_transitive(c: Config, s: State, p: Seq<int>, j: int)
    requires inv(c, s), dep_path(s, p), 0 <= j < p.len(), doomed(c, s, p[0])
    ensures doomed(c, s, p[j]), s.tx[p[j]].epoch == s.tx[p[0]].epoch
    decreases j
{
    if j > 0 {
        rollback_transitive(c, s, p, j - 1);
        let prev = j - 1;
        assert(s.tx[p[prev + 1]].deps.contains(p[prev]));
        rollback_dependency(c, s, p[j], p[j - 1]);
    }
}
// A logical decision is shared by every writes-i. Physical replay and undo are
// asynchronous; this safety theorem does not assert their eventual scheduling.
pub open spec fn safety(c: Config, s: State) -> bool {
    &&& forall|id: int, i: int| #[trigger] s.acked.contains(id) && #[trigger] s.tx[id].part.dom().contains(i) ==>
        s.durable.contains((id, i)) && !s.rolled.contains((id, i))
    &&& forall|id: int, i: int, j: int| #[trigger] s.replayed.contains((id, i)) ==>
        !#[trigger] s.rolled.contains((id, j))
    &&& forall|id: int, d: int| #[trigger] s.tx.dom().contains(id) && #[trigger] s.tx[id].deps.contains(d) && doomed(c, s, d) ==>
        doomed(c, s, id) && s.tx[id].epoch == s.tx[d].epoch
    &&& forall|id: int, i: int| #[trigger] s.tx.dom().contains(id) && #[trigger] s.tx[id].part.dom().contains(i)
        && s.finalized.contains(s.tx[id].epoch) && !s.installed.contains((id, i)) ==> doomed(c, s, id)
}
pub proof fn inv_safety(c: Config, s: State)
    requires inv(c, s)
    ensures safety(c, s)
{
    assert forall|id: int, i: int| #[trigger] s.acked.contains(id) && #[trigger] s.tx[id].part.dom().contains(i) implies
        s.durable.contains((id, i)) && !s.rolled.contains((id, i)) by { cut_durable(c, s, id, i); }
    assert forall|id: int, d: int| #[trigger] s.tx.dom().contains(id) && #[trigger] s.tx[id].deps.contains(d) && doomed(c, s, d) implies
        doomed(c, s, id) && s.tx[id].epoch == s.tx[d].epoch by { rollback_dependency(c, s, id, d); }
    assert forall|id: int, i: int| #[trigger] s.tx.dom().contains(id) && #[trigger] s.tx[id].part.dom().contains(i)
        && s.finalized.contains(s.tx[id].epoch) && !s.installed.contains((id, i)) implies doomed(c, s, id) by {
        partial_install_excluded(c, s, id, i);
    }
}
/// Unbounded induction: every state of every finite behavior satisfies safety.
pub proof fn theorem_mako_safety(c: Config, h: Seq<State>, i: int)
    requires behavior(c, h), 0 <= i < h.len()
    ensures safety(c, h[i])
{
    behavior_inv(c, h, i);
    inv_safety(c, h[i]);
}

/// At a finalized cut all participants have the same logical outcome.
/// A retained transaction has every fragment durable; an excluded transaction
/// has no acknowledged/replayed fragment, and every installed fragment admits undo.
pub proof fn theorem_final_atomicity(c: Config, h: Seq<State>, j: int, id: int)
    requires behavior(c, h), 0 <= j < h.len(), h[j].tx.dom().contains(id),
        h[j].finalized.contains(h[j].tx[id].epoch)
    ensures
        below_cut(c, h[j], h[j].tx[id]) ==> (forall|i: int| #[trigger] h[j].tx[id].part.dom().contains(i) ==>
            h[j].durable.contains((id, i)) && !h[j].rolled.contains((id, i))),
        !below_cut(c, h[j], h[j].tx[id]) ==> !h[j].acked.contains(id) &&
            (forall|i: int| !#[trigger] h[j].replayed.contains((id, i))) &&
            (forall|i: int| #[trigger] h[j].installed.contains((id, i)) ==>
                rollback(c, h[j], rollback_result(c, h[j], id, i), id, i))
{
    let s = h[j];
    behavior_inv(c, h, j);
    if below_cut(c, s, s.tx[id]) {
        assert forall|i: int| #[trigger] s.tx[id].part.dom().contains(i) implies
            s.durable.contains((id, i)) && !s.rolled.contains((id, i)) by {
            cut_durable(c, s, id, i);
        }
    }
}
pub proof fn theorem_transitive_rollback(c: Config, h: Seq<State>, j: int, p: Seq<int>)
    requires behavior(c, h), 0 <= j < h.len(), dep_path(h[j], p), doomed(c, h[j], p[0])
    ensures doomed(c, h[j], p.last()), h[j].tx[p.last()].epoch == h[j].tx[p[0]].epoch
{
    behavior_inv(c, h, j);
    rollback_transitive(c, h[j], p, p.len() - 1);
}

pub open spec fn epoch_ids(s: State, e: nat) -> Set<int> {
    s.tx.dom().filter(|id: int| s.tx[id].epoch == e)
}
pub proof fn epoch_frozen(c: Config, s: State, z: State, a: Action, e: nat)
    requires inv(c, s), step(c, s, z, a), e < s.epoch
    ensures epoch_ids(s, e) == epoch_ids(z, e), epoch_ids(s, e).finite()
{
    reveal(step);
    assert(epoch_ids(s, e) =~= epoch_ids(z, e));
    vstd::iset_lib::lemma_iset_subset_finite(s.tx.dom(), epoch_ids(s, e));
}
/// Closed epochs have a fixed finite set of candidates. No later transaction
/// joins the rollback set for that epoch, regardless of later failures.
pub proof fn theorem_bounded_rollback(c: Config, h: Seq<State>, i: int, j: int, e: nat)
    requires behavior(c, h), 0 <= i <= j < h.len(), e < h[i].epoch
    ensures epoch_ids(h[i], e) == epoch_ids(h[j], e), epoch_ids(h[i], e).finite()
    decreases j - i
{
    behavior_inv(c, h, i);
    if i == j {
        vstd::iset_lib::lemma_iset_subset_finite(h[i].tx.dom(), epoch_ids(h[i], e));
    } else {
        assert(next(c, h[i], h[i+1]));
        let a = choose|a: Action| #[trigger] step(c, h[i], h[i+1], a);
        step_frame(c, h[i], h[i+1], a);
        epoch_frozen(c, h[i], h[i+1], a, e);
        theorem_bounded_rollback(c, h, i + 1, j, e);
    }
}
pub proof fn history_frame(c: Config, h: Seq<State>, i: int, j: int)
    requires behavior(c, h), 0 <= i <= j < h.len()
    ensures
        h[i].epoch <= h[j].epoch,
        forall|id: int| #[trigger] h[i].tx.dom().contains(id) ==> h[j].tx.dom().contains(id) && h[j].tx[id] == h[i].tx[id],
        h[i].acked.subset_of(h[j].acked), h[i].replayed.subset_of(h[j].replayed),
        forall|k: Stream| #[trigger] h[i].closed.contains(k) ==> endpoint(h[i], k) == endpoint(h[j], k),
        h[i].closed.subset_of(h[j].closed)
    decreases j - i
{
    if i < j {
        history_frame(c, h, i + 1, j);
        behavior_inv(c, h, i);
        assert(next(c, h[i], h[i+1]));
        let a = choose|a: Action| #[trigger] step(c, h[i], h[i+1], a);
        step_frame(c, h[i], h[i+1], a);
        reveal(step);
    }
}
/// Acknowledgment is permanent, including across arbitrarily many recoveries.
pub proof fn theorem_ack_irrevocable(c: Config, h: Seq<State>, i: int, j: int, id: int, sh: int)
    requires behavior(c, h), 0 <= i <= j < h.len(), h[i].acked.contains(id), h[i].tx[id].part.dom().contains(sh)
    ensures h[j].durable.contains((id, sh)), !h[j].rolled.contains((id, sh)), !doomed(c, h[j], id)
{
    history_frame(c, h, i, j);
    behavior_inv(c, h, i);
    behavior_inv(c, h, j);
    cut_durable(c, h[j], id, sh);
}
/// Re-running recovery computes the same final cut from frozen stream prefixes.
pub proof fn theorem_final_cut_stable(c: Config, h: Seq<State>, i: int, j: int, t: Tx)
    requires behavior(c, h), 0 <= i <= j < h.len(), h[i].finalized.contains(t.epoch)
    ensures below_cut(c, h[i], t) == below_cut(c, h[j], t)
{
    history_frame(c, h, i, j);
    behavior_inv(c, h, i);
    final_cut_fixed(c, h[i], h[j], t);
}
} // verus!
