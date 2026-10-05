//! Composes the independently checked OCC and watermark layers at their
//! transaction-record interface. Correspondence is explicit, not an OCC oracle.
use vstd::prelude::*;
use vstd::iset::ISet as Set;
use vstd::imap::IMap as Map;
use super::occ as o;
use super::occ_proof as op;
use super::production as p;
use super::production_proof as pp;
use super::model as a;
use super::safety as safe;

verus! {
// This theorem needs no assumed dependency closure or production history.
// Every componentwise vector cut is closed under the actual OCC read-from edges.
pub open spec fn below(c: o::Config, t: o::Tx, cut: Map<int, a::Bound>) -> bool {
    forall|sh: int| 0 <= sh < c.shards ==> a::covered(t.vc[sh], #[trigger] cut[sh])
}
pub open spec fn vector_cut(c: o::Config, s: o::State, cut: Map<int, a::Bound>) -> Set<int> {
    op::certified(s).filter(|id: int| below(c, s.tx[id], cut))
}
pub proof fn vector_cut_closed(c: o::Config, s: o::State, cut: Map<int, a::Bound>)
    requires op::inv(c, s) ensures op::closed(s, vector_cut(c, s, cut))
{
    op::certified_closed(c, s);
    assert forall|id: int, d: int| #[trigger] vector_cut(c, s, cut).contains(id) && #[trigger] o::deps(s, id).contains(d)
        implies vector_cut(c, s, cut).contains(d) by {
        assert(op::certified(s).contains(d));
        assert forall|sh: int| 0 <= sh < c.shards implies a::covered(s.tx[d].vc[sh], #[trigger] cut[sh]) by {
            super::occ_vectors::certified_dependency_clock(c, s, id, d, sh);
            assert(a::covered(s.tx[id].vc[sh], cut[sh]));
        }
    }
}
pub proof fn theorem_vector_cut_serializable(c: o::Config, h: Seq<o::State>, j: int, cut: Map<int, a::Bound>)
    requires o::behavior(c, h), 0 <= j < h.len(), cut.dom() == o::zero(c).dom()
    ensures op::serializable(c, h[j], vector_cut(c, h[j], cut))
{
    op::behavior_inv(c, h, j);
    vector_cut_closed(c, h[j], cut);
    op::inv_serializable(c, h[j], vector_cut(c, h[j], cut));
}
// One OCC epoch uses the same transaction identities and computed version vectors
// as the producer history. Read-from closure is proved, not supplied.
// A participant covers every key written on its shard.
// Older stable versions are the arbitrary base database of this OCC epoch.
pub open spec fn correspondence(oc: o::Config, s: o::State, pc: p::Settings, ps: p::State, e: nat) -> bool {
    &&& oc.shards == pc.protocol.shards
    &&& forall|id: int| #[trigger] op::certified(s).contains(id) ==>
        ps.core.tx.dom().contains(id) && ps.core.tx[id].epoch == e
        && ps.core.tx[id].vc == s.tx[id].vc
    &&& forall|id: int, k: o::Key| #[trigger] op::certified(s).contains(id)
        && #[trigger] s.tx[id].writes.dom().contains(k) ==> ps.core.tx[id].part.dom().contains(k.shard)
}
pub open spec fn retained(s: o::State, ps: p::State, pc: p::Settings) -> Set<int> {
    op::certified(s).filter(|id: int| a::below_cut(pc.protocol, ps.core, ps.core.tx[id]))
}
pub proof fn produced_cut_closed(oc: o::Config, s: o::State, pc: p::Settings, ps: p::State, e: nat)
    requires op::inv(oc, s), pp::inv(pc, ps), correspondence(oc, s, pc, ps, e)
    ensures op::closed(s, retained(s, ps, pc))
{
    op::certified_closed(oc, s);
    assert forall|id: int, d: int| #[trigger] retained(s, ps, pc).contains(id) && #[trigger] o::deps(s, id).contains(d)
        implies retained(s, ps, pc).contains(d) by {
        assert(op::certified(s).contains(d));
        assert forall|k: a::Stream| a::stream(pc.protocol, k) && k.epoch == ps.core.tx[d].epoch implies
            a::covered(ps.core.tx[d].vc[k.shard], #[trigger] a::endpoint(ps.core, k)) by {
            super::occ_vectors::certified_dependency_clock(oc, s, id, d, k.shard);
            assert(a::covered(ps.core.tx[id].vc[k.shard], a::endpoint(ps.core, k)));
        }
    }
}
/// The watermark cut preserves the serial semantics of explicitly validated
/// reads; key writes of every retained transaction are on durable fragments.
pub proof fn theorem_occ_and_watermark_safety(oc: o::Config, oh: Seq<o::State>, oi: int,
    pc: p::Settings, ph: Seq<p::State>, pi: int, e: nat)
    requires o::behavior(oc, oh), 0 <= oi < oh.len(), p::behavior(pc, ph), 0 <= pi < ph.len(),
        correspondence(oc, oh[oi], pc, ph[pi], e)
    ensures op::serializable(oc, oh[oi], retained(oh[oi], ph[pi], pc)),
        safe::safety(pc.protocol, ph[pi].core),
        forall|id: int, k: o::Key| #[trigger] retained(oh[oi], ph[pi], pc).contains(id)
            && #[trigger] oh[oi].tx[id].writes.dom().contains(k) ==> ph[pi].core.durable.contains((id, k.shard))
{
    op::behavior_inv(oc, oh, oi);
    pp::behavior_inv(pc, ph, pi);
    produced_cut_closed(oc, oh[oi], pc, ph[pi], e);
    op::inv_serializable(oc, oh[oi], retained(oh[oi], ph[pi], pc));
    safe::inv_safety(pc.protocol, ph[pi].core);
    assert forall|id: int, k: o::Key| #[trigger] retained(oh[oi], ph[pi], pc).contains(id)
        && #[trigger] oh[oi].tx[id].writes.dom().contains(k) implies ph[pi].core.durable.contains((id, k.shard)) by {
        safe::cut_durable(pc.protocol, ph[pi].core, id, k.shard);
    }
}
} // verus!
