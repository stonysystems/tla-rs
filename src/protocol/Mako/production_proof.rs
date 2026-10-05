//! Inductive proof of watermark production and refinement to the abstract
//! transaction protocol. The global bound is an invariant, never a guard.
use vstd::prelude::*;
use vstd::imap::IMap as Map;
use vstd::iset::ISet as Set;
use super::model as abs;
use super::model::{Bound, Stream, Tx, bound_le, covered, endpoint, shard, stream};
use super::invariants as ai;
use super::safety as safe;
use super::watermark_math::*;
use super::production::*;

verus! {

pub open spec fn endpoints(c: Settings, s: abs::State) -> Map<Stream, Bound> {
    Map::new(|k: Stream| stream(c.protocol, k), |k: Stream| endpoint(s, k))
}
pub open spec fn lower(c: Settings, s: abs::State, e: nat, sh: int, b: Bound) -> bool {
    forall|w: int| 0 <= w < c.protocol.workers ==> bound_le(b, #[trigger] endpoint(s, worker(e, sh, w)))
}
pub open spec fn complete(c: Settings, s: abs::State, e: nat, sh: int) -> bool {
    forall|w: int| 0 <= w < c.protocol.workers ==> #[trigger] s.closed.contains(worker(e, sh, w))
}
pub open spec fn exact(c: Settings, s: abs::State, e: nat, sh: int, b: Bound) -> bool {
    complete(c, s, e, sh) && b == minimum(endpoints(c, s), e, sh, c.protocol.workers as nat)
}
pub open spec fn data_ok(c: Settings, s: State) -> bool {
    &&& c.observers > 0
    &&& s.reports.dom() == Set::new(|k: Stream| stream(c.protocol, k))
    &&& s.local.dom() == Set::new(|p: (nat, int)| shard(c.protocol, p.1))
    &&& s.views.dom() == Set::new(|p: (int, nat, int)| observer(c, p.0) && shard(c.protocol, p.2))
    &&& s.sealed_reports.subset_of(s.reports.dom())
    &&& s.sealed_local.subset_of(s.local.dom())
    &&& s.sealed_views.subset_of(s.views.dom())
    &&& forall|k: Stream| stream(c.protocol, k) ==>
        bound_le(#[trigger] s.reports[k], endpoint(s.core, k)) &&
        (s.sealed_reports.contains(k) ==> s.core.closed.contains(k) && s.reports[k] == endpoint(s.core, k))
    &&& forall|p: (nat, int)| shard(c.protocol, p.1) ==>
        lower(c, s.core, p.0, p.1, #[trigger] s.local[p])
        && bound_le(s.local[p], minimum(s.reports, p.0, p.1, c.protocol.workers as nat))
        && (s.sealed_local.contains(p) ==> all_reported(c, s, p.0, p.1) && exact(c, s.core, p.0, p.1, s.local[p]))
    &&& forall|p: (int, nat, int)| observer(c, p.0) && shard(c.protocol, p.2) ==>
        lower(c, s.core, p.1, p.2, #[trigger] s.views[p])
        && bound_le(s.views[p], s.core.wm[(p.1, p.2)])
        && (s.sealed_views.contains(p) ==> exact(c, s.core, p.1, p.2, s.views[p]))
}
pub open spec fn messages_ok(c: Settings, s: State) -> bool {
    &&& forall|m: WorkerReport| #[trigger] s.worker_net.contains(m) ==> stream(c.protocol, m.stream)
        && bound_le(m.value, endpoint(s.core, m.stream))
        && (m.sealed ==> s.core.closed.contains(m.stream) && m.value == endpoint(s.core, m.stream))
    &&& forall|m: Gossip| #[trigger] s.gossip_net.contains(m) ==> observer(c, m.dst) && shard(c.protocol, m.shard)
        && lower(c, s.core, m.epoch, m.shard, m.value)
        && (m.sealed ==> exact(c, s.core, m.epoch, m.shard, m.value))
}
pub open spec fn inv(c: Settings, s: State) -> bool {
    ai::inv(c.protocol, s.core) && data_ok(c, s) && messages_ok(c, s)
}
pub proof fn lower_min(c: Settings, s: abs::State, e: nat, sh: int, b: Bound)
    requires abs::valid(c.protocol), shard(c.protocol, sh)
    ensures lower(c, s, e, sh, b) == bound_le(b, minimum(endpoints(c, s), e, sh, c.protocol.workers as nat))
{
    let v = endpoints(c, s);
    if lower(c, s, e, sh, b) {
        assert forall|w: int| 0 <= w < c.protocol.workers implies bound_le(b, #[trigger] v[worker(e, sh, w)]) by { }
        minimum_greatest(v, e, sh, c.protocol.workers as nat, b);
    } else if bound_le(b, minimum(v, e, sh, c.protocol.workers as nat)) {
        assert forall|w: int| 0 <= w < c.protocol.workers implies bound_le(b, #[trigger] endpoint(s, worker(e, sh, w))) by {
            minimum_lower(v, e, sh, c.protocol.workers as nat, w);
            order(b, minimum(v, e, sh, c.protocol.workers as nat), v[worker(e, sh, w)]);
        }
    }
}
pub proof fn lower_max(c: Settings, s: abs::State, e: nat, sh: int, a: Bound, b: Bound)
    requires lower(c, s, e, sh, a), lower(c, s, e, sh, b)
    ensures lower(c, s, e, sh, bmax(a, b))
{
    assert forall|w: int| 0 <= w < c.protocol.workers implies
        bound_le(bmax(a, b), #[trigger] endpoint(s, worker(e, sh, w))) by {
        order(a, b, endpoint(s, worker(e, sh, w)));
    }
}
pub proof fn exact_max(c: Settings, s: abs::State, e: nat, sh: int, a: Bound, b: Bound)
    requires abs::valid(c.protocol), shard(c.protocol, sh), lower(c, s, e, sh, a), lower(c, s, e, sh, b),
        exact(c, s, e, sh, a) || exact(c, s, e, sh, b)
    ensures exact(c, s, e, sh, bmax(a, b))
{
    lower_min(c, s, e, sh, a); lower_min(c, s, e, sh, b);
    order(a, b, minimum(endpoints(c, s), e, sh, c.protocol.workers as nat));
}
pub open spec fn views_bounded(c: Settings, s: State) -> bool {
    forall|p: (int, nat, int)| observer(c, p.0) && shard(c.protocol, p.2) ==>
        bound_le(#[trigger] s.views[p], s.core.wm[(p.1, p.2)])
}
pub proof fn view_covered(c: Settings, s: State, o: int, t: Tx)
    requires views_bounded(c, s), observer(c, o), abs::below_wm(c.protocol, view(c, s, o), t)
    ensures abs::below_wm(c.protocol, s.core, t)
{
    assert forall|i: int| shard(c.protocol, i) implies covered(t.vc[i], #[trigger] s.core.wm[(t.epoch, i)]) by {
        assert(covered(t.vc[i], view(c, s, o).wm[(t.epoch, i)]));
        ai::covered_trans(t.vc[i], s.views[(o, t.epoch, i)], s.core.wm[(t.epoch, i)]);
    }
}
pub proof fn final_view(c: Settings, s: State, o: int, t: Tx)
    requires inv(c, s), observer(c, o), all_final(c, s, o, t.epoch)
    ensures abs::below_wm(c.protocol, view(c, s, o), t) == abs::below_cut(c.protocol, s.core, t),
        forall|k: Stream| stream(c.protocol, k) && k.epoch == t.epoch ==> #[trigger] s.core.closed.contains(k)
{
    assert forall|k: Stream| stream(c.protocol, k) && k.epoch == t.epoch implies #[trigger] s.core.closed.contains(k) by {
        assert(s.sealed_views.contains((o, t.epoch, k.shard)));
        assert(exact(c, s.core, t.epoch, k.shard, s.views[(o, t.epoch, k.shard)]));
        assert(worker(t.epoch, k.shard, k.worker) == k);
    }
    if abs::below_wm(c.protocol, view(c, s, o), t) {
        assert forall|k: Stream| stream(c.protocol, k) && k.epoch == t.epoch implies
            covered(t.vc[k.shard], #[trigger] endpoint(s.core, k)) by {
            assert(worker(t.epoch, k.shard, k.worker) == k);
            assert(covered(t.vc[k.shard], view(c, s, o).wm[(t.epoch, k.shard)]));
            ai::covered_trans(t.vc[k.shard], s.views[(o, t.epoch, k.shard)], endpoint(s.core, k));
        }
    } else if abs::below_cut(c.protocol, s.core, t) {
        assert forall|i: int| shard(c.protocol, i) implies covered(t.vc[i], #[trigger] view(c, s, o).wm[(t.epoch, i)]) by {
            assert forall|w: int| 0 <= w < c.protocol.workers implies
                bound_le(Bound::Finite(t.vc[i]), #[trigger] endpoint(s.core, worker(t.epoch, i, w))) by {
                assert(stream(c.protocol, worker(t.epoch, i, w)));
            }
            lower_min(c, s.core, t.epoch, i, Bound::Finite(t.vc[i]));
            assert(s.sealed_views.contains((o, t.epoch, i)));
        }
    }
}
#[verifier::rlimit(10)]
pub proof fn begin_refines(c: Settings, s: State, o: int, id: int, tx: Tx)
    requires views_bounded(c, s), observer(c, o),
        abs::begin(c.protocol, view(c, s, o), abs::begin_result(c.protocol, view(c, s, o), id, tx), id, tx)
    ensures abs::begin(c.protocol, s.core, abs::begin_result(c.protocol, s.core, id, tx), id, tx)
{
    assert forall|d: int| #[trigger] tx.deps.contains(d) implies s.core.tx.dom().contains(d)
        && s.core.tx[d].epoch <= tx.epoch
        && (exists|i: int| s.core.installed.contains((d, i)))
        && (s.core.tx[d].epoch < tx.epoch ==> abs::below_wm(c.protocol, s.core, s.core.tx[d])) by {
        if s.core.tx[d].epoch < tx.epoch { view_covered(c, s, o, s.core.tx[d]); }
    }
    assert forall|i: int| #[trigger] shard(c.protocol, i) implies if tx.part.dom().contains(i) {
        !s.core.busy.dom().contains(abs::key(tx, i)) && !s.core.closed.contains(abs::key(tx, i))
        && (exists|r: nat| abs::read_max(s.core, tx, i, r) && tx.vc[i] ==
            if r > s.core.clock[(tx.epoch, i)] { r } else { s.core.clock[(tx.epoch, i)] + 1 })
    } else { abs::read_max(s.core, tx, i, tx.vc[i]) } by {
        if tx.part.dom().contains(i) {
            let r = choose|r: nat| abs::read_max(view(c, s, o), tx, i, r) && tx.vc[i] ==
                if r > s.core.clock[(tx.epoch, i)] { r } else { s.core.clock[(tx.epoch, i)] + 1 };
            assert(abs::read_max(s.core, tx, i, r));
        }
    }
}
pub proof fn core_refines(c: Settings, s: State, o: int, a: abs::Action)
    requires inv(c, s), observer(c, o), allowed(a),
        abs::step(c.protocol, view(c, s, o), abs::effect(c.protocol, view(c, s, o), a), a)
    ensures abs::step(c.protocol, s.core, core_result(c, s, o, a).core, a)
{
    reveal(abs::step);
    match a {
        abs::Action::Begin { id, tx } => { begin_refines(c, s, o, id, tx); },
        abs::Action::Ack { id } => { view_covered(c, s, o, s.core.tx[id]); },
        abs::Action::Replay { id, shard } => { view_covered(c, s, o, s.core.tx[id]); },
        _ => {},
    }
}
pub open spec fn abstract_action(s: State, a: Action) -> abs::Action {
    match a {
        Action::Core { observer, action } => action,
        Action::Receive { message: m } => abs::Action::Publish { epoch: m.epoch, shard: m.shard,
            bound: bmax(s.core.wm[(m.epoch, m.shard)], m.value) },
        Action::Finish { epoch, observer } => abs::Action::Finalize { epoch },
        Action::Rollback { id, shard, observer } => abs::Action::Rollback { id, shard },
        _ => abs::Action::Stutter,
    }
}
pub proof fn step_refines(c: Settings, s: State, z: State, a: Action)
    requires inv(c, s), step(c, s, z, a)
    ensures abs::step(c.protocol, s.core, z.core, abstract_action(s, a))
{
    reveal(step); reveal(abs::step);
    match a {
        Action::Core { observer: o, action } => { core_refines(c, s, o, action); },
        Action::Receive { message: m } => {
            order(s.core.wm[(m.epoch, m.shard)], m.value, Bound::Infinity);
            assert forall|k: Stream| stream(c.protocol, k) && k.epoch == m.epoch && k.shard == m.shard implies
                bound_le(bmax(s.core.wm[(m.epoch, m.shard)], m.value), #[trigger] endpoint(s.core, k)) by {
                assert(worker(m.epoch, m.shard, k.worker) == k);
                order(s.core.wm[(m.epoch, m.shard)], m.value, endpoint(s.core, k));
            }
        },
        Action::Finish { epoch: e, observer: o } => {
            assert forall|k: Stream| stream(c.protocol, k) && k.epoch == e implies #[trigger] s.core.closed.contains(k) by {
                assert(s.sealed_views.contains((o, e, k.shard)));
                assert(exact(c, s.core, e, k.shard, s.views[(o, e, k.shard)]));
                assert(worker(e, k.shard, k.worker) == k);
            }
        },
        Action::Rollback { id, shard, observer: o } => { final_view(c, s, o, s.core.tx[id]); },
        _ => {},
    }
}

pub open spec fn frame(c: Settings, s: abs::State, z: abs::State) -> bool {
    &&& forall|k: Stream| stream(c.protocol, k) ==> bound_le(#[trigger] endpoint(s, k), endpoint(z, k))
    &&& s.closed.subset_of(z.closed)
    &&& forall|k: Stream| #[trigger] s.closed.contains(k) ==> endpoint(s, k) == endpoint(z, k)
}
pub proof fn lower_frame(c: Settings, s: abs::State, z: abs::State, e: nat, sh: int, b: Bound)
    requires shard(c.protocol, sh), frame(c, s, z), lower(c, s, e, sh, b)
    ensures lower(c, z, e, sh, b)
{
    assert forall|w: int| 0 <= w < c.protocol.workers implies bound_le(b, #[trigger] endpoint(z, worker(e, sh, w))) by {
        assert(stream(c.protocol, worker(e, sh, w)));
        order(b, endpoint(s, worker(e, sh, w)), endpoint(z, worker(e, sh, w)));
    }
}
pub proof fn exact_frame(c: Settings, s: abs::State, z: abs::State, e: nat, sh: int, b: Bound)
    requires abs::valid(c.protocol), shard(c.protocol, sh), frame(c, s, z), exact(c, s, e, sh, b)
    ensures exact(c, z, e, sh, b)
{
    let a = endpoints(c, s); let d = endpoints(c, z);
    assert forall|w: int| 0 <= w < c.protocol.workers implies #[trigger] a[worker(e, sh, w)] == d[worker(e, sh, w)] by {
        assert(s.closed.contains(worker(e, sh, w)));
    }
    minimum_equal(a, d, e, sh, c.protocol.workers as nat);
}
pub proof fn production_frame(c: Settings, s: State, z: State, a: Action)
    requires inv(c, s), step(c, s, z, a)
    ensures frame(c, s.core, z.core),
        forall|k: Stream| !resets(a, k.epoch, k.shard) && #[trigger] s.sealed_reports.contains(k) ==> z.sealed_reports.contains(k),
        forall|k: Stream| stream(c.protocol, k) && !resets(a, k.epoch, k.shard) ==> bound_le(#[trigger] s.reports[k], z.reports[k]),
        forall|p: (nat, int)| shard(c.protocol, p.1) ==> bound_le(#[trigger] s.core.wm[p], z.core.wm[p])
{
    step_refines(c, s, z, a);
    ai::step_frame(c.protocol, s.core, z.core, abstract_action(s, a));
    reveal(step);
}
pub proof fn init_inv(c: Settings, s: State)
    requires initial(c, s)
    ensures inv(c, s)
{
    ai::init_inv(c.protocol, s.core);
    assert forall|p: (nat, int)| shard(c.protocol, p.1) implies
        lower(c, s.core, p.0, p.1, #[trigger] s.local[p])
        && bound_le(s.local[p], minimum(s.reports, p.0, p.1, c.protocol.workers as nat))
        && (s.sealed_local.contains(p) ==> all_reported(c, s, p.0, p.1) && exact(c, s.core, p.0, p.1, s.local[p])) by {
        minimum_greatest(s.reports, p.0, p.1, c.protocol.workers as nat, Bound::Finite(0));
    }
}
pub proof fn compute_correct(c: Settings, s: State, e: nat, sh: int)
    requires inv(c, s), shard(c.protocol, sh)
    ensures lower(c, s.core, e, sh, minimum(s.reports, e, sh, c.protocol.workers as nat)),
        all_reported(c, s, e, sh) ==> exact(c, s.core, e, sh, minimum(s.reports, e, sh, c.protocol.workers as nat))
{
    let b = minimum(s.reports, e, sh, c.protocol.workers as nat);
    assert forall|w: int| 0 <= w < c.protocol.workers implies bound_le(b, #[trigger] endpoint(s.core, worker(e, sh, w))) by {
        minimum_lower(s.reports, e, sh, c.protocol.workers as nat, w);
        order(b, s.reports[worker(e, sh, w)], endpoint(s.core, worker(e, sh, w)));
    }
    if all_reported(c, s, e, sh) {
        let ends = endpoints(c, s.core);
        assert forall|w: int| 0 <= w < c.protocol.workers implies #[trigger] s.core.closed.contains(worker(e, sh, w)) by {
            assert(s.sealed_reports.contains(worker(e, sh, w)));
            assert(bound_le(s.reports[worker(e, sh, w)], endpoint(s.core, worker(e, sh, w))));
        }
        assert forall|w: int| 0 <= w < c.protocol.workers implies #[trigger] s.reports[worker(e, sh, w)] == ends[worker(e, sh, w)] by {
            assert(s.sealed_reports.contains(worker(e, sh, w)));
        }
        minimum_equal(s.reports, ends, e, sh, c.protocol.workers as nat);
    }
}
pub proof fn step_messages(c: Settings, s: State, z: State, a: Action)
    requires inv(c, s), step(c, s, z, a)
    ensures messages_ok(c, z)
{
    production_frame(c, s, z, a);
    reveal(step);
    assert forall|m: WorkerReport| #[trigger] z.worker_net.contains(m) implies stream(c.protocol, m.stream)
        && bound_le(m.value, endpoint(z.core, m.stream))
        && (m.sealed ==> z.core.closed.contains(m.stream) && m.value == endpoint(z.core, m.stream)) by {
        if s.worker_net.contains(m) {
            order(m.value, endpoint(s.core, m.stream), endpoint(z.core, m.stream));
        }
    }
    assert forall|m: Gossip| #[trigger] z.gossip_net.contains(m) implies observer(c, m.dst) && shard(c.protocol, m.shard)
        && lower(c, z.core, m.epoch, m.shard, m.value)
        && (m.sealed ==> exact(c, z.core, m.epoch, m.shard, m.value)) by {
        if s.gossip_net.contains(m) {
            lower_frame(c, s.core, z.core, m.epoch, m.shard, m.value);
            if m.sealed { exact_frame(c, s.core, z.core, m.epoch, m.shard, m.value); }
        }
    }
}
#[verifier::rlimit(10)]
pub proof fn step_reports(c: Settings, s: State, z: State, a: Action)
    requires inv(c, s), step(c, s, z, a)
    ensures forall|k: Stream| stream(c.protocol, k) ==>
        bound_le(#[trigger] z.reports[k], endpoint(z.core, k)) &&
        (z.sealed_reports.contains(k) ==> z.core.closed.contains(k) && z.reports[k] == endpoint(z.core, k))
{
    production_frame(c, s, z, a);
    reveal(step);
    assert forall|k: Stream| stream(c.protocol, k) implies
        bound_le(#[trigger] z.reports[k], endpoint(z.core, k)) &&
        (z.sealed_reports.contains(k) ==> z.core.closed.contains(k) && z.reports[k] == endpoint(z.core, k)) by {
        order(s.reports[k], endpoint(s.core, k), endpoint(z.core, k));
        match a {
            Action::ReceiveWorker { report: m } => {
                if k == m.stream {
                    order(s.reports[k], m.value, endpoint(s.core, k));
                }
            },
            _ => {},
        }
    }
}
#[verifier::rlimit(10)]
pub proof fn step_local(c: Settings, s: State, z: State, a: Action)
    requires inv(c, s), step(c, s, z, a)
    ensures forall|p: (nat, int)| shard(c.protocol, p.1) ==>
        lower(c, z.core, p.0, p.1, #[trigger] z.local[p])
        && bound_le(z.local[p], minimum(z.reports, p.0, p.1, c.protocol.workers as nat))
        && (z.sealed_local.contains(p) ==> all_reported(c, z, p.0, p.1) && exact(c, z.core, p.0, p.1, z.local[p]))
{
    production_frame(c, s, z, a);
    reveal(step);
    assert forall|p: (nat, int)| shard(c.protocol, p.1) implies
        lower(c, z.core, p.0, p.1, #[trigger] z.local[p])
        && bound_le(z.local[p], minimum(z.reports, p.0, p.1, c.protocol.workers as nat))
        && (z.sealed_local.contains(p) ==> all_reported(c, z, p.0, p.1) && exact(c, z.core, p.0, p.1, z.local[p])) by {
        if resets(a, p.0, p.1) {
            minimum_greatest(z.reports, p.0, p.1, c.protocol.workers as nat, Bound::Finite(0));
        } else {
        lower_frame(c, s.core, z.core, p.0, p.1, s.local[p]);
        if s.sealed_local.contains(p) { exact_frame(c, s.core, z.core, p.0, p.1, s.local[p]); }
        assert forall|w: int| 0 <= w < c.protocol.workers implies
            bound_le(#[trigger] s.reports[worker(p.0, p.1, w)], z.reports[worker(p.0, p.1, w)]) by {
            assert(stream(c.protocol, worker(p.0, p.1, w)));
        }
        minimum_mono(s.reports, z.reports, p.0, p.1, c.protocol.workers as nat);
        order(s.local[p], minimum(s.reports, p.0, p.1, c.protocol.workers as nat), minimum(z.reports, p.0, p.1, c.protocol.workers as nat));
        match a {
            Action::Compute { epoch: e, shard: sh } => {
                if p == (e, sh) { compute_correct(c, s, e, sh); }
            },
            _ => {},
        }
        }
    }
}
#[verifier::rlimit(10)]
pub proof fn step_views(c: Settings, s: State, z: State, a: Action)
    requires inv(c, s), step(c, s, z, a)
    ensures forall|p: (int, nat, int)| observer(c, p.0) && shard(c.protocol, p.2) ==>
        lower(c, z.core, p.1, p.2, #[trigger] z.views[p])
        && bound_le(z.views[p], z.core.wm[(p.1, p.2)])
        && (z.sealed_views.contains(p) ==> exact(c, z.core, p.1, p.2, z.views[p]))
{
    production_frame(c, s, z, a);
    reveal(step);
    assert forall|p: (int, nat, int)| observer(c, p.0) && shard(c.protocol, p.2) implies
        lower(c, z.core, p.1, p.2, #[trigger] z.views[p])
        && bound_le(z.views[p], z.core.wm[(p.1, p.2)])
        && (z.sealed_views.contains(p) ==> exact(c, z.core, p.1, p.2, z.views[p])) by {
        lower_frame(c, s.core, z.core, p.1, p.2, s.views[p]);
        order(s.views[p], s.core.wm[(p.1, p.2)], z.core.wm[(p.1, p.2)]);
        if s.sealed_views.contains(p) { exact_frame(c, s.core, z.core, p.1, p.2, s.views[p]); }
        match a {
            Action::Receive { message: m } => {
                if p == (m.dst, m.epoch, m.shard) {
                    lower_max(c, s.core, p.1, p.2, s.views[p], m.value);
                    lower_frame(c, s.core, z.core, p.1, p.2, bmax(s.views[p], m.value));
                    order(s.views[p], m.value, bmax(s.core.wm[(p.1, p.2)], m.value));
                    order(s.views[p], s.core.wm[(p.1, p.2)], bmax(s.core.wm[(p.1, p.2)], m.value));
                    if m.sealed || s.sealed_views.contains(p) {
                        exact_max(c, s.core, p.1, p.2, s.views[p], m.value);
                        exact_frame(c, s.core, z.core, p.1, p.2, bmax(s.views[p], m.value));
                    }
                }
            },
            _ => {},
        }
    }
}
pub proof fn step_data(c: Settings, s: State, z: State, a: Action)
    requires inv(c, s), step(c, s, z, a)
    ensures data_ok(c, z)
{
    step_reports(c, s, z, a); step_local(c, s, z, a); step_views(c, s, z, a);
    reveal(step);
    assert(z.reports.dom() =~= s.reports.dom());
    assert(z.local.dom() =~= s.local.dom());
    assert(z.views.dom() =~= s.views.dom());
}
pub proof fn step_inv(c: Settings, s: State, z: State, a: Action)
    requires inv(c, s), step(c, s, z, a)
    ensures inv(c, z)
{
    step_refines(c, s, z, a);
    ai::step_inv(c.protocol, s.core, z.core, abstract_action(s, a));
    step_data(c, s, z, a);
    step_messages(c, s, z, a);
}
pub proof fn behavior_inv(c: Settings, h: Seq<State>, j: int)
    requires behavior(c, h), 0 <= j < h.len()
    ensures inv(c, h[j])
    decreases j
{
    if j == 0 { init_inv(c, h[0]); }
    else {
        behavior_inv(c, h, j - 1);
        let i = j - 1;
        assert(next(c, h[i], h[i+1]));
        let a = choose|a: Action| #[trigger] step(c, h[i], h[j], a);
        step_inv(c, h[i], h[j], a);
    }
}
/// End-to-end safety for the protocol with explicit production and gossip.
pub proof fn theorem_production_safety(c: Settings, h: Seq<State>, j: int)
    requires behavior(c, h), 0 <= j < h.len()
    ensures safe::safety(c.protocol, h[j].core)
{
    behavior_inv(c, h, j);
    safe::inv_safety(c.protocol, h[j].core);
}
/// A locally received watermark implies actual durability, without a global
/// safety guard in Sample, ReceiveWorker, Compute, Send, or Receive.
pub proof fn theorem_observer_watermark_sound(c: Settings, h: Seq<State>, j: int, o: int, id: int, sh: int)
    requires behavior(c, h), 0 <= j < h.len(), observer(c, o),
        h[j].core.tx.dom().contains(id), h[j].core.tx[id].part.dom().contains(sh),
        abs::below_wm(c.protocol, view(c, h[j], o), h[j].core.tx[id])
    ensures h[j].core.durable.contains((id, sh)), !abs::doomed(c.protocol, h[j].core, id)
{
    behavior_inv(c, h, j);
    view_covered(c, h[j], o, h[j].core.tx[id]);
    ai::watermark_sound(c.protocol, h[j].core, h[j].core.tx[id]);
    safe::cut_durable(c.protocol, h[j].core, id, sh);
}
/// Once an observer has every finalized component, its produced vector denotes
/// exactly the protocol's finalized cut, including finite and INF components.
pub proof fn theorem_produced_final_cut(c: Settings, h: Seq<State>, j: int, o: int, t: Tx)
    requires behavior(c, h), 0 <= j < h.len(), observer(c, o), all_final(c, h[j], o, t.epoch)
    ensures abs::below_wm(c.protocol, view(c, h[j], o), t) == abs::below_cut(c.protocol, h[j].core, t)
{
    behavior_inv(c, h, j);
    final_view(c, h[j], o, t);
}

pub open spec fn abstract_history(h: Seq<State>) -> Seq<abs::State> {
    Seq::new(h.len(), |i: int| h[i].core)
}
/// Every concrete history refines an abstract history. Abstract Publish is
/// selected by the proof after delivery; it is never enabled as a concrete action.
pub proof fn theorem_production_refines(c: Settings, h: Seq<State>)
    requires behavior(c, h)
    ensures abs::behavior(c.protocol, abstract_history(h))
{
    let ah = abstract_history(h);
    assert forall|i: int| 0 <= i < h.len() - 1 implies #[trigger] abs::next(c.protocol, ah[i], ah[i+1]) by {
        behavior_inv(c, h, i);
        assert(next(c, h[i], h[i+1]));
        let a = choose|a: Action| #[trigger] step(c, h[i], h[i+1], a);
        step_refines(c, h[i], h[i+1], a);
        assert(abs::step(c.protocol, ah[i], ah[i+1], abstract_action(h[i], a)));
    }
}
pub proof fn history_frame(c: Settings, h: Seq<State>, i: int, j: int)
    requires behavior(c, h), 0 <= i <= j < h.len()
    ensures frame(c, h[i].core, h[j].core)
    decreases j-i
{
    if i < j {
        history_frame(c, h, i+1, j);
        behavior_inv(c, h, i);
        assert(next(c, h[i], h[i+1]));
        let a = choose|a: Action| #[trigger] step(c, h[i], h[i+1], a);
        production_frame(c, h[i], h[i+1], a);
        assert forall|k: Stream| stream(c.protocol, k) implies bound_le(#[trigger] endpoint(h[i].core, k), endpoint(h[j].core, k)) by {
            order(endpoint(h[i].core, k), endpoint(h[i+1].core, k), endpoint(h[j].core, k));
        }
    }
}
/// Final components agree across observers and across later recoveries,
/// including an observer forgetting its vector and collecting it again.
pub proof fn theorem_final_agreement(c: Settings, h: Seq<State>, i: int, j: int, a: int, b: int, e: nat, sh: int)
    requires behavior(c, h), 0 <= i <= j < h.len(), observer(c, a), observer(c, b), shard(c.protocol, sh),
        h[i].sealed_views.contains((a, e, sh)), h[j].sealed_views.contains((b, e, sh))
    ensures h[i].views[(a, e, sh)] == h[j].views[(b, e, sh)]
{
    behavior_inv(c, h, i); behavior_inv(c, h, j);
    history_frame(c, h, i, j);
    assert(exact(c, h[i].core, e, sh, h[i].views[(a, e, sh)]));
    assert(exact(c, h[j].core, e, sh, h[j].views[(b, e, sh)]));
    exact_frame(c, h[i].core, h[j].core, e, sh, h[i].views[(a, e, sh)]);
}
pub proof fn receive_isolated(c: Settings, s: State, z: State, m: Gossip, p: (int, nat, int))
    requires step(c, s, z, Action::Receive { message: m }), p != (m.dst, m.epoch, m.shard)
    ensures z.views[p] == s.views[p], z.sealed_views.contains(p) == s.sealed_views.contains(p)
{
    reveal(step);
}
pub proof fn receive_monotone(c: Settings, s: State, z: State, m: Gossip)
    requires step(c, s, z, Action::Receive { message: m })
    ensures bound_le(s.views[(m.dst, m.epoch, m.shard)], z.views[(m.dst, m.epoch, m.shard)]),
        bound_le(m.value, z.views[(m.dst, m.epoch, m.shard)])
{
    reveal(step);
}
} // verus!
