use vstd::prelude::*;
use vstd::imap::IMap as Map;
use vstd::iset::ISet as Set;
use super::model::*;

verus! {

pub open spec fn shape(c: Config, s: State) -> bool {
    &&& valid(c)
    &&& s.tx.dom().finite()
    &&& s.clock.dom() == Set::new(|p: (nat, int)| shard(c, p.1))
    &&& s.tail.dom() == Set::new(|k: Stream| stream(c, k))
    &&& s.progress.dom() == s.tail.dom()
    &&& s.wm.dom() == s.clock.dom()
    &&& forall|id: int| #[trigger] s.tx.dom().contains(id) ==>
        tx_valid(c, s.tx[id]) && s.tx[id].epoch <= s.epoch
    &&& forall|k: Stream| #[trigger] s.closed.contains(k) ==> stream(c, k) && k.epoch < s.epoch
    &&& s.infinity.subset_of(s.closed)
    &&& forall|e: nat| #[trigger] s.finalized.contains(e) ==> e < s.epoch &&
        forall|k: Stream| stream(c, k) && k.epoch == e ==> #[trigger] s.closed.contains(k)
}
pub open spec fn streams_ok(c: Config, s: State) -> bool {
    &&& forall|k: Stream| #![trigger s.progress[k]] #![trigger s.tail[k]] stream(c, k) ==> s.progress[k] <= s.tail[k] && s.tail[k] <= s.clock[(k.epoch, k.shard)]
    &&& forall|k: Stream| #[trigger] s.busy.dom().contains(k) ==> stream(c, k)
        && s.tx.dom().contains(s.busy[k]) && s.tx[s.busy[k]].part.dom().contains(k.shard)
        && key(s.tx[s.busy[k]], k.shard) == k
        && !s.installed.contains((s.busy[k], k.shard))
    &&& forall|id: int, i: int| #[trigger] s.tx.dom().contains(id) && #[trigger] s.tx[id].part.dom().contains(i) ==>
        s.tx[id].vc[i] <= s.clock[(s.tx[id].epoch, i)] &&
        if s.installed.contains((id, i)) { s.tx[id].vc[i] <= s.tail[key(s.tx[id], i)] }
        else { s.busy.dom().contains(key(s.tx[id], i)) && s.busy[key(s.tx[id], i)] == id
            && s.tail[key(s.tx[id], i)] < s.tx[id].vc[i] }
    &&& forall|f: (int, int)| #[trigger] s.installed.contains(f) ==>
        s.tx.dom().contains(f.0) && s.tx[f.0].part.dom().contains(f.1)
    &&& s.durable.subset_of(s.installed)
    &&& forall|id: int, i: int| #[trigger] s.tx.dom().contains(id) && #[trigger] s.tx[id].part.dom().contains(i)
        && covered(s.tx[id].vc[i], endpoint(s, key(s.tx[id], i))) ==> s.durable.contains((id, i))
    &&& forall|k: Stream| #[trigger] s.infinity.contains(k) ==> !s.busy.dom().contains(k)
    &&& forall|k: Stream| stream(c, k) ==> bound_le(#[trigger] s.wm[(k.epoch, k.shard)], endpoint(s, k))
}
pub open spec fn deps_ok(c: Config, s: State) -> bool {
    forall|id: int, d: int| #[trigger] s.tx.dom().contains(id) && #[trigger] s.tx[id].deps.contains(d) ==>
        s.tx.dom().contains(d) && s.tx[d].epoch <= s.tx[id].epoch &&
        if s.tx[d].epoch == s.tx[id].epoch { vc_le(c, s.tx[d], s.tx[id]) }
        else { below_cut(c, s, s.tx[d]) }
}
pub open spec fn decisions_ok(c: Config, s: State) -> bool {
    &&& forall|id: int| #[trigger] s.acked.contains(id) ==> s.tx.dom().contains(id) && below_cut(c, s, s.tx[id])
    &&& forall|f: (int, int)| #[trigger] s.replayed.contains(f) ==> s.durable.contains(f) && below_cut(c, s, s.tx[f.0])
    &&& forall|f: (int, int)| #[trigger] s.rolled.contains(f) ==> s.installed.contains(f) && doomed(c, s, f.0)
}
pub open spec fn inv(c: Config, s: State) -> bool {
    shape(c, s) && streams_ok(c, s) && deps_ok(c, s) && decisions_ok(c, s)
}
pub proof fn stream_bounds(c: Config, s: State, k: Stream)
    requires streams_ok(c, s), stream(c, k)
    ensures s.progress[k] <= s.tail[k], s.tail[k] <= s.clock[(k.epoch, k.shard)]
{ }
pub proof fn bound_trans(a: Bound, b: Bound, d: Bound)
    requires bound_le(a, b), bound_le(b, d)
    ensures bound_le(a, d)
{ }
pub proof fn covered_trans(v: nat, a: Bound, b: Bound)
    requires covered(v, a), bound_le(a, b)
    ensures covered(v, b)
{ }
pub proof fn watermark_sound(c: Config, s: State, t: Tx)
    requires streams_ok(c, s), below_wm(c, s, t)
    ensures below_cut(c, s, t)
{
    assert forall|k: Stream| stream(c, k) && k.epoch == t.epoch implies
        covered(t.vc[k.shard], #[trigger] endpoint(s, k)) by {
        covered_trans(t.vc[k.shard], s.wm[(t.epoch, k.shard)], endpoint(s, k));
    }
}
pub proof fn init_inv(c: Config, s: State)
    requires initial(c, s)
    ensures inv(c, s)
{ broadcast use vstd::iset::lemma_iset_empty_finite; }
// Every step preserves old transaction metadata and durable evidence. Closed
// stream endpoints never change, even if recovery is interrupted repeatedly.
pub proof fn step_frame(c: Config, s: State, z: State, a: Action)
    requires inv(c, s), step(c, s, z, a)
    ensures
        s.epoch <= z.epoch,
        forall|id: int| #[trigger] s.tx.dom().contains(id) ==> z.tx.dom().contains(id) && z.tx[id] == s.tx[id],
        s.installed.subset_of(z.installed), s.durable.subset_of(z.durable),
        s.closed.subset_of(z.closed), s.finalized.subset_of(z.finalized),
        forall|k: Stream| stream(c, k) ==> bound_le(#[trigger] endpoint(s, k), endpoint(z, k)),
        forall|k: Stream| #[trigger] s.closed.contains(k) ==> endpoint(s, k) == endpoint(z, k)
{
    reveal(step);
}
pub proof fn cut_grows(c: Config, s: State, z: State, t: Tx)
    requires below_cut(c, s, t),
        forall|k: Stream| stream(c, k) ==> bound_le(#[trigger] endpoint(s, k), endpoint(z, k))
    ensures below_cut(c, z, t)
{
    assert forall|k: Stream| stream(c, k) && k.epoch == t.epoch implies
        covered(t.vc[k.shard], #[trigger] endpoint(z, k)) by {
        covered_trans(t.vc[k.shard], endpoint(s, k), endpoint(z, k));
    }
}
pub proof fn final_cut_fixed(c: Config, s: State, z: State, t: Tx)
    requires shape(c, s), s.finalized.contains(t.epoch),
        forall|k: Stream| #[trigger] s.closed.contains(k) ==> endpoint(s, k) == endpoint(z, k)
    ensures below_cut(c, s, t) == below_cut(c, z, t)
{
    if below_cut(c, s, t) {
        assert forall|k: Stream| stream(c, k) && k.epoch == t.epoch implies
            covered(t.vc[k.shard], #[trigger] endpoint(z, k)) by {
            assert(s.closed.contains(k));
            assert(covered(t.vc[k.shard], endpoint(s, k)));
        }
    } else if below_cut(c, z, t) {
        assert forall|k: Stream| stream(c, k) && k.epoch == t.epoch implies
            covered(t.vc[k.shard], #[trigger] endpoint(s, k)) by {
            assert(s.closed.contains(k));
            assert(covered(t.vc[k.shard], endpoint(z, k)));
        }
    }
}
pub proof fn step_shape(c: Config, s: State, z: State, a: Action)
    requires inv(c, s), step(c, s, z, a)
    ensures shape(c, z)
{
    reveal(step);
    match a {
        Action::Begin { id, tx } => {
            vstd::iset::lemma_iset_insert_finite(s.tx.dom(), id);
            assert(z.clock.dom() =~= s.clock.dom());
            assert forall|j: int| #[trigger] z.tx.dom().contains(j) implies
                tx_valid(c, z.tx[j]) && z.tx[j].epoch <= z.epoch by {
                if j != id { assert(s.tx.dom().contains(j)); }
            }
            assert(z.tail.dom() == s.tail.dom());
            assert(z.wm.dom() == z.clock.dom());
            assert(z.clock.dom() == Set::new(|p: (nat, int)| shard(c, p.1)));
            assert(z.tail.dom() == Set::new(|k: Stream| stream(c, k)));
            assert(z.progress.dom() == z.tail.dom());
            assert(z.infinity.subset_of(z.closed));
            assert forall|k: Stream| #[trigger] z.closed.contains(k) implies stream(c, k) && k.epoch < z.epoch by { }
            assert forall|e: nat| #[trigger] z.finalized.contains(e) implies e < z.epoch &&
                forall|k: Stream| stream(c, k) && k.epoch == e ==> #[trigger] z.closed.contains(k) by { }
            assert(shape(c, z));
        },
        Action::Install { id, shard: i } => {
            assert(stream(c, key(s.tx[id], i)));
            assert(z.tail.dom() =~= s.tail.dom());
        },
        Action::Replicate { stream: k, progress: p } => { assert(z.progress.dom() =~= s.progress.dom()); },
        Action::Publish { epoch: e, shard: i, bound: b } => { assert(z.wm.dom() =~= s.wm.dom()); },
        _ => {},
    }
}
pub proof fn close_no_pending(c: Config, s: State, z: State, k: Stream, good: bool)
    requires inv(c, s), close(c, s, z, k, good)
    ensures forall|j: Stream| #[trigger] z.infinity.contains(j) ==> !z.busy.dom().contains(j)
{ }
#[verifier::rlimit(10)]
pub proof fn step_streams(c: Config, s: State, z: State, a: Action)
    requires inv(c, s), step(c, s, z, a)
    ensures streams_ok(c, z)
{
    // Stream ordering needs the allocated clock, not the read-dependency
    // quantifier inside read_max; unfolding it floods the rolling solver.
    hide(read_max);
    reveal(step);
    if let Action::Close { stream: k, good } = a { close_no_pending(c, s, z, k, good); }
    assert forall|k: Stream| stream(c, k) implies #[trigger] z.progress[k] <= z.tail[k] <= z.clock[(k.epoch, k.shard)] by {
        stream_bounds(c, s, k);
        match a {
            Action::Begin { id, tx } => {
                if k.epoch == tx.epoch && tx.part.dom().contains(k.shard) {
                    let r = choose|r: nat| read_max(s, tx, k.shard, r) && tx.vc[k.shard] ==
                        if r > s.clock[(tx.epoch, k.shard)] { r } else { s.clock[(tx.epoch, k.shard)] + 1 };
                }
            },
            Action::Install { id, shard: i } => {
                assert(s.tx[id].part.dom().contains(i));
                assert(stream(c, key(s.tx[id], i)));
                assert(s.tx[id].vc[i] <= s.clock[(s.tx[id].epoch, i)]);
                assert(s.tail[key(s.tx[id], i)] < s.tx[id].vc[i]);
                assert(s.progress[key(s.tx[id], i)] <= s.tail[key(s.tx[id], i)]);
            },
            _ => {},
        }
    }
    assert forall|k: Stream| #[trigger] z.busy.dom().contains(k) implies stream(c, k)
        && z.tx.dom().contains(z.busy[k]) && z.tx[z.busy[k]].part.dom().contains(k.shard)
        && key(z.tx[z.busy[k]], k.shard) == k
        && !z.installed.contains((z.busy[k], k.shard)) by { }
    assert forall|id: int, i: int| #[trigger] z.tx.dom().contains(id) && #[trigger] z.tx[id].part.dom().contains(i) implies
        z.tx[id].vc[i] <= z.clock[(z.tx[id].epoch, i)] &&
        if z.installed.contains((id, i)) { z.tx[id].vc[i] <= z.tail[key(z.tx[id], i)] }
        else { z.busy.dom().contains(key(z.tx[id], i)) && z.busy[key(z.tx[id], i)] == id
            && z.tail[key(z.tx[id], i)] < z.tx[id].vc[i] } by {
        match a {
            Action::Begin { id: new_id, tx } => {
                if tx.part.dom().contains(i) {
                    let r = choose|r: nat| read_max(s, tx, i, r) && tx.vc[i] ==
                        if r > s.clock[(tx.epoch, i)] { r } else { s.clock[(tx.epoch, i)] + 1 };
                    assert(tx.vc[i] > s.clock[(tx.epoch, i)]);
                }
                if id == new_id { assert(stream(c, key(tx, i))); }
            },
            Action::Install { id: installed_id, shard: installed_i } => {
                assert(!s.installed.contains((installed_id, installed_i)));
            },
            _ => {},
        }
    }
    assert forall|id: int, i: int| #[trigger] z.tx.dom().contains(id) && #[trigger] z.tx[id].part.dom().contains(i)
        && covered(z.tx[id].vc[i], endpoint(z, key(z.tx[id], i))) implies z.durable.contains((id, i)) by {
        let k = key(z.tx[id], i);
        match a {
            Action::Begin { id: new_id, tx } => {
                if id == new_id {
                    let r = choose|r: nat| read_max(s, tx, i, r) && tx.vc[i] ==
                        if r > s.clock[(tx.epoch, i)] { r } else { s.clock[(tx.epoch, i)] + 1 };
                    assert(stream(c, k));
                    assert(!s.infinity.contains(k));
                }
            },
            Action::Replicate { stream: changed, progress: p } => {
                if k == changed {
                    assert(s.installed.contains((id, i)));
                    assert(z.durable.contains((id, i)));
                }
            },
            Action::Close { stream: changed, good } => {
                if k == changed && good {
                    assert(s.installed.contains((id, i)));
                    assert(s.tx[id].vc[i] <= s.progress[k]);
                    assert(covered(s.tx[id].vc[i], endpoint(s, k)));
                }
            },
            _ => {},
        }
    }
    assert forall|k: Stream| stream(c, k) implies bound_le(#[trigger] z.wm[(k.epoch, k.shard)], endpoint(z, k)) by {
        step_frame(c, s, z, a);
        match a {
            Action::Publish { epoch: e, shard: i, bound: b } => {},
            _ => { bound_trans(s.wm[(k.epoch, k.shard)], endpoint(s, k), endpoint(z, k)); },
        }
    }
}
pub proof fn begin_old_dependency(c: Config, s: State, z: State, id: int, t: Tx, d: int)
    requires begin(c, s, z, id, t), t.deps.contains(d), s.tx[d].epoch < t.epoch
    ensures below_wm(c, s, s.tx[d])
{ }
pub proof fn step_deps(c: Config, s: State, z: State, a: Action)
    requires inv(c, s), step(c, s, z, a)
    ensures deps_ok(c, z)
{
    step_frame(c, s, z, a);
    reveal(step);
    assert forall|id: int, d: int| #[trigger] z.tx.dom().contains(id) && #[trigger] z.tx[id].deps.contains(d) implies
        z.tx.dom().contains(d) && z.tx[d].epoch <= z.tx[id].epoch &&
        if z.tx[d].epoch == z.tx[id].epoch { vc_le(c, z.tx[d], z.tx[id]) }
        else { below_cut(c, z, z.tx[d]) } by {
        if s.tx.dom().contains(id) {
            if s.tx[d].epoch < s.tx[id].epoch { cut_grows(c, s, z, s.tx[d]); }
        } else {
            match a {
                Action::Begin { id: new_id, tx } => {
                    if s.tx[d].epoch < tx.epoch {
                        begin_old_dependency(c, s, z, new_id, tx, d);
                        watermark_sound(c, s, s.tx[d]); cut_grows(c, s, z, s.tx[d]);
                    } else {
                        assert forall|i: int| shard(c, i) implies #[trigger] z.tx[d].vc[i] <= #[trigger] z.tx[id].vc[i] by {
                            if tx.part.dom().contains(i) {
                                let r = choose|r: nat| read_max(s, tx, i, r) && tx.vc[i] ==
                                    if r > s.clock[(tx.epoch, i)] { r } else { s.clock[(tx.epoch, i)] + 1 };
                            }
                        }
                    }
                },
                _ => {},
            }
        }
    }
}
pub proof fn step_decisions(c: Config, s: State, z: State, a: Action)
    requires inv(c, s), step(c, s, z, a)
    ensures decisions_ok(c, z)
{
    step_frame(c, s, z, a);
    reveal(step);
    assert forall|id: int| #[trigger] z.acked.contains(id) implies z.tx.dom().contains(id) && below_cut(c, z, z.tx[id]) by {
        if s.acked.contains(id) { cut_grows(c, s, z, s.tx[id]); }
        else { watermark_sound(c, s, s.tx[id]); cut_grows(c, s, z, s.tx[id]); }
    }
    assert forall|f: (int, int)| #[trigger] z.replayed.contains(f) implies z.durable.contains(f) && below_cut(c, z, z.tx[f.0]) by {
        if s.replayed.contains(f) { cut_grows(c, s, z, s.tx[f.0]); }
        else { watermark_sound(c, s, s.tx[f.0]); cut_grows(c, s, z, s.tx[f.0]); }
    }
    assert forall|f: (int, int)| #[trigger] z.rolled.contains(f) implies z.installed.contains(f) && doomed(c, z, f.0) by {
        if s.rolled.contains(f) { final_cut_fixed(c, s, z, s.tx[f.0]); }
    }
}
pub proof fn step_inv(c: Config, s: State, z: State, a: Action)
    requires inv(c, s), step(c, s, z, a)
    ensures inv(c, z)
{
    step_shape(c, s, z, a);
    step_streams(c, s, z, a);
    step_deps(c, s, z, a);
    step_decisions(c, s, z, a);
}
pub proof fn behavior_inv(c: Config, h: Seq<State>, i: int)
    requires behavior(c, h), 0 <= i < h.len()
    ensures inv(c, h[i])
    decreases i
{
    if i == 0 { init_inv(c, h[0]); }
    else {
        behavior_inv(c, h, i - 1);
        let j = i - 1;
        assert(next(c, h[j], h[j + 1]));
        assert(h[j + 1] == h[i]);
        let a = choose|a: Action| #[trigger] step(c, h[i - 1], h[i], a);
        step_inv(c, h[i - 1], h[i], a);
    }
}
} // verus!
