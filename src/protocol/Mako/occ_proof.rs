//! Inductive proof of OCC, not an oracle for successful validation.
use vstd::prelude::*;
use vstd::iset::ISet as Set;
use super::occ::*;
use super::occ_vectors::*;

verus! {
pub open spec fn authentic(c: Config, s: State, k: Key, v: Version) -> bool {
    match v.writer {
        None => v.serial == 0 && v.value == c.base[k] && v.ticket == 0 && v.vc == zero(c),
        Some(w) => s.tx.dom().contains(w) && s.tx[w].phase is Certified
            && s.tx[w].writes.dom().contains(k) && s.installed.contains((w, k))
            && v.serial == s.tx[w].serial && v.value == s.tx[w].writes[k]
            && v.vc == s.tx[w].vc && v.ticket == s.tx[w].tickets[k.shard] && s.tx[w].tickets.dom().contains(k.shard),
    }
}
pub open spec fn shape(c: Config, s: State) -> bool {
    &&& c.shards > 0 && c.base.dom() == Set::new(|k: Key| key(c, k))
    &&& s.tx.dom().finite() && s.data.dom() == c.base.dom()
    &&& s.clocks.dom() == Set::new(|sh: int| 0 <= sh < c.shards)
    &&& forall|id: int, sh: int| #[trigger] s.tx.dom().contains(id) && #[trigger] s.tx[id].tickets.dom().contains(sh) ==>
        0 <= sh < c.shards && 0 < s.tx[id].tickets[sh] <= s.clocks[sh]
    &&& forall|a: int, b: int, sh: int| #[trigger] s.tx.dom().contains(a) && #[trigger] s.tx.dom().contains(b)
        && #[trigger] s.tx[a].tickets.dom().contains(sh) && s.tx[b].tickets.dom().contains(sh)
        && s.tx[a].tickets[sh] == s.tx[b].tickets[sh] ==> a == b
    &&& forall|id: int, k: Key| #[trigger] s.tx.dom().contains(id) && active(s.tx[id])
        && #[trigger] s.tx[id].writes.dom().contains(k) ==> s.tx[id].tickets.dom().contains(k.shard)
    &&& forall|id: int| #[trigger] s.tx.dom().contains(id) ==>
        s.tx[id].writes.dom().finite() && s.tx[id].serial <= s.serial
        && ((s.tx[id].phase is Running || s.tx[id].phase is Locking) ==> s.tx[id].serial == 0 && s.tx[id].checked.is_empty())
        && (s.tx[id].phase is Running ==> s.tx[id].tickets.is_empty())
        && (active(s.tx[id]) ==> s.tx[id].serial > 0)
        && (s.tx[id].phase is Certified ==> all_checked(s.tx[id]))
    &&& forall|id: int, k: Key| #[trigger] s.tx.dom().contains(id) && #[trigger] s.tx[id].writes.dom().contains(k) ==> key(c, k)
    &&& forall|id: int, j: int| #[trigger] s.tx.dom().contains(id) && #[trigger] s.tx[id].checked.contains(j) ==> 0 <= j < s.tx[id].reads.len()
    &&& forall|a: int, b: int| #[trigger] s.tx.dom().contains(a) && #[trigger] s.tx.dom().contains(b)
        && s.tx[a].serial > 0 && s.tx[a].serial == s.tx[b].serial ==> a == b
}
pub open spec fn versions(c: Config, s: State) -> bool {
    &&& forall|k: Key| key(c, k) ==> authentic(c, s, k, #[trigger] s.data[k]) && s.data[k].serial <= s.serial
    &&& forall|id: int, j: int| #[trigger] s.tx.dom().contains(id) && 0 <= j < s.tx[id].reads.len() ==>
        key(c, s.tx[id].reads[j].key) && authentic(c, s, s.tx[id].reads[j].key, #[trigger] s.tx[id].reads[j].version)
        && s.tx[id].reads[j].version.serial <= s.serial
        && (s.tx[id].serial > 0 ==> s.tx[id].reads[j].version.serial < s.tx[id].serial)
    &&& forall|p: (int, Key)| #[trigger] s.installed.contains(p) ==> s.tx.dom().contains(p.0)
        && s.tx[p.0].phase is Certified && s.tx[p.0].writes.dom().contains(p.1)
        && s.tx[p.0].serial <= s.data[p.1].serial
}
pub open spec fn locking(s: State) -> bool {
    &&& forall|k: Key| #[trigger] s.locks.dom().contains(k) ==> s.tx.dom().contains(s.locks[k])
        && (s.tx[s.locks[k]].phase is Locking || active(s.tx[s.locks[k]]))
        && s.tx[s.locks[k]].writes.dom().contains(k) && !s.installed.contains((s.locks[k], k))
        && (s.tx[s.locks[k]].serial > 0 ==> s.data[k].serial < s.tx[s.locks[k]].serial)
    &&& forall|id: int, k: Key| #[trigger] s.tx.dom().contains(id) && active(s.tx[id])
        && #[trigger] s.tx[id].writes.dom().contains(k) ==> s.installed.contains((id, k)) || owns(s, id, k)
}
// Every checked read excludes all earlier live writers other than the observed
// writer and its predecessors. Pending writers are covered as well as installed
// writers, so a later certification cannot invalidate an earlier checked read.
pub open spec fn prior_writers(s: State, id: int, j: int) -> bool {
    forall|w: int| #[trigger] s.tx.dom().contains(w) && active(s.tx[w]) && w != id
        && s.tx[w].writes.dom().contains(s.tx[id].reads[j].key) && s.tx[w].serial < s.tx[id].serial
        ==> s.tx[w].serial <= s.tx[id].reads[j].version.serial
}
pub open spec fn validated(s: State) -> bool {
    forall|id: int, j: int| #[trigger] s.tx.dom().contains(id) && active(s.tx[id])
        && #[trigger] s.tx[id].checked.contains(j) ==> prior_writers(s, id, j)
}
pub open spec fn inv(c: Config, s: State) -> bool { shape(c, s) && versions(c, s) && locking(s) && validated(s) && vectors(c, s) }

pub proof fn same_ticket_same_version(c: Config, s: State, k: Key, a: Version, b: Version)
    requires shape(c, s), authentic(c, s, k, a), authentic(c, s, k, b), a.ticket == b.ticket
    ensures a == b
{ }
pub proof fn validation_prior_writer(c: Config, s: State, id: int, j: int, w: int)
    requires versions(c, s), locking(s), validation(s, id, j),
        s.data[s.tx[id].reads[j].key] == s.tx[id].reads[j].version,
        s.tx.dom().contains(w), active(s.tx[w]), w != id,
        s.tx[w].writes.dom().contains(s.tx[id].reads[j].key), s.tx[w].serial < s.tx[id].serial
    ensures s.tx[w].serial <= s.tx[id].reads[j].version.serial
{
    let k = s.tx[id].reads[j].key;
    if !s.installed.contains((w, k)) { assert(owns(s, w, k)); }
}
pub proof fn validation_correct(c: Config, s: State, id: int, j: int)
    requires inv(c, s), validation(s, id, j)
    ensures prior_writers(s, id, j), s.data[s.tx[id].reads[j].key] == s.tx[id].reads[j].version
{
    let r = s.tx[id].reads[j];
    ticket_component(c, s, r.key, r.version);
    ticket_component(c, s, r.key, s.data[r.key]);
    same_ticket_same_version(c, s, r.key, s.data[r.key], r.version);
    assert forall|w: int| #[trigger] s.tx.dom().contains(w) && active(s.tx[w]) && w != id
        && s.tx[w].writes.dom().contains(r.key) && s.tx[w].serial < s.tx[id].serial
        implies s.tx[w].serial <= r.version.serial by {
        validation_prior_writer(c, s, id, j, w);
    }
}
pub proof fn init_inv(c: Config, s: State)
    requires initial(c, s) ensures inv(c, s)
{ broadcast use vstd::iset::lemma_iset_empty_finite; }

// Previously certified transactions, their reads, and their writes never change.
pub proof fn frame(c: Config, s: State, z: State, a: Action)
    requires shape(c, s), versions(c, s), locking(s), step(c, s, z, a)
    ensures s.serial <= z.serial,
        s.installed.subset_of(z.installed),
        forall|id: int| #[trigger] s.tx.dom().contains(id) ==> z.tx.dom().contains(id)
            && (s.tx[id].phase is Certified ==> z.tx[id] == s.tx[id])
            && (s.tx[id].serial > 0 ==> z.tx[id].serial == s.tx[id].serial),
        forall|k: Key| key(c, k) ==> #[trigger] s.data[k].serial <= z.data[k].serial
{
    reveal(step);
    if let Action::Install { id, shard: sh } = a {
        assert forall|k: Key| key(c, k) implies #[trigger] s.data[k].serial <= z.data[k].serial by {
            if k.shard == sh && s.tx[id].writes.dom().contains(k) { assert(owns(s, id, k)); }
        }
    }
}
pub proof fn step_shape(c: Config, s: State, z: State, a: Action)
    requires shape(c, s), versions(c, s), locking(s), step(c, s, z, a) ensures shape(c, z)
{
    reveal(step);
    broadcast use vstd::iset::lemma_iset_empty_finite;
    match a {
        Action::Open { id } => { vstd::iset::lemma_iset_insert_finite(s.tx.dom(), id); },
        Action::Write { id, key: k, value } => { vstd::iset::lemma_iset_insert_finite(s.tx[id].writes.dom(), k); },
        _ => {},
    }
    assert(z.clocks.dom() =~= s.clocks.dom());
    assert forall|id: int, sh: int| #[trigger] z.tx.dom().contains(id) && #[trigger] z.tx[id].tickets.dom().contains(sh) implies
        0 <= sh < c.shards && 0 < z.tx[id].tickets[sh] <= z.clocks[sh] by { }
    assert forall|x: int, y: int, sh: int| #[trigger] z.tx.dom().contains(x) && #[trigger] z.tx.dom().contains(y)
        && #[trigger] z.tx[x].tickets.dom().contains(sh) && z.tx[y].tickets.dom().contains(sh)
        && z.tx[x].tickets[sh] == z.tx[y].tickets[sh] implies x == y by {
        match a {
            Action::GetClock { id, shard: sh2 } => {
                if x == id && sh == sh2 && y != id { assert(s.tx[y].tickets[sh] <= s.clocks[sh]); }
                if y == id && sh == sh2 && x != id { assert(s.tx[x].tickets[sh] <= s.clocks[sh]); }
            },
            _ => {},
        }
    }
}
pub proof fn authentic_preserved(c: Config, s: State, z: State, a: Action, k: Key, v: Version)
    requires shape(c, s), versions(c, s), locking(s), step(c, s, z, a), authentic(c, s, k, v)
    ensures authentic(c, z, k, v)
{ frame(c, s, z, a); }
pub proof fn step_data_version(c: Config, s: State, z: State, a: Action, k: Key)
    requires shape(c, s), versions(c, s), locking(s), step(c, s, z, a), key(c, k)
    ensures authentic(c, z, k, z.data[k]), z.data[k].serial <= z.serial
{
    reveal(step);
    frame(c, s, z, a);
    authentic_preserved(c, s, z, a, k, s.data[k]);
}
pub proof fn step_read_version(c: Config, s: State, z: State, a: Action, id: int, j: int)
    requires shape(c, s), versions(c, s), locking(s), step(c, s, z, a), z.tx.dom().contains(id), 0 <= j < z.tx[id].reads.len()
    ensures key(c, z.tx[id].reads[j].key), authentic(c, z, z.tx[id].reads[j].key, z.tx[id].reads[j].version),
        z.tx[id].reads[j].version.serial <= z.serial,
        z.tx[id].serial > 0 ==> z.tx[id].reads[j].version.serial < z.tx[id].serial
{
    reveal(step);
    frame(c, s, z, a);
    match a {
        Action::Read { id: t, key: k } => {
            if id == t && j == s.tx[t].reads.len() { authentic_preserved(c, s, z, a, k, s.data[k]); }
            else { authentic_preserved(c, s, z, a, s.tx[id].reads[j].key, s.tx[id].reads[j].version); }
        },
        _ => { authentic_preserved(c, s, z, a, s.tx[id].reads[j].key, s.tx[id].reads[j].version); },
    }
}
pub proof fn step_versions(c: Config, s: State, z: State, a: Action)
    requires shape(c, s), versions(c, s), locking(s), step(c, s, z, a) ensures versions(c, z)
{
    reveal(step);
    frame(c, s, z, a);
    assert forall|k: Key| key(c, k) implies authentic(c, z, k, #[trigger] z.data[k]) && z.data[k].serial <= z.serial by {
        step_data_version(c, s, z, a, k);
    }
    assert forall|id: int, j: int| #[trigger] z.tx.dom().contains(id) && 0 <= j < z.tx[id].reads.len() implies
        key(c, z.tx[id].reads[j].key) && authentic(c, z, z.tx[id].reads[j].key, #[trigger] z.tx[id].reads[j].version)
        && z.tx[id].reads[j].version.serial <= z.serial
        && (z.tx[id].serial > 0 ==> z.tx[id].reads[j].version.serial < z.tx[id].serial) by {
        step_read_version(c, s, z, a, id, j);
    }
    assert forall|p: (int, Key)| #[trigger] z.installed.contains(p) implies z.tx.dom().contains(p.0)
        && z.tx[p.0].phase is Certified && z.tx[p.0].writes.dom().contains(p.1)
        && z.tx[p.0].serial <= z.data[p.1].serial by { }
}
pub proof fn step_locking(c: Config, s: State, z: State, a: Action)
    requires shape(c, s), versions(c, s), locking(s), step(c, s, z, a) ensures locking(z)
{
    reveal(step);
    assert forall|k: Key| #[trigger] z.locks.dom().contains(k) implies z.tx.dom().contains(z.locks[k])
        && (z.tx[z.locks[k]].phase is Locking || active(z.tx[z.locks[k]]))
        && z.tx[z.locks[k]].writes.dom().contains(k) && !z.installed.contains((z.locks[k], k))
        && (z.tx[z.locks[k]].serial > 0 ==> z.data[k].serial < z.tx[z.locks[k]].serial) by {
        match a {
            Action::Check { id } => { if z.locks[k] == id { assert(key(c, k)); } },
            _ => {},
        }
    }
    assert forall|id: int, k: Key| #[trigger] z.tx.dom().contains(id) && active(z.tx[id])
        && #[trigger] z.tx[id].writes.dom().contains(k) implies z.installed.contains((id, k)) || owns(z, id, k) by { }
}
pub proof fn step_validated(c: Config, s: State, z: State, a: Action)
    requires inv(c, s), step(c, s, z, a) ensures validated(z)
{
    reveal(step);
    if let Action::Validate { id, index } = a { validation_correct(c, s, id, index); }
    assert forall|id: int, j: int| #[trigger] z.tx.dom().contains(id) && active(z.tx[id])
        && #[trigger] z.tx[id].checked.contains(j) implies prior_writers(z, id, j) by {
        assert forall|w: int| #[trigger] z.tx.dom().contains(w) && active(z.tx[w]) && w != id
            && z.tx[w].writes.dom().contains(z.tx[id].reads[j].key) && z.tx[w].serial < z.tx[id].serial
            implies z.tx[w].serial <= z.tx[id].reads[j].version.serial by {
            match a {
                Action::Check { id: t } => { if w == t { assert(s.tx[id].serial <= s.serial); } },
                _ => {},
            }
        }
    }
}
pub proof fn step_inv(c: Config, s: State, z: State, a: Action)
    requires inv(c, s), step(c, s, z, a) ensures inv(c, z)
{ step_shape(c, s, z, a); step_versions(c, s, z, a); step_locking(c, s, z, a); step_validated(c, s, z, a); step_vectors(c, s, z, a); }
pub proof fn behavior_inv(c: Config, h: Seq<State>, j: int)
    requires behavior(c, h), 0 <= j < h.len() ensures inv(c, h[j]) decreases j
{
    if j == 0 { init_inv(c, h[0]); }
    else {
        behavior_inv(c, h, j-1);
        let i = j-1;
        assert(next(c, h[i], h[i+1]));
        let a = choose|a: Action| #[trigger] step(c, h[j-1], h[j], a);
        step_inv(c, h[j-1], h[j], a);
    }
}
pub open spec fn certified(s: State) -> Set<int> {
    s.tx.dom().filter(|id: int| s.tx[id].phase is Certified)
}
pub open spec fn closed(s: State, keep: Set<int>) -> bool {
    keep.subset_of(certified(s)) && forall|id: int, d: int| #[trigger] keep.contains(id) && #[trigger] deps(s, id).contains(d) ==> keep.contains(d)
}
// Finite transactions ordered by distinct positive serial numbers. Each read
// observes the last preceding retained writer, or the initial database when
// no such writer exists. Writes are the immutable buffered values.
pub open spec fn serializable(c: Config, s: State, keep: Set<int>) -> bool {
    &&& keep.finite() && keep.subset_of(certified(s))
    &&& forall|id: int| #[trigger] keep.contains(id) ==> s.tx[id].serial > 0
    &&& forall|a: int, b: int| #[trigger] keep.contains(a) && #[trigger] keep.contains(b) && a != b ==> s.tx[a].serial != s.tx[b].serial
    &&& forall|id: int, j: int| #[trigger] keep.contains(id) && 0 <= j < s.tx[id].reads.len() ==>
        #[trigger] s.tx[id].reads[j].version.serial < s.tx[id].serial
        && (match s.tx[id].reads[j].version.writer {
            None => s.tx[id].reads[j].version.serial == 0 && s.tx[id].reads[j].version.value == c.base[s.tx[id].reads[j].key],
            Some(w) => keep.contains(w) && s.tx[w].writes.dom().contains(s.tx[id].reads[j].key)
                && s.tx[id].reads[j].version.serial == s.tx[w].serial
                && s.tx[id].reads[j].version.value == s.tx[w].writes[s.tx[id].reads[j].key],
        })
        && (forall|w: int| #[trigger] keep.contains(w) && s.tx[w].writes.dom().contains(s.tx[id].reads[j].key)
            && s.tx[w].serial < s.tx[id].serial ==> s.tx[w].serial <= s.tx[id].reads[j].version.serial)
}
pub proof fn inv_serializable(c: Config, s: State, keep: Set<int>)
    requires inv(c, s), closed(s, keep) ensures serializable(c, s, keep)
{
    assert(keep.subset_of(s.tx.dom()));
    vstd::iset_lib::lemma_len_subset(keep, s.tx.dom());
    assert forall|id: int, j: int| #[trigger] keep.contains(id) && 0 <= j < s.tx[id].reads.len() implies
        #[trigger] s.tx[id].reads[j].version.serial < s.tx[id].serial
        && (match s.tx[id].reads[j].version.writer {
            None => s.tx[id].reads[j].version.serial == 0 && s.tx[id].reads[j].version.value == c.base[s.tx[id].reads[j].key],
            Some(w) => keep.contains(w) && s.tx[w].writes.dom().contains(s.tx[id].reads[j].key)
                && s.tx[id].reads[j].version.serial == s.tx[w].serial
                && s.tx[id].reads[j].version.value == s.tx[w].writes[s.tx[id].reads[j].key],
        })
        && (forall|w: int| #[trigger] keep.contains(w) && s.tx[w].writes.dom().contains(s.tx[id].reads[j].key)
            && s.tx[w].serial < s.tx[id].serial ==> s.tx[w].serial <= s.tx[id].reads[j].version.serial) by {
        assert(s.tx[id].checked.contains(j));
        if let Some(w) = s.tx[id].reads[j].version.writer { assert(deps(s, id).contains(w)); }
    }
}
pub proof fn certified_closed(c: Config, s: State)
    requires inv(c, s) ensures closed(s, certified(s))
{
    assert forall|id: int, d: int| #[trigger] certified(s).contains(id) && #[trigger] deps(s, id).contains(d) implies certified(s).contains(d) by {
        let j = choose|j: int| 0 <= j < s.tx[id].reads.len() && #[trigger] s.tx[id].reads[j].version.writer == Some(d);
        assert(authentic(c, s, s.tx[id].reads[j].key, s.tx[id].reads[j].version));
    }
}
pub proof fn theorem_occ_serializable(c: Config, h: Seq<State>, j: int)
    requires behavior(c, h), 0 <= j < h.len() ensures serializable(c, h[j], certified(h[j]))
{ behavior_inv(c, h, j); certified_closed(c, h[j]); inv_serializable(c, h[j], certified(h[j])); }
pub proof fn theorem_rollback_preserves_serializability(c: Config, h: Seq<State>, j: int, keep: Set<int>)
    requires behavior(c, h), 0 <= j < h.len(), closed(h[j], keep)
    ensures serializable(c, h[j], keep)
{ behavior_inv(c, h, j); inv_serializable(c, h[j], keep); }
} // verus!
