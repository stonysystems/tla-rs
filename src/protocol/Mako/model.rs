//! Mako, OSDI 2025, Sections 4-5 and Appendix A.
//! Transaction abstraction used by the producer proof. Key-level OCC has its
//! own checked model in occ.rs; occ_composition.rs states the linking obligation.
//! Consensus remains an abstract durable-prefix/sealing interface.
use vstd::prelude::*;
use vstd::imap::IMap as Map;
use vstd::iset::ISet as Set;

verus! {

pub struct Config { pub shards: int, pub workers: int }
pub struct Stream { pub epoch: nat, pub shard: int, pub worker: int }
pub struct Tx {
    pub epoch: nat,
    pub vc: Map<int, nat>,
    // Participant shard -> worker reserved for this transaction.
    pub part: Map<int, int>,
    pub deps: Set<int>,
}
pub enum Bound { Finite(nat), Infinity }
pub struct State {
    pub epoch: nat,
    pub tx: Map<int, Tx>,
    pub clock: Map<(nat, int), nat>,
    pub tail: Map<Stream, nat>,
    pub progress: Map<Stream, nat>,
    pub busy: Map<Stream, int>,
    pub installed: Set<(int, int)>,
    pub durable: Set<(int, int)>,
    pub closed: Set<Stream>,
    pub infinity: Set<Stream>,
    // Any conservative, possibly stale, gossiped vector watermark.
    pub wm: Map<(nat, int), Bound>,
    pub finalized: Set<nat>,
    pub acked: Set<int>,
    pub replayed: Set<(int, int)>,
    pub rolled: Set<(int, int)>,
}
pub open spec fn valid(c: Config) -> bool { c.shards > 0 && c.workers > 0 }
pub open spec fn shard(c: Config, i: int) -> bool { 0 <= i < c.shards }
pub open spec fn stream(c: Config, k: Stream) -> bool {
    shard(c, k.shard) && 0 <= k.worker < c.workers
}
pub open spec fn key(t: Tx, i: int) -> Stream {
    Stream { epoch: t.epoch, shard: i, worker: t.part[i] }
}
pub open spec fn covered(v: nat, b: Bound) -> bool {
    match b { Bound::Finite(n) => v <= n, Bound::Infinity => true }
}
pub open spec fn bound_le(a: Bound, b: Bound) -> bool {
    match a { Bound::Finite(n) => covered(n, b), Bound::Infinity => b is Infinity }
}
pub open spec fn endpoint(s: State, k: Stream) -> Bound {
    if s.infinity.contains(k) { Bound::Infinity } else { Bound::Finite(s.progress[k]) }
}
pub open spec fn tx_valid(c: Config, t: Tx) -> bool {
    &&& t.vc.dom() == Set::new(|i: int| shard(c, i))
    &&& !t.part.dom().is_empty()
    &&& forall|i: int| #[trigger] t.part.dom().contains(i) ==>
        shard(c, i) && 0 <= t.part[i] < c.workers && t.vc[i] > 0
}
pub open spec fn below_wm(c: Config, s: State, t: Tx) -> bool {
    forall|i: int| shard(c, i) ==> covered(t.vc[i], #[trigger] s.wm[(t.epoch, i)])
}
pub open spec fn below_cut(c: Config, s: State, t: Tx) -> bool {
    forall|k: Stream| stream(c, k) && k.epoch == t.epoch ==>
        covered(t.vc[k.shard], #[trigger] endpoint(s, k))
}
pub open spec fn doomed(c: Config, s: State, id: int) -> bool {
    s.tx.dom().contains(id) && s.finalized.contains(s.tx[id].epoch)
        && !below_cut(c, s, s.tx[id])
}
pub open spec fn vc_le(c: Config, a: Tx, b: Tx) -> bool {
    forall|i: int| shard(c, i) ==> #[trigger] a.vc[i] <= #[trigger] b.vc[i]
}
pub open spec fn initial(c: Config, s: State) -> bool {
    &&& valid(c)
    &&& s.epoch == 0
    &&& s.tx == Map::<int, Tx>::empty()
    &&& s.clock == Map::new(|p: (nat, int)| shard(c, p.1), |p| 0nat)
    &&& s.tail == Map::new(|k: Stream| stream(c, k), |k| 0nat)
    &&& s.progress == Map::new(|k: Stream| stream(c, k), |k| 0nat)
    &&& s.busy == Map::<Stream, int>::empty()
    &&& s.installed == Set::<(int, int)>::empty()
    &&& s.durable == Set::<(int, int)>::empty()
    &&& s.closed == Set::<Stream>::empty()
    &&& s.infinity == Set::<Stream>::empty()
    &&& s.wm == Map::new(|p: (nat, int)| shard(c, p.1), |p| Bound::Finite(0))
    &&& s.finalized == Set::<nat>::empty()
    &&& s.acked == Set::<int>::empty()
    &&& s.replayed == Set::<(int, int)>::empty()
    &&& s.rolled == Set::<(int, int)>::empty()
}
// The maximum read version, merged componentwise. Attainment excludes arbitrary
// invented components. Earlier-epoch versions are the stable initial snapshot.
pub open spec fn read_max(s: State, t: Tx, i: int, v: nat) -> bool {
    &&& forall|d: int| #[trigger] t.deps.contains(d) && s.tx[d].epoch == t.epoch ==> s.tx[d].vc[i] <= v
    &&& (v == 0 || exists|d: int| #[trigger] t.deps.contains(d) && s.tx[d].epoch == t.epoch && s.tx[d].vc[i] == v)
}
pub open spec fn begin_result(c: Config, s: State, id: int, t: Tx) -> State {
    State {
        tx: s.tx.insert(id, t),
        clock: Map::new(|p: (nat, int)| s.clock.dom().contains(p), |p: (nat, int)|
            if p.0 == t.epoch && t.part.dom().contains(p.1) { t.vc[p.1] } else { s.clock[p] }),
        busy: Map::new(|k: Stream| s.busy.dom().contains(k) ||
            (k.epoch == t.epoch && t.part.dom().contains(k.shard) && t.part[k.shard] == k.worker),
            |k: Stream| if k.epoch == t.epoch && t.part.dom().contains(k.shard) && t.part[k.shard] == k.worker { id } else { s.busy[k] }),
        ..s
    }
}
pub open spec fn begin(c: Config, s: State, z: State, id: int, t: Tx) -> bool {
    &&& !s.tx.dom().contains(id)
    &&& tx_valid(c, t) && t.epoch == s.epoch
    // Successful OCC reads of speculatively installed versions. Key-level
    // validation and locking are the Appendix A OCC interface.
    &&& forall|d: int| #[trigger] t.deps.contains(d) ==> s.tx.dom().contains(d)
        && s.tx[d].epoch <= t.epoch
        && (exists|i: int| s.installed.contains((d, i)))
        && (s.tx[d].epoch < t.epoch ==> below_wm(c, s, s.tx[d]))
    &&& forall|i: int| #[trigger] shard(c, i) ==> if t.part.dom().contains(i) {
        !s.busy.dom().contains(key(t, i)) && !s.closed.contains(key(t, i))
        && (exists|r: nat| read_max(s, t, i, r) && t.vc[i] ==
            if r > s.clock[(t.epoch, i)] { r } else { s.clock[(t.epoch, i)] + 1 })
    } else { read_max(s, t, i, t.vc[i]) }
    &&& z == begin_result(c, s, id, t)
}
pub open spec fn install_result(c: Config, s: State, id: int, i: int) -> State {
    State { installed: s.installed.insert((id, i)),
        tail: s.tail.insert(key(s.tx[id], i), s.tx[id].vc[i]),
        busy: s.busy.remove(key(s.tx[id], i)), ..s }
}
pub open spec fn install(c: Config, s: State, z: State, id: int, i: int) -> bool {
    &&& s.tx.dom().contains(id) && s.tx[id].part.dom().contains(i)
    &&& s.busy.dom().contains(key(s.tx[id], i)) && s.busy[key(s.tx[id], i)] == id
    &&& !s.closed.contains(key(s.tx[id], i))
    &&& z == install_result(c, s, id, i)
}
// A Paxos callback makes a prefix durable. The prefix can stop at any logged
// transaction, so replication on different streams and shards is independent.
pub open spec fn replicate_result(c: Config, s: State, k: Stream, p: nat) -> State {
    State { progress: s.progress.insert(k, p),
        durable: s.durable.union(Set::new(|f: (int, int)| s.tx.dom().contains(f.0)
            && s.tx[f.0].part.dom().contains(f.1) && key(s.tx[f.0], f.1) == k
            && s.installed.contains(f) && s.tx[f.0].vc[f.1] <= p)), ..s }
}
pub open spec fn replicate(c: Config, s: State, z: State, k: Stream, p: nat) -> bool {
    &&& stream(c, k) && !s.closed.contains(k)
    &&& s.progress[k] <= p <= s.tail[k]
    &&& (p == s.progress[k] || exists|id: int| #[trigger] s.tx.dom().contains(id)
        && s.tx[id].part.dom().contains(k.shard) && key(s.tx[id], k.shard) == k
        && s.installed.contains((id, k.shard)) && s.tx[id].vc[k.shard] == p)
    &&& z == replicate_result(c, s, k, p)
}
pub open spec fn publish_result(c: Config, s: State, e: nat, i: int, b: Bound) -> State {
    State { wm: s.wm.insert((e, i), b), ..s }
}
pub open spec fn publish(c: Config, s: State, z: State, e: nat, i: int, b: Bound) -> bool {
    &&& shard(c, i) && bound_le(s.wm[(e, i)], b)
    &&& forall|k: Stream| stream(c, k) && k.epoch == e && k.shard == i ==>
        bound_le(b, #[trigger] endpoint(s, k))
    &&& z == publish_result(c, s, e, i, b)
}
pub open spec fn advance_result(s: State) -> State {
    State { epoch: s.epoch + 1, ..s }
}
pub open spec fn advance(s: State, z: State) -> bool {
    z == advance_result(s)
}
// No more old-epoch log entries after closure. A normal close requires all
// installs and replication to finish. A failed/timed-out close retains a
// finite prefix and cannot manufacture an INF record over a pending install.
pub open spec fn close_result(c: Config, s: State, k: Stream, good: bool) -> State {
    State { closed: s.closed.insert(k),
        infinity: if good { s.infinity.insert(k) } else { s.infinity }, ..s }
}
pub open spec fn close(c: Config, s: State, z: State, k: Stream, good: bool) -> bool {
    &&& stream(c, k) && k.epoch < s.epoch && !s.closed.contains(k)
    &&& (good ==> !s.busy.dom().contains(k) && s.progress[k] == s.tail[k])
    &&& z == close_result(c, s, k, good)
}
pub open spec fn finalize_result(c: Config, s: State, e: nat) -> State {
    State { finalized: s.finalized.insert(e), ..s }
}
pub open spec fn finalize(c: Config, s: State, z: State, e: nat) -> bool {
    &&& e < s.epoch
    &&& forall|k: Stream| stream(c, k) && k.epoch == e ==> #[trigger] s.closed.contains(k)
    &&& z == finalize_result(c, s, e)
}
pub open spec fn acknowledge_result(c: Config, s: State, id: int) -> State {
    State { acked: s.acked.insert(id), ..s }
}
pub open spec fn acknowledge(c: Config, s: State, z: State, id: int) -> bool {
    &&& s.tx.dom().contains(id) && below_wm(c, s, s.tx[id])
    &&& z == acknowledge_result(c, s, id)
}
pub open spec fn replay_result(c: Config, s: State, id: int, i: int) -> State {
    State { replayed: s.replayed.insert((id, i)), ..s }
}
pub open spec fn replay(c: Config, s: State, z: State, id: int, i: int) -> bool {
    &&& s.durable.contains((id, i)) && below_wm(c, s, s.tx[id])
    &&& z == replay_result(c, s, id, i)
}
pub open spec fn rollback_result(c: Config, s: State, id: int, i: int) -> State {
    State { rolled: s.rolled.insert((id, i)), ..s }
}
pub open spec fn rollback(c: Config, s: State, z: State, id: int, i: int) -> bool {
    &&& s.installed.contains((id, i)) && doomed(c, s, id)
    &&& z == rollback_result(c, s, id, i)
}
pub enum Action {
    Begin { id: int, tx: Tx }, Install { id: int, shard: int },
    Replicate { stream: Stream, progress: nat },
    Publish { epoch: nat, shard: int, bound: Bound }, Advance,
    Close { stream: Stream, good: bool }, Finalize { epoch: nat },
    Ack { id: int }, Replay { id: int, shard: int }, Rollback { id: int, shard: int }, Stutter,
}
#[verifier::opaque]
pub open spec fn step(c: Config, s: State, z: State, a: Action) -> bool {
    match a {
        Action::Begin { id, tx } => begin(c, s, z, id, tx),
        Action::Install { id, shard } => install(c, s, z, id, shard),
        Action::Replicate { stream, progress } => replicate(c, s, z, stream, progress),
        Action::Publish { epoch, shard, bound } => publish(c, s, z, epoch, shard, bound),
        Action::Advance => advance(s, z),
        Action::Close { stream, good } => close(c, s, z, stream, good),
        Action::Finalize { epoch } => finalize(c, s, z, epoch),
        Action::Ack { id } => acknowledge(c, s, z, id),
        Action::Replay { id, shard } => replay(c, s, z, id, shard),
        Action::Rollback { id, shard } => rollback(c, s, z, id, shard),
        Action::Stutter => z == s,
    }
}
pub open spec fn effect(c: Config, s: State, a: Action) -> State {
    match a {
        Action::Begin { id, tx } => begin_result(c, s, id, tx),
        Action::Install { id, shard } => install_result(c, s, id, shard),
        Action::Replicate { stream, progress } => replicate_result(c, s, stream, progress),
        Action::Publish { epoch, shard, bound } => publish_result(c, s, epoch, shard, bound),
        Action::Advance => advance_result(s),
        Action::Close { stream, good } => close_result(c, s, stream, good),
        Action::Finalize { epoch } => finalize_result(c, s, epoch),
        Action::Ack { id } => acknowledge_result(c, s, id),
        Action::Replay { id, shard } => replay_result(c, s, id, shard),
        Action::Rollback { id, shard } => rollback_result(c, s, id, shard),
        Action::Stutter => s,
    }
}
pub open spec fn next(c: Config, s: State, z: State) -> bool {
    exists|a: Action| #[trigger] step(c, s, z, a)
}
pub open spec fn behavior(c: Config, h: Seq<State>) -> bool {
    h.len() > 0 && initial(c, h[0]) &&
        forall|j: int| 0 <= j < h.len() - 1 ==> #[trigger] next(c, h[j], h[j+1])
}
} // verus!
