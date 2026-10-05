//! Key-level OCC for one speculation epoch (paper Section 4.2).
//! Locks and validation are separate transitions. Serial numbers are proof-only:
//! validation compares version vectors, never the ghost serial order.
use vstd::prelude::*;
use vstd::imap::IMap as Map;
use vstd::iset::ISet as Set;

verus! {

pub struct Key { pub shard: int, pub record: int }
pub struct Version { pub writer: Option<int>, pub value: int, pub serial: nat, pub ticket: nat, pub vc: Map<int, nat> }
pub struct Read { pub key: Key, pub version: Version }
pub enum Phase { Running, Locking, Checking, Certified, Aborted }
pub struct Tx {
    pub phase: Phase,
    pub writes: Map<Key, int>,
    pub reads: Seq<Read>,
    pub checked: Set<int>,
    pub tickets: Map<int, nat>,
    pub vc: Map<int, nat>,
    pub serial: nat,
}
pub struct Config { pub shards: int, pub base: Map<Key, int> }
pub struct State {
    pub tx: Map<int, Tx>,
    pub data: Map<Key, Version>,
    pub locks: Map<Key, int>,
    pub clocks: Map<int, nat>,
    pub installed: Set<(int, Key)>,
    // A ghost counter chooses a serial order after acquiring all write locks
    // and before issuing validation requests. This is not a timestamp service.
    pub serial: nat,
}
pub open spec fn key(c: Config, k: Key) -> bool { 0 <= k.shard < c.shards }
pub open spec fn active(t: Tx) -> bool { t.phase is Checking || t.phase is Certified }
pub open spec fn zero(c: Config) -> Map<int, nat> {
    Map::new(|sh: int| 0 <= sh < c.shards, |sh| 0nat)
}
pub open spec fn max(a: nat, b: nat) -> nat { if a >= b { a } else { b } }
pub open spec fn read_max(rs: Seq<Read>, sh: int, n: nat) -> nat
    decreases n
{ if n == 0 { 0 } else { max(read_max(rs, sh, (n-1) as nat), rs[n as int-1].version.vc[sh]) } }
pub open spec fn vector(c: Config, t: Tx) -> Map<int, nat> {
    Map::new(|sh: int| 0 <= sh < c.shards, |sh: int|
        max(if t.tickets.dom().contains(sh) { t.tickets[sh] } else { 0 }, read_max(t.reads, sh, t.reads.len())))
}
pub open spec fn initial(c: Config, s: State) -> bool {
    &&& c.shards > 0 && c.base.dom() == Set::new(|k: Key| key(c, k))
    &&& s.tx == Map::<int, Tx>::empty()
    &&& s.data == Map::new(|k: Key| key(c, k), |k: Key| Version { writer: None, value: c.base[k], serial: 0, ticket: 0, vc: zero(c) })
    &&& s.clocks == Map::new(|sh: int| 0 <= sh < c.shards, |sh| 0nat)
    &&& s.locks == Map::<Key, int>::empty()
    &&& s.installed == Set::<(int, Key)>::empty() && s.serial == 0
}
pub open spec fn owns(s: State, id: int, k: Key) -> bool {
    s.locks.dom().contains(k) && s.locks[k] == id
}
pub open spec fn unlocked_or_own(s: State, id: int, k: Key) -> bool {
    !s.locks.dom().contains(k) || s.locks[k] == id
}
pub open spec fn all_locked(s: State, id: int) -> bool {
    forall|k: Key| #[trigger] s.tx[id].writes.dom().contains(k) ==> owns(s, id, k)
}
pub open spec fn all_checked(t: Tx) -> bool {
    forall|j: int| 0 <= j < t.reads.len() ==> #[trigger] t.checked.contains(j)
}
pub open spec fn validation(s: State, id: int, j: int) -> bool {
    &&& s.tx.dom().contains(id) && s.tx[id].phase is Checking
    &&& 0 <= j < s.tx[id].reads.len()
    &&& s.data[s.tx[id].reads[j].key].vc == s.tx[id].reads[j].version.vc
    &&& unlocked_or_own(s, id, s.tx[id].reads[j].key)
}
pub open spec fn deps(s: State, id: int) -> Set<int> {
    Set::new(|d: int| exists|j: int| 0 <= j < s.tx[id].reads.len()
        && #[trigger] s.tx[id].reads[j].version.writer == Some(d))
}
pub enum Action {
    Open { id: int }, Read { id: int, key: Key }, Write { id: int, key: Key, value: int },
    Freeze { id: int }, Lock { id: int, key: Key },
    // Separate shard replies permit arbitrary GetClock interleavings.
    GetClock { id: int, shard: int },
    // The proof-only serialization point follows the last clock reply.
    Check { id: int }, Validate { id: int, index: int }, Certify { id: int },
    Install { id: int, shard: int }, Abort { id: int }, Stutter,
}
pub open spec fn update(s: State, id: int, t: Tx) -> State {
    State { tx: s.tx.insert(id, t), ..s }
}
pub open spec fn effect(c: Config, s: State, a: Action) -> State {
    match a {
        Action::Open { id } => update(s, id, Tx { phase: Phase::Running,
            writes: Map::empty(), reads: Seq::empty(), checked: Set::empty(), tickets: Map::empty(), vc: Map::empty(), serial: 0 }),
        Action::Read { id, key: k } => update(s, id, Tx {
            reads: s.tx[id].reads.push(Read { key: k, version: s.data[k] }), ..s.tx[id] }),
        Action::Write { id, key: k, value } => update(s, id, Tx {
            writes: s.tx[id].writes.insert(k, value), ..s.tx[id] }),
        Action::Freeze { id } => update(s, id, Tx { phase: Phase::Locking, ..s.tx[id] }),
        Action::Lock { id, key: k } => State { locks: s.locks.insert(k, id), ..s },
        Action::GetClock { id, shard: sh } => State { clocks: s.clocks.insert(sh, s.clocks[sh] + 1),
            tx: s.tx.insert(id, Tx { tickets: s.tx[id].tickets.insert(sh, s.clocks[sh] + 1), ..s.tx[id] }), ..s },
        Action::Check { id } => State { serial: s.serial + 1,
            tx: s.tx.insert(id, Tx { phase: Phase::Checking, serial: s.serial + 1, vc: vector(c, s.tx[id]), ..s.tx[id] }), ..s },
        Action::Validate { id, index } => update(s, id, Tx {
            checked: s.tx[id].checked.insert(index), ..s.tx[id] }),
        Action::Certify { id } => update(s, id, Tx { phase: Phase::Certified, ..s.tx[id] }),
        Action::Install { id, shard: sh } => State {
            data: Map::new(|k: Key| key(c, k), |k: Key|
                if k.shard == sh && s.tx[id].writes.dom().contains(k) {
                    Version { writer: Some(id), value: s.tx[id].writes[k], serial: s.tx[id].serial, ticket: s.tx[id].tickets[k.shard], vc: s.tx[id].vc }
                } else { s.data[k] }),
            locks: s.locks.remove_keys(Set::new(|k: Key| k.shard == sh && s.tx[id].writes.dom().contains(k))),
            installed: s.installed.union(Set::new(|p: (int, Key)| p.0 == id && p.1.shard == sh && s.tx[id].writes.dom().contains(p.1))), ..s },
        Action::Abort { id } => State { tx: s.tx.insert(id, Tx { phase: Phase::Aborted, ..s.tx[id] }),
            locks: s.locks.remove_keys(Set::new(|k: Key| owns(s, id, k))), ..s },
        Action::Stutter => s,
    }
}
#[verifier::opaque]
pub open spec fn step(c: Config, s: State, z: State, a: Action) -> bool {
    &&& z == effect(c, s, a)
    &&& match a {
        Action::Open { id } => !s.tx.dom().contains(id),
        Action::Read { id, key: k } => s.tx.dom().contains(id) && s.tx[id].phase is Running
            && key(c, k) && !s.locks.dom().contains(k),
        Action::Write { id, key: k, value } => s.tx.dom().contains(id) && s.tx[id].phase is Running && key(c, k),
        Action::Freeze { id } => s.tx.dom().contains(id) && s.tx[id].phase is Running,
        Action::Lock { id, key: k } => s.tx.dom().contains(id) && s.tx[id].phase is Locking
            && s.tx[id].writes.dom().contains(k) && !s.locks.dom().contains(k),
        Action::GetClock { id, shard: sh } => s.tx.dom().contains(id) && s.tx[id].phase is Locking
            && all_locked(s, id) && 0 <= sh < c.shards && !s.tx[id].tickets.dom().contains(sh)
            && (exists|k: Key| k.shard == sh && #[trigger] s.tx[id].writes.dom().contains(k)),
        Action::Check { id } => s.tx.dom().contains(id) && s.tx[id].phase is Locking && all_locked(s, id)
            && (forall|k: Key| #[trigger] s.tx[id].writes.dom().contains(k) ==> s.tx[id].tickets.dom().contains(k.shard)),
        Action::Validate { id, index } => validation(s, id, index),
        Action::Certify { id } => s.tx.dom().contains(id) && s.tx[id].phase is Checking && all_checked(s.tx[id]),
        Action::Install { id, shard: sh } => s.tx.dom().contains(id) && s.tx[id].phase is Certified
            && 0 <= sh < c.shards
            && (exists|k: Key| k.shard == sh && #[trigger] s.tx[id].writes.dom().contains(k))
            && (forall|k: Key| k.shard == sh && #[trigger] s.tx[id].writes.dom().contains(k) ==> owns(s, id, k)),
        Action::Abort { id } => s.tx.dom().contains(id) && !(s.tx[id].phase is Certified) && !(s.tx[id].phase is Aborted),
        Action::Stutter => true,
    }
}
pub open spec fn next(c: Config, s: State, z: State) -> bool { exists|a: Action| #[trigger] step(c, s, z, a) }
pub open spec fn behavior(c: Config, h: Seq<State>) -> bool {
    h.len() > 0 && initial(c, h[0]) && forall|i: int| 0 <= i < h.len()-1 ==> #[trigger] next(c, h[i], h[i+1])
}
} // verus!
