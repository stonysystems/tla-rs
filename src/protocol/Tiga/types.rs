//! Immutable transaction bodies, replica state, and routed messages.
use vstd::prelude::*;

verus! {

// One integer key per shard is enough to express noncommuting stored procedures.
// Add and Read return the old value; Put returns its written value.
pub enum Op { Read, Put { value: int }, Add { delta: int } }
pub struct Txn { pub ops: Map<int, Op> }
pub struct Entry { pub id: int, pub ts: int }
pub enum Status { Normal, ViewChange, Rebuilt, Down }
pub struct Pending { pub entry: Entry, pub executed: bool }
pub struct Replica {
    pub gv: nat,
    pub lv: nat,
    pub last_normal: nat,
    pub status: Status,
    pub clock: int,
    pub queue: Map<int, Pending>,
    pub log: Seq<Entry>,
    // Number of synchronized entries, rather than the paper's inclusive index.
    pub synced: nat,
    // Abstracts rMap/wMap: timestamps of already released/executed transactions.
    pub seen: Map<int, Entry>,
}
pub enum Kind { Request, Fast, Timestamp, Sync, Slow, View, Report, Rebuilt, Start }
pub struct Packet {
    pub kind: Kind,
    pub src: int,
    pub dst: int,
    pub gv: nat,
    pub lv: nat,
    pub entry: Entry,
    pub log: Seq<Entry>,
    pub synced: nat,
    pub last_normal: nat,
    pub result: int,
}
pub struct Completion {
    pub gv: nat,
    pub ts: int,
    pub results: Map<int, int>,
    pub tick: nat,
}
pub struct Constants { pub shards: int, pub f: int }
pub struct State {
    pub nodes: Seq<Replica>,
    pub network: Set<Packet>,
    // The immutable transaction body associated with an id is carried by messages.
    // A shared dictionary avoids copying that body into every abstract packet.
    pub txns: Map<int, Txn>,
    pub invoked: Map<int, nat>,
    pub client_view: Map<int, nat>,
    pub completed: Map<int, Completion>,
    // Abstract consistent view-manager output, indexed by global view.
    pub views: Seq<Seq<nat>>,
    pub tick: nat,
}

pub open spec fn valid_constants(c: Constants) -> bool { c.shards > 0 && c.f >= 1 }
pub open spec fn replicas(c: Constants) -> int { 2 * c.f + 1 }
pub open spec fn count(c: Constants) -> int { c.shards * replicas(c) }
pub open spec fn member(c: Constants, n: int) -> bool { 0 <= n < count(c) }
pub open spec fn members(c: Constants) -> Set<int> { Set::range(0, count(c)) }
pub open spec fn shard(c: Constants, n: int) -> int { n / replicas(c) }
pub open spec fn shard_members(c: Constants, sh: int) -> Set<int> {
    Set::range(sh * replicas(c), (sh + 1) * replicas(c))
}
pub open spec fn leader(s: State, c: Constants, gv: nat, sh: int) -> int {
    sh * replicas(c) + (s.views[gv as int][sh] as int) % replicas(c)
}
pub open spec fn am_leader(s: State, c: Constants, n: int) -> bool {
    n == leader(s, c, s.nodes[n].gv, shard(c, n))
}
pub open spec fn recovery_threshold(c: Constants) -> int { (c.f + 1) / 2 + 1 }
pub open spec fn fast_size(c: Constants) -> int { c.f + recovery_threshold(c) }
pub open spec fn writes(op: Op) -> bool { !(op is Read) }
pub open spec fn conflict(s: State, sh: int, a: int, b: int) -> bool {
    s.txns[a].ops.dom().contains(sh) && s.txns[b].ops.dom().contains(sh)
        && (writes(s.txns[a].ops[sh]) || writes(s.txns[b].ops[sh]))
}
pub open spec fn before(a: Entry, b: Entry) -> bool {
    a.ts < b.ts || (a.ts == b.ts && a.id < b.id)
}
pub open spec fn ids(log: Seq<Entry>) -> Set<int> { log.to_set().map(|e: Entry| e.id) }
pub open spec fn sorted(log: Seq<Entry>) -> bool {
    forall |i: int, j: int| 0 <= i < j < log.len() ==> before(log[i], log[j])
}
pub open spec fn distinct(log: Seq<Entry>) -> bool {
    forall |i: int, j: int| #![trigger log[i], log[j]] 0 <= i < j < log.len() ==> log[i].id != log[j].id
}
pub open spec fn apply_op(value: int, op: Op) -> int {
    match op { Op::Read => value, Op::Put { value: v } => v, Op::Add { delta } => value + delta }
}
pub open spec fn return_op(value: int, op: Op) -> int {
    match op { Op::Put { value: v } => v, _ => value }
}
pub open spec fn eval(txns: Map<int, Txn>, sh: int, log: Seq<Entry>) -> int
    decreases log.len()
{
    if log.len() == 0 { 0 } else {
        apply_op(eval(txns, sh, log.drop_last()), txns[log.last().id].ops[sh])
    }
}
pub open spec fn log_seen(log: Seq<Entry>) -> Map<int, Entry> {
    Map::new(ids(log), |id: int| choose |e: Entry| #![trigger log.contains(e)] log.contains(e) && e.id == id)
}
pub open spec fn empty_replica() -> Replica {
    Replica { gv: 0, lv: 0, last_normal: 0, status: Status::Normal, clock: 0,
        queue: Map::empty(), log: Seq::empty(), synced: 0, seen: Map::empty() }
}
pub open spec fn initial(c: Constants) -> State {
    State { nodes: Seq::new(count(c) as nat, |n: int| empty_replica()),
        network: Set::empty(), txns: Map::empty(), invoked: Map::empty(),
        client_view: Map::empty(), completed: Map::empty(),
        views: seq![Seq::new(c.shards as nat, |sh: int| 0nat)], tick: 0 }
}
pub open spec fn packet(kind: Kind, src: int, dst: int, gv: nat, lv: nat, e: Entry) -> Packet {
    Packet { kind, src, dst, gv, lv, entry: e, log: Seq::empty(), synced: 0,
        last_normal: 0, result: 0 }
}
pub open spec fn blank_entry() -> Entry { Entry { id: -1, ts: 0 } }
pub open spec fn broadcast(p: Packet, destinations: Set<int>) -> Set<Packet> {
    destinations.map(|dst: int| Packet { dst, ..p })
}
pub open spec fn replace(s: State, node: int, r: Replica, output: Set<Packet>) -> State {
    State { nodes: s.nodes.update(node, r), network: s.network.union(output), ..s }
}
pub open spec fn routed(s: State, c: Constants, p: Packet) -> bool {
    s.network.contains(p) && member(c, p.dst)
}
pub open spec fn current(s: State, c: Constants, p: Packet) -> bool {
    routed(s, c, p) && s.nodes[p.dst].gv == p.gv
        && s.nodes[p.dst].lv == p.lv
}

} // verus!
