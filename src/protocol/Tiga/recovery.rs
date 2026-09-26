//! Section 4 and technical-report Algorithm 5, including cross-shard import.
use super::types::*;
use vstd::prelude::*;

verus! {

pub open spec fn can_new_view(s: State, c: Constants, views: Seq<nat>) -> bool {
    views.len() == c.shards && forall |sh: int| 0 <= sh < c.shards
        ==> #[trigger] views[sh] >= s.views.last()[sh]
}
pub open spec fn new_view(s: State, c: Constants, views: Seq<nat>) -> State {
    let gv = s.views.len();
    let output = members(c).map(|n: int|
        packet(Kind::View, -2, n, gv, views[shard(c, n)], blank_entry()));
    State { views: s.views.push(views), network: s.network.union(output), ..s }
}
pub open spec fn can_enter_view(s: State, c: Constants, p: Packet, pending: Seq<Entry>) -> bool {
    let r = s.nodes[p.dst];
    &&& routed(s, c, p)
    &&& p.kind is View
    &&& !(r.status is Down)
    &&& p.gv > r.gv
    &&& ids(pending) == r.queue.dom()
    &&& sorted(pending) && distinct(pending)
    &&& forall |i: int| 0 <= i < pending.len() ==> #[trigger] pending[i] == r.queue[pending[i].id].entry
}
pub open spec fn enter_view(s: State, c: Constants, p: Packet, pending: Seq<Entry>) -> State {
    let r = s.nodes[p.dst];
    let log = r.log + pending;
    let next = Replica { gv: p.gv, lv: p.lv, status: Status::ViewChange,
        log, queue: Map::empty(), ..r };
    let report = Packet { log, synced: r.synced, last_normal: r.last_normal,
        ..packet(Kind::Report, p.dst, leader(s, c, p.gv, shard(c, p.dst)), p.gv, p.lv, blank_entry()) };
    replace(s, p.dst, next, set![report])
}
pub open spec fn view_reports(s: State, c: Constants, n: int, batch: Map<int, Packet>) -> bool {
    let r = s.nodes[n];
    &&& batch.dom().subset_of(shard_members(c, shard(c, n)))
    &&& batch.dom().len() == c.f + 1
    &&& forall |sender: int| #[trigger] batch.dom().contains(sender) ==> {
        let p = batch[sender];
        &&& s.network.contains(p)
        &&& p.src == sender && p.dst == n
        &&& p.kind is Report
        &&& p.gv == r.gv && p.lv == r.lv
        &&& p.synced <= p.log.len()
    }
}
pub open spec fn maximal_snapshot(batch: Map<int, Packet>, selected: int) -> bool {
    &&& batch.dom().contains(selected)
    &&& forall |n: int| #[trigger] batch.dom().contains(n) ==> {
        batch[n].last_normal <= batch[selected].last_normal
            && (batch[n].last_normal == batch[selected].last_normal ==> batch[n].synced <= batch[selected].synced)
    }
}
pub open spec fn tail_candidates(batch: Map<int, Packet>) -> Set<Entry> {
    batch.dom().map(|n: int| batch[n].log.skip(batch[n].synced as int).to_set()).flatten()
}
pub open spec fn supporters(batch: Map<int, Packet>, e: Entry) -> Set<int> {
    batch.dom().filter(|n: int| batch[n].log.contains(e))
}
pub open spec fn recovered_entries(c: Constants, batch: Map<int, Packet>, selected: int) -> Set<Entry> {
    let base = batch[selected].log.take(batch[selected].synced as int);
    let tail = tail_candidates(batch).filter(|e: Entry| supporters(batch, e).len() >= recovery_threshold(c)
        && !ids(base).contains(e.id)
        && forall |i: int| #![trigger base[i]] 0 <= i < base.len() ==> before(base[i], e));
    base.to_set().union(tail)
}
pub open spec fn can_rebuild(s: State, c: Constants, n: int, batch: Map<int, Packet>,
    selected: int, log: Seq<Entry>) -> bool {
    &&& member(c, n)
    &&& s.nodes[n].status is ViewChange
    &&& am_leader(s, c, n)
    &&& view_reports(s, c, n, batch)
    &&& maximal_snapshot(batch, selected)
    &&& sorted(log) && distinct(log)
    &&& log.to_set() == recovered_entries(c, batch, selected)
}
pub open spec fn rebuild(s: State, c: Constants, n: int, log: Seq<Entry>) -> State {
    let r = s.nodes[n];
    let output = Set::range(0, c.shards).map(|sh: int| Packet { log,
        ..packet(Kind::Rebuilt, n, leader(s, c, r.gv, sh), r.gv, s.views[r.gv as int][sh], blank_entry()) });
    replace(s, n, Replica { status: Status::Rebuilt, log, synced: 0, ..r }, output)
}
pub open spec fn reconstruction_reports(s: State, c: Constants, n: int, batch: Map<int, Packet>) -> bool {
    let r = s.nodes[n];
    &&& batch.dom() == Set::range(0, c.shards)
    &&& forall |sh: int| #[trigger] batch.dom().contains(sh) ==> {
        let p = batch[sh];
        &&& s.network.contains(p)
        &&& p.kind is Rebuilt
        &&& p.src == leader(s, c, r.gv, sh) && p.dst == n
        &&& p.gv == r.gv && p.lv == r.lv
    }
}
pub open spec fn imported_entries(s: State, c: Constants, n: int, batch: Map<int, Packet>) -> Set<Entry> {
    batch.dom().map(|sh: int| batch[sh].log.to_set()).flatten()
        .filter(|e: Entry| s.txns[e.id].ops.dom().contains(shard(c, n)))
}
pub open spec fn merged_entries(s: State, c: Constants, n: int, batch: Map<int, Packet>) -> Set<Entry> {
    let candidates = imported_entries(s, c, n, batch);
    candidates.filter(|e: Entry| forall |other: Entry| #[trigger] candidates.contains(other)
        && other.id == e.id ==> other.ts <= e.ts)
}
pub open spec fn can_install(s: State, c: Constants, n: int, batch: Map<int, Packet>, log: Seq<Entry>) -> bool {
    &&& member(c, n)
    &&& s.nodes[n].status is Rebuilt
    &&& am_leader(s, c, n)
    &&& reconstruction_reports(s, c, n, batch)
    &&& sorted(log) && distinct(log)
    // Algorithm 5, lines 73-89: import missing ids, choose each maximum
    // reported timestamp, then sort. No local timestamp repair is inserted.
    &&& log.to_set() == merged_entries(s, c, n, batch)
}
pub open spec fn install(s: State, c: Constants, n: int, log: Seq<Entry>) -> State {
    let r = s.nodes[n];
    let next = Replica { status: Status::Normal, last_normal: r.lv,
        log, synced: log.len(), queue: Map::empty(), seen: log_seen(log), ..r };
    let p = Packet { log, synced: log.len(), last_normal: r.lv,
        ..packet(Kind::Start, n, n, r.gv, r.lv, blank_entry()) };
    replace(s, n, next, broadcast(p, shard_members(c, shard(c, n)).remove(n)))
}
pub open spec fn can_start(s: State, c: Constants, p: Packet) -> bool {
    &&& current(s, c, p)
    &&& p.kind is Start
    &&& p.src == leader(s, c, p.gv, shard(c, p.dst))
    &&& p.dst != p.src
    &&& s.nodes[p.dst].status is ViewChange
}
pub open spec fn start(s: State, c: Constants, p: Packet) -> State {
    let r = s.nodes[p.dst];
    replace(s, p.dst, Replica { status: Status::Normal, last_normal: r.lv,
        log: p.log, synced: p.synced, queue: Map::empty(), seen: log_seen(p.log), ..r }, Set::empty())
}

} // verus!
