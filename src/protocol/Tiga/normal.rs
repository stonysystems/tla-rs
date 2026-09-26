//! Sections 3.1-3.7 and technical-report Algorithms 2 and 3.
use super::types::*;
use vstd::prelude::*;

verus! {

pub open spec fn can_submit(s: State, c: Constants, id: int, txn: Txn, ts: int) -> bool {
    id >= 0 && ts >= 0 && !s.txns.dom().contains(id) && txn.ops.dom().len() > 0
        && txn.ops.dom().subset_of(Set::range(0, c.shards))
}
pub open spec fn submit(s: State, c: Constants, id: int, txn: Txn, ts: int) -> State {
    let gv = (s.views.len() - 1) as nat;
    let packets = members(c).filter(|n: int| txn.ops.dom().contains(shard(c, n)))
        .map(|n: int| packet(Kind::Request, -1, n, gv, s.views[gv as int][shard(c, n)], Entry { id, ts }));
    State { txns: s.txns.insert(id, txn), invoked: s.invoked.insert(id, s.tick),
        client_view: s.client_view.insert(id, gv), network: s.network.union(packets), ..s }
}
pub open spec fn acceptable(s: State, c: Constants, n: int, e: Entry) -> bool {
    forall |id: int| #[trigger] s.nodes[n].seen.dom().contains(id)
        && conflict(s, shard(c, n), id, e.id) ==> before(s.nodes[n].seen[id], e)
}
pub open spec fn can_receive(s: State, c: Constants, p: Packet) -> bool {
    &&& current(s, c, p)
    &&& p.kind is Request
    &&& s.nodes[p.dst].status is Normal
    &&& s.txns.dom().contains(p.entry.id)
    &&& s.txns[p.entry.id].ops.dom().contains(shard(c, p.dst))
    &&& !ids(s.nodes[p.dst].log).contains(p.entry.id)
    &&& !s.nodes[p.dst].queue.dom().contains(p.entry.id)
    &&& acceptable(s, c, p.dst, p.entry) || (am_leader(s, c, p.dst)
        && acceptable(s, c, p.dst, Entry { ts: s.nodes[p.dst].clock, ..p.entry }))
}
pub open spec fn receive(s: State, c: Constants, p: Packet) -> State {
    let r = s.nodes[p.dst];
    let e = if acceptable(s, c, p.dst, p.entry) { p.entry }
        else { Entry { ts: r.clock, ..p.entry } };
    replace(s, p.dst, Replica { queue: r.queue.insert(e.id, Pending { entry: e, executed: false }), ..r }, Set::empty())
}
pub open spec fn can_release(s: State, c: Constants, n: int, id: int) -> bool {
    let r = s.nodes[n];
    &&& member(c, n)
    &&& r.status is Normal
    &&& r.queue.dom().contains(id)
    &&& !r.queue[id].executed
    &&& r.queue[id].entry.ts <= r.clock
    &&& forall |other: int| #[trigger] r.queue.dom().contains(other)
        && other != id && conflict(s, shard(c, n), id, other)
        ==> before(r.queue[id].entry, r.queue[other].entry)
}
pub open spec fn notifications(s: State, c: Constants, n: int, e: Entry) -> Set<Packet> {
    let r = s.nodes[n];
    s.txns[e.id].ops.dom().map(|sh: int|
        packet(Kind::Timestamp, n, leader(s, c, r.gv, sh), r.gv, s.views[r.gv as int][sh], e))
}
pub open spec fn release(s: State, c: Constants, n: int, id: int) -> State {
    let r = s.nodes[n];
    let e = r.queue[id].entry;
    let p = Packet { log: r.log, result: if am_leader(s, c, n) {
        return_op(eval(s.txns, shard(c, n), r.log), s.txns[id].ops[shard(c, n)])
    } else { 0 }, ..packet(Kind::Fast, n, -1, r.gv, r.lv, e) };
    if am_leader(s, c, n) {
        replace(s, n, Replica { queue: r.queue.insert(id, Pending { executed: true, entry: e }),
            seen: r.seen.insert(id, e), ..r }, notifications(s, c, n, e).insert(p))
    } else {
        replace(s, n, Replica { queue: r.queue.remove(id), log: r.log.push(e),
            seen: r.seen.insert(id, e), ..r }, set![p])
    }
}
pub open spec fn timestamp_replies(s: State, c: Constants, n: int, id: int, batch: Map<int, Packet>) -> bool {
    let r = s.nodes[n];
    &&& batch.dom() == s.txns[id].ops.dom()
    &&& forall |sh: int| #[trigger] batch.dom().contains(sh) ==> {
        let p = batch[sh];
        &&& s.network.contains(p)
        &&& p.kind is Timestamp
        &&& p.src == leader(s, c, r.gv, sh)
        &&& p.dst == n
        &&& p.gv == r.gv
        &&& p.lv == r.lv
        &&& p.entry.id == id
    }
}
pub open spec fn can_agree(s: State, c: Constants, n: int, id: int, batch: Map<int, Packet>, ts: int) -> bool {
    let r = s.nodes[n];
    &&& member(c, n)
    &&& am_leader(s, c, n)
    &&& r.status is Normal
    &&& r.queue.dom().contains(id)
    &&& r.queue[id].executed
    &&& timestamp_replies(s, c, n, id, batch)
    &&& exists |sh: int| #![trigger batch.dom().contains(sh)] batch.dom().contains(sh) && batch[sh].entry.ts == ts
    &&& forall |sh: int| #[trigger] batch.dom().contains(sh) ==> batch[sh].entry.ts <= ts
    // A smaller local timestamp is revoked. At the maximum, wait for matching
    // execution notifications from every participant before dequeueing.
    &&& r.queue[id].entry.ts < ts || (r.queue[id].entry.ts == ts
        && forall |sh: int| #[trigger] batch.dom().contains(sh) ==> batch[sh].entry.ts == ts)
}
pub open spec fn agree(s: State, c: Constants, n: int, id: int, ts: int) -> State {
    let r = s.nodes[n];
    let e = Entry { ts, ..r.queue[id].entry };
    if r.queue[id].entry.ts < ts {
        // Speculative effects are derived from the queue, not made durable.
        replace(s, n, Replica { queue: r.queue.insert(id, Pending { entry: e, executed: false }), ..r }, Set::empty())
    } else {
        let log = r.log.push(e);
        let p = Packet { log, synced: log.len(), ..packet(Kind::Sync, n, n, r.gv, r.lv, e) };
        replace(s, n, Replica { queue: r.queue.remove(id), log, synced: log.len(), ..r },
            broadcast(p, shard_members(c, shard(c, n)).remove(n)))
    }
}
pub open spec fn can_sync(s: State, c: Constants, p: Packet) -> bool {
    &&& current(s, c, p)
    &&& p.kind is Sync
    &&& s.nodes[p.dst].status is Normal
    &&& p.src == leader(s, c, p.gv, shard(c, p.dst))
    &&& p.dst != p.src
    &&& p.synced >= s.nodes[p.dst].synced
}
pub open spec fn sync(s: State, c: Constants, p: Packet) -> State {
    let r = s.nodes[p.dst];
    let reply = Packet { log: p.log, synced: p.synced,
        ..packet(Kind::Slow, p.dst, -1, p.gv, p.lv, p.entry) };
    replace(s, p.dst, Replica { log: p.log, synced: p.synced, seen: log_seen(p.log),
        queue: r.queue.remove_keys(ids(p.log)), ..r }, set![reply])
}

// A map of actual replies deduplicates senders. Full prefix equality models
// collision-free hashes without assuming a cryptographic result.
pub open spec fn shard_certificate(s: State, c: Constants, id: int, gv: nat, sh: int,
    first: Packet, votes: Map<int, Packet>) -> bool {
    &&& s.network.contains(first)
    &&& first.kind is Fast
    &&& first.src == leader(s, c, gv, sh)
    &&& first.dst == -1
    &&& first.gv == gv
    &&& first.lv == s.views[gv as int][sh]
    &&& first.entry.id == id
    &&& votes.dom().subset_of(shard_members(c, sh))
    &&& votes.dom().contains(first.src)
    &&& votes[first.src] == first
    &&& forall |n: int| #[trigger] votes.dom().contains(n) ==> {
        let p = votes[n];
        &&& s.network.contains(p)
        &&& p.src == n && p.dst == -1 && p.gv == gv && p.lv == first.lv
        &&& p.entry == first.entry
        &&& (p.kind is Fast && p.log == first.log)
            || (p.kind is Slow && p.log.len() > first.log.len()
                && p.log.take(first.log.len() as int) == first.log
                && p.log[first.log.len() as int] == first.entry
                && p.synced > first.log.len())
    }
    &&& votes.dom().len() >= fast_size(c)
        || votes.dom().filter(|n: int| votes[n].kind is Slow).len() >= c.f
}
pub open spec fn can_complete(s: State, c: Constants, id: int, leaders: Map<int, Packet>,
    votes: Map<int, Map<int, Packet>>, ts: int) -> bool {
    &&& s.txns.dom().contains(id)
    &&& !s.completed.dom().contains(id)
    &&& leaders.dom() == s.txns[id].ops.dom()
    &&& votes.dom() == leaders.dom()
    &&& forall |sh: int| #[trigger] leaders.dom().contains(sh) ==> {
        shard_certificate(s, c, id, s.client_view[id], sh, leaders[sh], votes[sh])
            && leaders[sh].entry.ts == ts
    }
}
pub open spec fn complete(s: State, id: int, leaders: Map<int, Packet>, ts: int) -> State {
    let completion = Completion { gv: s.client_view[id], ts, tick: s.tick,
        results: Map::new(leaders.dom(), |sh: int| leaders[sh].result) };
    State { completed: s.completed.insert(id, completion), ..s }
}

} // verus!
