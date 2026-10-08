//! Handwritten snapshot configuration of MultiShardTxn and Storage.
//! NoValue remains an integer parameter: the source excludes transaction IDs,
//! but does not exclude timestamps. Router read timestamps preserve that aliasing.
use vstd::prelude::*;
verus! {
pub enum Kind { Read,Write }
pub enum Status { Ok,Rollback,NotFound,PrepareConflict }
pub struct Operation { pub kind: Kind,pub key: int,pub value: int }
pub struct Participant { pub shard: int,pub kinds: Set<Kind> }
pub struct RTransaction { pub count: nat,pub read_ts: int,pub committing: bool,pub participants: Seq<Participant> }
pub enum Request { Op { key: int,kind: Kind,shard: int,coordinator: bool,start: bool,read_ts: int },Coordinate { shard: int,participants: Seq<int> } }
pub struct Snapshot { pub active: bool,pub committed: bool,pub aborted: bool,pub prepared: bool,pub prepare_ts: int,pub ts: int,
    pub data: IMap<int,int>,pub reads: Set<int>,pub writes: Set<int> }
pub struct Transaction { pub requests: Seq<Request>,pub coordinator: bool,pub participants: Seq<int>,pub committing: bool,
    pub votes: Set<(int,int)>,pub ops: Seq<Operation>,pub aborted: bool,pub snapshot: Snapshot,pub status: Status }
pub struct LogEntry { pub txn: int,pub ts: int,pub prepare: bool,pub data: IMap<int,int>,pub durable: Option<int> }
pub struct LShard { pub active: Set<int>,pub prepared: Set<int>,pub log: Seq<LogEntry>,pub txns: IMap<int,Transaction>,pub durable: int }
pub struct Prepare { pub shard: int,pub txn: int,pub coordinator: int }
pub struct Vote { pub shard: int,pub txn: int,pub to: int,pub ts: int }
pub struct Commit { pub shard: int,pub txn: int,pub ts: int }
pub struct Constants { pub keys: ISet<int>,pub txns: ISet<int>,pub routers: ISet<int>,pub shards: ISet<int>,pub timestamps: ISet<int>,pub no_value: int }
pub struct LState { pub catalog: IMap<int,int>,pub routers: IMap<int,IMap<int,RTransaction>>,pub shards: IMap<int,LShard>,pub ops: IMap<int,Seq<Operation>>,
    pub prepares: Set<Prepare>,pub votes: Set<Vote>,pub commits: Set<Commit> }
pub open spec fn valid_constants(c: Constants) -> bool { !c.txns.contains(c.no_value) && forall |ts: int| c.timestamps.contains(ts) ==> ts >= 0 }
pub open spec fn valid_catalog(c: Constants,catalog: IMap<int,int>) -> bool { catalog.dom() == c.keys && forall |k: int| #![trigger c.keys.contains(k)] c.keys.contains(k) ==> c.shards.contains(catalog[k]) }
pub open spec fn empty_snapshot(c: Constants) -> Snapshot { Snapshot { active: false,committed: false,aborted: false,prepared: false,prepare_ts: 0,ts: 0,
    data: IMap::new(|k: int| c.keys.contains(k),|k: int| c.no_value),reads: Set::empty(),writes: Set::empty() } }
pub open spec fn initial(c: Constants,catalog: IMap<int,int>) -> LState {
    LState { catalog,routers: IMap::new(|r: int| c.routers.contains(r),|r: int| IMap::new(|t: int| c.txns.contains(t),|t: int| RTransaction { count: 0,read_ts: c.no_value,committing: false,participants: Seq::empty() })),
        shards: IMap::new(|s: int| c.shards.contains(s),|s: int| LShard { active: Set::empty(),prepared: Set::empty(),log: Seq::empty(),durable: 0,
            txns: IMap::new(|t: int| c.txns.contains(t),|t: int| Transaction { requests: Seq::empty(),coordinator: false,participants: Seq::empty(),committing: false,
                votes: Set::empty(),ops: Seq::empty(),aborted: false,snapshot: empty_snapshot(c),status: Status::Ok }) }),
        ops: IMap::new(|t: int| c.txns.contains(t),|t: int| Seq::empty()),prepares: Set::empty(),votes: Set::empty(),commits: Set::empty() }
}
#[verifier::opaque]
pub open spec fn maximum(q: ISet<int>) -> int { choose |v: int| q.contains(v) && forall |w: int| q.contains(w) ==> w <= v }
pub open spec fn active_read_ts(n: LShard,c: Constants) -> ISet<int> { c.txns.map(|t: int| if n.txns[t].snapshot.active { n.txns[t].snapshot.ts } else { 0 }) }
pub open spec fn log_ts(n: LShard) -> ISet<int> { n.log.to_set().map(|e: LogEntry| e.ts).to_iset() }
pub open spec fn next_ts(n: LShard,c: Constants) -> int { maximum(log_ts(n).union(active_read_ts(n,c)))+1 }
pub open spec fn all_durable(n: LShard,c: Constants) -> int {
    if exists |t: int| #![trigger c.txns.contains(t)] c.txns.contains(t) && n.txns[t].snapshot.committed {
        maximum(n.log.to_set().filter(|e: LogEntry| !e.prepare).map(|e: LogEntry| e.ts).to_iset())
    } else { 0 }
}
pub open spec fn snapshot_read(n: LShard,c: Constants,k: int,ts: int) -> int {
    let q=Set::range(0,n.log.len() as int).filter(|i: int| !n.log[i].prepare && n.log[i].data.dom().contains(k) && n.log[i].ts <= ts);
    if q.is_empty() { c.no_value } else { n.log[maximum(q.to_iset())].data[k] }
}
pub open spec fn new_snapshot(n: LShard,c: Constants,ts: int) -> Snapshot {
    Snapshot { active: true,ts,data: IMap::new(|k: int| c.keys.contains(k),|k: int| snapshot_read(n,c,k,ts)),..empty_snapshot(c) }
}
pub open spec fn write_conflict(n: LShard,c: Constants,t: int,k: int) -> bool {
    exists |other: int| #![trigger c.txns.contains(other)] c.txns.contains(other) && other != t && (
        n.txns[t].snapshot.active && n.txns[other].snapshot.active && n.txns[other].snapshot.writes.contains(k)
        || exists |i: int| 0 <= i < n.log.len() && !(#[trigger] n.log[i]).prepare && n.log[i].ts > n.txns[t].snapshot.ts && n.log[i].data.dom().contains(k))
}
pub open spec fn prepare_conflict(n: LShard,c: Constants,t: int,k: int) -> bool {
    exists |other: int| #![trigger c.txns.contains(other)] c.txns.contains(other) && other != t && n.txns[other].snapshot.active && n.txns[other].snapshot.prepared
        && n.txns[other].snapshot.writes.contains(k) && n.txns[other].snapshot.prepare_ts <= n.txns[t].snapshot.ts
}
pub open spec fn txn_read(n: LShard,c: Constants,t: int,k: int) -> int {
    if exists |other: int,p: int,m: int| #![trigger c.txns.contains(other), n.log[p], n.log[m]] c.txns.contains(other) && other != t && 0 <= p < n.log.len() && 0 <= m < n.log.len()
        && n.log[p].prepare && n.log[p].txn == other && !n.log[m].prepare && n.log[m].txn == other && n.log[m].ts <= n.txns[t].snapshot.ts
        && n.log[m].data.dom().contains(k) && !n.txns[t].snapshot.writes.contains(k) {
        snapshot_read(n,c,k,n.txns[t].snapshot.ts)
    } else { n.txns[t].snapshot.data[k] }
}
pub open spec fn can_operate(n: LShard,t: int) -> bool { n.txns[t].snapshot.active && !n.txns[t].snapshot.prepared && !n.txns[t].snapshot.aborted }
pub open spec fn storage_can_start(n: LShard,t: int) -> bool { !n.txns[t].snapshot.active && !n.txns[t].snapshot.committed && !n.txns[t].snapshot.aborted && forall |i: int| 0 <= i < n.log.len() ==> (#[trigger] n.log[i]).txn != t }
pub open spec fn storage_can_commit(n: LShard,c: Constants,t: int,ts: int,prepared: bool) -> bool {
    ts > 0 && n.txns[t].snapshot.active && !n.txns[t].snapshot.aborted && n.txns[t].snapshot.prepared == prepared
    && if prepared { ts >= n.txns[t].snapshot.prepare_ts } else {
        let q=active_read_ts(n,c).union(log_ts(n)); q.is_empty() || ts > maximum(q)
    }
}
pub open spec fn storage_can_prepare(n: LShard,c: Constants,t: int,ts: int) -> bool { ts > 0 && can_operate(n,t) && ts > maximum(active_read_ts(n,c)) }
pub open spec fn replace_shard(s: LState,i: int,n: LShard) -> LState { LState { shards: s.shards.insert(i,n),..s } }
pub open spec fn replace_txn(s: LState,i: int,t: int,x: Transaction) -> LState { replace_shard(s,i,LShard { txns: s.shards[i].txns.insert(t,x),..s.shards[i] }) }
pub open spec fn replace_router(s: LState,r: int,t: int,x: RTransaction) -> LState { LState { routers: s.routers.insert(r,s.routers[r].insert(t,x)),..s } }
pub open spec fn participant_shards(q: Seq<Participant>) -> Seq<int> { Seq::new(q.len(),|k: int| q[k].shard) }
pub open spec fn update_participants(q: Seq<Participant>,i: int,op: Kind) -> Seq<Participant> {
    if participant_shards(q).contains(i) { Seq::new(q.len(),|k: int| if q[k].shard == i { Participant { kinds: q[k].kinds.insert(op),..q[k] } } else { q[k] }) }
    else { q.push(Participant { shard: i,kinds: set![op] }) }
}
pub open spec fn any_aborted(s: LState,c: Constants,t: int) -> bool { exists |i: int| #![trigger c.shards.contains(i)] c.shards.contains(i) && s.shards[i].txns[t].aborted }
pub open spec fn commit_messages(q: Seq<int>,t: int,ts: int) -> Set<Commit> { q.to_set().map(|i: int| Commit { shard: i,txn: t,ts }) }
pub enum Action { RouterStart { r: int,t: int,ts: int },RouterOp { r: int,i: int,t: int,k: int,op: Kind },
    RouterCoordinate { r: int,i: int,t: int },RouterReadOnly { r: int,i: int,t: int },RouterSingle { r: int,i: int,t: int },
    Start(int,int),Read(int,int,int),Write(int,int,int),Coordinate(int,int),RecvVote(int,Vote),Decide(int,int),Prepare(Prepare),Commit(Commit),Abort(int,int),Stutter }
#[verifier::opaque]
pub open spec fn enabled(s: LState,c: Constants,a: Action) -> bool {
    match a {
        Action::Stutter => true,
        Action::RouterStart { r,t,ts } => c.routers.contains(r) && c.txns.contains(t) && c.timestamps.contains(ts) && forall |other: int| #![trigger c.routers.contains(other)] c.routers.contains(other) ==> s.routers[other][t].read_ts == c.no_value,
        Action::RouterOp { r,i,t,k,op } => c.routers.contains(r) && c.shards.contains(i) && c.txns.contains(t) && c.keys.contains(k)
            && !any_aborted(s,c,t) && !s.routers[r][t].committing && s.routers[r][t].read_ts != c.no_value && s.catalog[k] == i && s.shards[i].txns[t].requests.len() == 0,
        Action::RouterCoordinate { r,i,t } => c.routers.contains(r) && c.shards.contains(i) && c.txns.contains(t) && s.shards[i].txns[t].requests.len() == 0
            && s.routers[r][t].participants.len() > 1 && !s.routers[r][t].committing && !any_aborted(s,c,t) && s.routers[r][t].participants[0].shard == i,
        Action::RouterReadOnly { r,i,t } => c.routers.contains(r) && c.shards.contains(i) && c.txns.contains(t) && s.routers[r][t].participants.len() > 1
            && (forall |k: int| 0 <= k < s.routers[r][t].participants.len() ==> (#[trigger] s.routers[r][t].participants[k]).kinds == set![Kind::Read])
            && s.shards[i].txns[t].requests.len() == 0 && !s.routers[r][t].committing && !s.shards[i].txns[t].aborted,
        Action::RouterSingle { r,i,t } => c.routers.contains(r) && c.shards.contains(i) && c.txns.contains(t) && s.routers[r][t].participants.len() == 1
            && s.routers[r][t].participants[0].shard == i && s.shards[i].txns[t].requests.len() == 0 && !s.shards[i].txns[t].aborted && !s.routers[r][t].committing,
        Action::Start(i,t) => c.shards.contains(i) && c.txns.contains(t) && s.shards[i].txns[t].requests.len() > 0 && !s.shards[i].active.contains(t) && storage_can_start(s.shards[i],t)
            && match s.shards[i].txns[t].requests[0] { Request::Op { start,.. } => start,_ => false },
        Action::Read(i,t,k) | Action::Write(i,t,k) => c.shards.contains(i) && c.txns.contains(t) && c.keys.contains(k)
            && s.shards[i].active.contains(t) && !s.shards[i].prepared.contains(t) && s.shards[i].txns[t].requests.len() > 0 && can_operate(s.shards[i],t)
            && match s.shards[i].txns[t].requests[0] { Request::Op { key,kind,.. } => key == k && if a is Read { kind == Kind::Read && !prepare_conflict(s.shards[i],c,t,k) && (txn_read(s.shards[i],c,t,k) == c.no_value || c.txns.contains(txn_read(s.shards[i],c,t,k))) } else { kind == Kind::Write },_ => false },
        Action::Coordinate(i,t) => !c.keys.is_empty() && c.shards.contains(i) && c.txns.contains(t) && s.shards[i].active.contains(t) && s.shards[i].txns[t].requests.len() > 0
            && s.shards[i].txns[t].requests[0] is Coordinate && s.shards[i].txns[t].coordinator,
        Action::RecvVote(i,m) => !c.keys.is_empty() && c.shards.contains(i) && c.shards.contains(m.shard) && c.txns.contains(m.txn)
            && s.shards[i].active.contains(m.txn) && s.shards[i].txns[m.txn].coordinator && s.shards[i].txns[m.txn].committing && s.votes.contains(m),
        Action::Decide(i,t) => !c.keys.is_empty() && c.shards.contains(i) && c.txns.contains(t) && s.shards[i].active.contains(t) && s.shards[i].txns[t].coordinator
            && s.shards[i].txns[t].votes.map(|v: (int,int)| v.0) == s.shards[i].txns[t].participants.to_set(),
        Action::Prepare(m) => !c.keys.is_empty() && c.shards.contains(m.shard) && c.txns.contains(m.txn) && s.prepares.contains(m) && s.shards[m.shard].active.contains(m.txn)
            && !s.shards[m.shard].prepared.contains(m.txn) && !s.shards[m.shard].txns[m.txn].aborted && storage_can_prepare(s.shards[m.shard],c,m.txn,next_ts(s.shards[m.shard],c)),
        Action::Commit(m) => !c.keys.is_empty() && c.shards.contains(m.shard) && c.txns.contains(m.txn) && s.commits.contains(m) && s.shards[m.shard].active.contains(m.txn)
            && storage_can_commit(s.shards[m.shard],c,m.txn,if m.ts == c.no_value { next_ts(s.shards[m.shard],c) } else { m.ts },m.ts != c.no_value),
        Action::Abort(i,t) => !c.keys.is_empty() && c.shards.contains(i) && c.txns.contains(t) && s.shards[i].active.contains(t) && s.shards[i].txns[t].snapshot.active,
    }
}
#[verifier::opaque]
pub open spec fn apply(s: LState,c: Constants,a: Action) -> LState {
    match a {
        Action::Stutter => s,
        Action::RouterStart { r,t,ts } => replace_router(s,r,t,RTransaction { read_ts: ts,..s.routers[r][t] }),
        Action::RouterOp { r,i,t,k,op } => {
            let rtx=s.routers[r][t]; let x=s.shards[i].txns[t];
            let req=Request::Op { key: k,kind: op,shard: i,coordinator: rtx.count == 0,start: !participant_shards(rtx.participants).contains(i),read_ts: rtx.read_ts };
            replace_txn(replace_router(s,r,t,RTransaction { count: rtx.count+1,participants: update_participants(rtx.participants,i,op),..rtx }),i,t,Transaction { requests: x.requests.push(req),..x })
        },
        Action::RouterCoordinate { r,i,t } => {
            let x=s.shards[i].txns[t]; let q=participant_shards(s.routers[r][t].participants);
            replace_txn(replace_router(s,r,t,RTransaction { committing: true,..s.routers[r][t] }),i,t,Transaction { requests: x.requests.push(Request::Coordinate { shard: i,participants: q }),..x })
        },
        Action::RouterReadOnly { r,i,t } | Action::RouterSingle { r,i,t } => {
            let q=if a is RouterSingle { seq![i] } else { participant_shards(s.routers[r][t].participants) };
            LState { commits: s.commits.union(commit_messages(q,t,c.no_value)),..replace_router(s,r,t,RTransaction { committing: true,..s.routers[r][t] }) }
        },
        Action::Start(i,t) => match s.shards[i].txns[t].requests[0] { Request::Op { coordinator,read_ts,.. } => {
            let n=s.shards[i]; let x=n.txns[t]; let x2=Transaction { coordinator,participants: seq![i],committing: false,snapshot: new_snapshot(n,c,read_ts),status: Status::Ok,..x };
            let n2=LShard { active: n.active.insert(t),txns: n.txns.insert(t,x2),..n };
            replace_shard(s,i,LShard { durable: all_durable(n2,c),..n2 })
        }, _ => s },
        Action::Read(i,t,k) => {
            let x=s.shards[i].txns[t]; let v=txn_read(s.shards[i],c,t,k);
            replace_txn(s,i,t,Transaction { requests: x.requests.drop_first(),ops: x.ops.push(Operation { kind: Kind::Read,key: k,value: v }),
                status: if v == c.no_value { Status::NotFound } else { Status::Ok },snapshot: if v == c.no_value { x.snapshot } else { Snapshot { reads: x.snapshot.reads.insert(k),..x.snapshot } },..x })
        },
        Action::Write(i,t,k) => {
            let x=s.shards[i].txns[t]; let conflict=write_conflict(s.shards[i],c,t,k);
            replace_txn(s,i,t,Transaction { requests: x.requests.drop_first(),ops: x.ops.push(Operation { kind: Kind::Write,key: k,value: t }),status: if conflict { Status::Rollback } else { Status::Ok },
                snapshot: if conflict { Snapshot { aborted: true,..x.snapshot } } else { Snapshot { writes: x.snapshot.writes.insert(k),data: x.snapshot.data.insert(k,t),..x.snapshot } },..x })
        },
        Action::Coordinate(i,t) => match s.shards[i].txns[t].requests[0] { Request::Coordinate { participants,.. } => {
            let x=s.shards[i].txns[t]; let u=replace_txn(s,i,t,Transaction { coordinator: true,participants,committing: true,votes: Set::empty(),requests: x.requests.drop_first(),..x });
            LState { prepares: s.prepares.union(participants.to_set().map(|p: int| Prepare { shard: p,txn: t,coordinator: i })),..u }
        }, _ => s },
        Action::RecvVote(i,m) => {
            let x=s.shards[i].txns[m.txn]; LState { votes: s.votes.remove(m),..replace_txn(s,i,m.txn,Transaction { votes: x.votes.insert((m.shard,m.ts)),..x }) }
        },
        Action::Decide(i,t) => {
            let x=s.shards[i].txns[t]; let ts=maximum(x.votes.map(|v: (int,int)| v.1).to_iset());
            LState { commits: s.commits.union(commit_messages(x.participants,t,ts)),..s }
        },
        Action::Prepare(m) => {
            let n=s.shards[m.shard]; let x=n.txns[m.txn]; let ts=next_ts(n,c);
            let n2=LShard { prepared: n.prepared.insert(m.txn),log: n.log.push(LogEntry { txn: m.txn,ts,prepare: true,data: IMap::empty(),durable: None }),
                txns: n.txns.insert(m.txn,Transaction { snapshot: Snapshot { prepared: true,prepare_ts: ts,..x.snapshot },status: Status::Ok,..x }),..n };
            LState { votes: s.votes.insert(Vote { shard: m.shard,txn: m.txn,to: m.coordinator,ts }),..replace_shard(s,m.shard,n2) }
        },
        Action::Commit(m) => {
            let n=s.shards[m.shard]; let x=n.txns[m.txn]; let ts=if m.ts == c.no_value { next_ts(n,c) } else { m.ts };
            let data=IMap::new(|k: int| c.keys.contains(k) && x.snapshot.active && x.snapshot.writes.contains(k),|k: int| x.snapshot.data[k]);
            let log=n.log.push(LogEntry { txn: m.txn,ts,prepare: false,data,durable: if m.ts == c.no_value { None } else { Some(ts) } });
            let n2=LShard { active: n.active.remove(m.txn),prepared: n.prepared.remove(m.txn),log,
                txns: n.txns.insert(m.txn,Transaction { requests: Seq::empty(),snapshot: Snapshot { active: false,committed: true,..x.snapshot },status: Status::Ok,..x }),..n };
            let u=replace_shard(s,m.shard,LShard { durable: all_durable(n2,c),..n2 });
            LState { commits: s.commits.remove(m),ops: s.ops.insert(m.txn,s.ops[m.txn]+x.ops),..u }
        },
        Action::Abort(i,t) => {
            let n=s.shards[i]; let x=n.txns[t]; replace_shard(s,i,LShard { active: n.active.remove(t),
                txns: n.txns.insert(t,Transaction { aborted: true,ops: Seq::empty(),requests: Seq::empty(),snapshot: Snapshot { active: false,aborted: true,..x.snapshot },status: Status::Ok,..x }),..n })
        },
    }
}
#[verifier::opaque]
pub open spec fn next(s: LState,u: LState,c: Constants) -> bool { exists |a: Action| #[trigger] enabled(s,c,a) && u == apply(s,c,a) }
pub open spec fn single_writes(ops: Seq<Operation>) -> bool {
    forall |i: int,j: int| 0 <= i < ops.len() && 0 <= j < ops.len() && (#[trigger] ops[i]).kind == Kind::Write && (#[trigger] ops[j]).kind == Kind::Write && ops[i].key == ops[j].key ==> i == j
}
pub open spec fn single_write_per_key(s: LState,c: Constants) -> bool { forall |t: int| c.txns.contains(t) ==> #[trigger] single_writes(s.ops[t]) }
pub open spec fn write_keys(ops: Seq<Operation>) -> Set<int> { ops.to_set().filter(|o: Operation| o.kind == Kind::Write).map(|o: Operation| o.key) }
pub open spec fn effects(initial: IMap<int,int>,ops: Seq<Operation>) -> IMap<int,int>
    decreases ops.len()
{
    if ops.len() == 0 { initial } else {
        let prev=effects(initial,ops.drop_last()); let op=ops.last();
        if op.kind == Kind::Write { prev.insert(op.key,op.value) } else { prev }
    }
}
pub open spec fn execution(s: LState,c: Constants,order: Seq<int>) -> IMap<int,int>
    decreases order.len()
{
    if order.len() == 0 { IMap::new(|k: int| c.keys.contains(k),|k: int| c.no_value) }
    else { effects(execution(s,c,order.drop_last()),s.ops[order.last()]) }
}
pub open spec fn complete(snapshot: IMap<int,int>,ops: Seq<Operation>) -> bool {
    forall |i: int| 0 <= i < ops.len() && (#[trigger] ops[i]).kind == Kind::Read ==> ops[i].value == effects(snapshot,ops.take(i))[ops[i].key]
}
pub open spec fn no_conflict(s: LState,order: Seq<int>,position: int,cut: int) -> bool {
    forall |j: int| cut <= j < position ==> #[trigger] write_keys(s.ops[order[j]]).disjoint(write_keys(s.ops[order[position]]))
}
pub open spec fn snapshot_at(s: LState,c: Constants,order: Seq<int>,position: int,cut: int) -> bool {
    0 <= cut <= position && complete(execution(s,c,order.take(cut)),s.ops[order[position]]) && no_conflict(s,order,position,cut)
}
pub open spec fn si_order(s: LState,c: Constants,order: Seq<int>) -> bool {
    order.no_duplicates() && order.to_set().to_iset() == c.txns.filter(|t: int| s.ops[t].len() > 0)
    && forall |j: int| 0 <= j < order.len() ==> #[trigger] has_snapshot(s,c,order,j)
}
pub open spec fn has_snapshot(s: LState,c: Constants,order: Seq<int>,j: int) -> bool { exists |cut: int| #[trigger] snapshot_at(s,c,order,j,cut) }
pub open spec fn well_formed_ops(s: LState,c: Constants) -> bool {
    s.ops.dom() == c.txns && forall |t: int,i: int| c.txns.contains(t) && 0 <= i < s.ops[t].len() ==>
        c.keys.contains((#[trigger] s.ops[t][i]).key) && (c.txns.contains(s.ops[t][i].value) || s.ops[t][i].value == c.no_value)
}
pub open spec fn snapshot_isolation(s: LState,c: Constants) -> bool {
    well_formed_ops(s,c) && exists |order: Seq<int>| #[trigger] si_order(s,c,order)
}
} // verus!
