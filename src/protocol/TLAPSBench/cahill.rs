//! Handwritten Cahill SSI state machine. Transaction/key domains may be infinite.
//! Cycles are represented by finite paths. No bounded model-checking parameter
//! limits histories, transactions, paths, or the number of keys.
use vstd::prelude::*;
verus! {
pub enum Reason { CommitConflict,Voluntary,FirstCommitter,ReadConflict,WriteConflict,Deadlock }
pub enum Op { Begin,Commit,Abort(Reason),Read { key: int,version: int },Write(int) }
pub struct Event { pub txn: int,pub op: Op }
pub struct LTxn { pub xlocks: Set<int>,pub waiting: Option<int>,pub incoming: bool,pub outgoing: bool,pub siread: Set<int> }
pub struct LState { pub history: Seq<Event>,pub txns: IMap<int,LTxn> }
pub struct Constants { pub txns: ISet<int>,pub keys: ISet<int> }
pub open spec fn valid_constants(c: Constants) -> bool { true }
pub open spec fn blank() -> LTxn { LTxn { xlocks: Set::empty(),waiting: None,incoming: false,outgoing: false,siread: Set::empty() } }
pub open spec fn initial(c: Constants) -> LState { LState { history: Seq::empty(),txns: IMap::new(|t: int| c.txns.contains(t),|t: int| blank()) } }
pub open spec fn all(h: Seq<Event>) -> Set<int> { h.to_set().map(|e: Event| e.txn) }
pub open spec fn committed(h: Seq<Event>) -> Set<int> { h.to_set().filter(|e: Event| e.op == Op::Commit).map(|e: Event| e.txn) }
pub open spec fn aborted(h: Seq<Event>) -> Set<int> { h.to_set().filter(|e: Event| e.op is Abort).map(|e: Event| e.txn) }
pub open spec fn active(h: Seq<Event>) -> Set<int> { all(h).difference(committed(h).union(aborted(h))) }
pub open spec fn position(h: Seq<Event>,e: Event) -> int {
    if h.contains(e) { choose |k: int| 1 <= k <= h.len() && #[trigger] h[k-1] == e } else { -1 }
}
pub open spec fn start(h: Seq<Event>,t: int) -> int { choose |k: int| 1 <= k <= h.len() && #[trigger] h[k-1] == Event { txn: t,op: Op::Begin } }
pub open spec fn keys(h: Seq<Event>,t: int,read: bool) -> Set<int> {
    h.to_set().filter(|e: Event| e.txn == t && if read { e.op is Read } else { e.op is Write }).map(|e: Event| match e.op { Op::Read { key,.. } => key,Op::Write(k) => k,_ => 0 })
}
pub open spec fn sub(h: Seq<Event>,first: int,last: int) -> Seq<Event> { Seq::new(if last < first { 0 } else { (last-first+1) as nat },|k: int| h[k+first-1]) }
pub open spec fn writers_since(s: LState,t: int,k: int) -> Set<int> {
    committed(sub(s.history,start(s.history,t),s.history.len() as int)).filter(|w: int| keys(s.history,w,false).contains(k))
}
pub open spec fn version(s: LState,t: int,k: int) -> Set<int> {
    let h=sub(s.history,1,start(s.history,t));
    let writes=h.filter(|e: Event| e.op == Op::Write(k) && committed(h).contains(e.txn));
    if s.txns[t].xlocks.contains(k) { set![t] } else if writes.len() == 0 { Set::empty() } else { set![writes.last().txn] }
}
pub open spec fn newer_versions(s: LState,t: int,k: int) -> Set<int> {
    let writes=s.history.filter(|e: Event| e.op == Op::Write(k));
    let v=choose |v: int| version(s,t,k).contains(v);
    let index=choose |i: int| 1 <= i <= writes.len() && #[trigger] writes[i-1] == Event { txn: v,op: Op::Write(k) };
    all(sub(writes,index+1,writes.len() as int))
}
pub open spec fn public(s: LState,t: int) -> bool { active(s.history).contains(t) && s.txns[t].waiting == None }
pub open spec fn locked(s: LState,c: Constants,k: int) -> bool { exists |t: int| c.txns.contains(t) && #[trigger] s.txns[t].xlocks.contains(k) }
pub open spec fn concurrent_readers(s: LState,c: Constants,t: int,k: int) -> ISet<int> {
    c.txns.filter(|r: int| r != t && s.txns[r].siread.contains(k) && (!committed(s.history).contains(r)
        || position(s.history,Event { txn: r,op: Op::Commit }) > position(s.history,Event { txn: t,op: Op::Begin })))
}
pub open spec fn abort(s: LState,t: int,reason: Reason) -> LState {
    LState { history: s.history.push(Event { txn: t,op: Op::Abort(reason) }),txns: s.txns.insert(t,blank()) }
}
pub open spec fn losers(s: LState,c: Constants,t: int) -> Set<int> {
    c.txns.filter(|r: int| s.txns[r].waiting is Some && s.txns[t].xlocks.contains(s.txns[r].waiting.unwrap())).to_set().unwrap()
}
pub open spec fn aborts(q: Set<int>) -> Seq<Event>
    decreases q.len()
{
    if q.is_empty() { Seq::empty() } else {
        let t=choose |t: int| q.contains(t);
        seq![Event { txn: t,op: Op::Abort(Reason::FirstCommitter) }] + aborts(q.remove(t))
    }
}
#[verifier::opaque]
pub open spec fn commit(s: LState,c: Constants,t: int) -> LState {
    if s.txns[t].incoming && s.txns[t].outgoing { abort(s,t,Reason::CommitConflict) } else {
        let q=losers(s,c,t);
        LState { history: s.history.push(Event { txn: t,op: Op::Commit })+aborts(q),txns: IMap::new(|r: int| c.txns.contains(r),|r: int|
            if q.contains(r) { blank() } else if r == t { LTxn { xlocks: Set::empty(),..s.txns[r] } } else { s.txns[r] }) }
    }
}
#[verifier::opaque]
pub open spec fn read(s: LState,c: Constants,t: int,k: int) -> LState {
    let newer=newer_versions(s,t,k);
    if exists |w: int| #![trigger newer.contains(w)] newer.contains(w) && committed(s.history).contains(w) && s.txns[w].outgoing { abort(s,t,Reason::ReadConflict) } else {
        let v=choose |v: int| version(s,t,k).contains(v);
        let others=c.txns.filter(|w: int| w != t && s.txns[w].xlocks.contains(k));
        LState { history: s.history.push(Event { txn: t,op: Op::Read { key: k,version: v } }),txns: IMap::new(|r: int| c.txns.contains(r),|r: int|
            LTxn { incoming: s.txns[r].incoming || newer.contains(r) || others.contains(r),
                outgoing: s.txns[r].outgoing || r == t && (!newer.is_empty() || !others.is_empty()),
                siread: if r == t { s.txns[r].siread.insert(k) } else { s.txns[r].siread },..s.txns[r] }) }
    }
}
#[verifier::opaque]
pub open spec fn acquire(s: LState,c: Constants,t: int,k: int) -> LState {
    let readers=concurrent_readers(s,c,t,k);
    if exists |r: int| #![trigger readers.contains(r)] readers.contains(r) && (committed(s.history).contains(r) || s.txns[r].incoming) { abort(s,t,Reason::WriteConflict) } else {
        LState { history: s.history.push(Event { txn: t,op: Op::Write(k) }),txns: IMap::new(|r: int| c.txns.contains(r),|r: int|
            LTxn { xlocks: if r == t { s.txns[r].xlocks.insert(k) } else { s.txns[r].xlocks },waiting: if r == t { None } else { s.txns[r].waiting },
                incoming: s.txns[r].incoming || r == t && !readers.is_empty(),outgoing: s.txns[r].outgoing || readers.contains(r),..s.txns[r] }) }
    }
}
pub open spec fn owner(s: LState,k: int) -> Option<int> {
    let q=active(s.history).filter(|r: int| s.txns[r].xlocks.contains(k));
    if q.is_empty() { None } else { Some(choose |r: int| q.contains(r)) }
}
pub open spec fn wait_edge(s: LState,c: Constants,t: int,k: int,from: int,to: int) -> bool {
    let waiting=if from == t { Some(k) } else { s.txns[from].waiting };
    active(s.history).contains(from) && active(s.history).contains(to) && waiting is Some && c.keys.contains(waiting.unwrap()) && owner(s,waiting.unwrap()) == Some(to)
}
pub open spec fn deadlock_path(s: LState,c: Constants,t: int,k: int,p: Seq<int>) -> bool {
    p.len() > 0 && p[0] == t && p.no_duplicates()
    && (forall |i: int| 0 <= i < p.len()-1 ==> #[trigger] wait_edge(s,c,t,k,p[i],p[i+1]))
    && wait_edge(s,c,t,k,p.last(),t)
}
pub open spec fn deadlocked(s: LState,c: Constants,t: int,k: int) -> bool { exists |p: Seq<int>| #[trigger] deadlock_path(s,c,t,k,p) }
pub open spec fn deadlock_victim(s: LState,c: Constants,t: int,k: int,v: int) -> bool {
    let p=choose |p: Seq<int>| deadlock_path(s,c,t,k,p);
    p.contains(v)
}
pub enum Action { Begin(int),Commit(int),Abort(int),Read(int,int),Write { txn: int,key: int,victim: int },Finish(int),Stutter }
#[verifier::opaque]
pub open spec fn enabled(s: LState,c: Constants,a: Action) -> bool {
    match a {
        Action::Stutter => true,
        Action::Begin(t) => c.txns.contains(t) && !all(s.history).contains(t),
        Action::Commit(t) | Action::Abort(t) => c.txns.contains(t) && public(s,t),
        Action::Read(t,k) => c.txns.contains(t) && c.keys.contains(k) && public(s,t) && !keys(s.history,t,true).contains(k) && !version(s,t,k).is_empty(),
        Action::Write { txn: t,key: k,victim: v } => c.txns.contains(t) && c.keys.contains(k) && public(s,t) && !s.txns[t].xlocks.contains(k)
            && (writers_since(s,t,k).is_empty() && locked(s,c,k) && deadlocked(s,c,t,k) ==> deadlock_victim(s,c,t,k,v)),
        Action::Finish(t) => c.txns.contains(t) && s.txns[t].waiting is Some && !locked(s,c,s.txns[t].waiting.unwrap()),
    }
}
#[verifier::opaque]
pub open spec fn apply(s: LState,c: Constants,a: Action) -> LState {
    match a {
        Action::Stutter => s,
        Action::Begin(t) => LState { history: s.history.push(Event { txn: t,op: Op::Begin }),..s },
        Action::Commit(t) => commit(s,c,t),
        Action::Abort(t) => abort(s,t,Reason::Voluntary),
        Action::Read(t,k) => read(s,c,t,k),
        Action::Finish(t) => acquire(s,c,t,s.txns[t].waiting.unwrap()),
        Action::Write { txn: t,key: k,victim: v } => {
            if !writers_since(s,t,k).is_empty() {
                let u=abort(s,t,Reason::FirstCommitter);
                LState { txns: u.txns.insert(t,LTxn { waiting: s.txns[t].waiting,..u.txns[t] }),..u }
            } else if !locked(s,c,k) { acquire(s,c,t,k) }
            else if !deadlocked(s,c,t,k) { LState { txns: s.txns.insert(t,LTxn { waiting: Some(k),..s.txns[t] }),..s } }
            else {
                let u=abort(s,v,Reason::Deadlock);
                if v == t { LState { txns: u.txns.insert(t,LTxn { waiting: s.txns[t].waiting,..u.txns[t] }),..u } }
                else { LState { txns: u.txns.insert(t,LTxn { waiting: Some(k),..u.txns[t] }),..u } }
            }
        },
    }
}
#[verifier::opaque]
pub open spec fn next(s: LState,u: LState,c: Constants) -> bool { exists |a: Action| #[trigger] enabled(s,c,a) && u == apply(s,c,a) }
pub open spec fn dependency(h: Seq<Event>,c: Constants,a: int,b: int) -> bool {
    let ch=h.filter(|e: Event| committed(h).contains(e.txn));
    committed(h).contains(a) && committed(h).contains(b) && a != b && exists |k: int| c.keys.contains(k) && {
        let aw=position(ch,Event { txn: a,op: Op::Write(k) }); let bw=position(ch,Event { txn: b,op: Op::Write(k) });
        aw != -1 && bw != -1 && aw < bw
        || aw != -1 && keys(ch,b,true).contains(k) && position(ch,Event { txn: a,op: Op::Commit }) < position(ch,Event { txn: b,op: Op::Begin })
        || keys(h,a,true).contains(k) && bw != -1 && position(ch,Event { txn: a,op: Op::Begin }) < position(ch,Event { txn: b,op: Op::Commit })
    }
}
pub open spec fn cycle(h: Seq<Event>,c: Constants,p: Seq<int>) -> bool {
    p.len() > 1 && p[0] == p.last() && forall |i: int| 0 <= i < p.len()-1 ==> #[trigger] dependency(h,c,p[i],p[i+1])
}
pub open spec fn serializable(s: LState,c: Constants) -> bool { forall |p: Seq<int>| !#[trigger] cycle(s.history,c,p) }
} // verus!
