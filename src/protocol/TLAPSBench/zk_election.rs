//! FastLeaderElection dependency of the low-level ZooKeeper benchmark.
use vstd::prelude::*;
use super::zab::{Constants,Role,Txn,Zxid,Commit,boot,zero,newer,quorum,channels,init_ack};
verus! {
pub struct Vote { pub leader: Option<int>,pub zxid: Zxid,pub epoch: int }
pub struct Received { pub vote: Vote,pub round: int,pub role: Role,pub version: int }
pub struct Notification { pub source: int,pub role: Role,pub round: int,pub vote: Vote }
pub struct LServer { pub role: Role,pub current: int,pub history: Seq<Txn>,pub processed: Commit,
    pub vote: Vote,pub clock: int,pub received: Map<int,Received>,pub outside: Map<int,Received>,
    pub queue: Seq<Option<Notification>>,pub waiting: bool,pub leading: Set<int> }
pub struct LState { pub nodes: Map<int,LServer>,pub msgs: Map<(int,int),Seq<Notification>> }
pub open spec fn ranks(q: Set<int>) -> Map<int,int>
    decreases q.len()
{
    if q.is_empty() { Map::empty() } else { let i=choose |i: int| q.contains(i); ranks(q.remove(i)).insert(i,q.len() as int) }
}
pub open spec fn id_greater(c: Constants,i: int,j: int) -> bool { ranks(c.servers)[i] > ranks(c.servers)[j] }
pub open spec fn vote_newer(c: Constants,a: Vote,b: Vote) -> bool {
    a.epoch > b.epoch || a.epoch == b.epoch && (newer(a.zxid,b.zxid) || a.zxid == b.zxid && id_greater(c,a.leader.unwrap(),b.leader.unwrap()))
}
pub open spec fn blank_vote() -> Vote { Vote { leader: None,zxid: zero(),epoch: 0 } }
pub open spec fn blank_received() -> Received { Received { vote: blank_vote(),round: 0,role: Role::Looking,version: 0 } }
pub open spec fn self_vote(n: LServer,i: int) -> Vote { Vote { leader: Some(i),zxid: n.processed.zxid,epoch: n.current } }
pub open spec fn latest(h: Seq<Txn>) -> Commit { Commit { index: h.len() as int,zxid: if h.len() == 0 { zero() } else { h.last().zxid } } }
pub open spec fn initial(c: Constants) -> LState {
    LState { nodes: Map::new(c.servers,|i: int| LServer { role: Role::Looking,current: 0,history: seq![Txn { zxid: boot(),value: 0,ack: c.servers,epoch: 0 }],processed: Commit { index: 1,zxid: boot() },
        vote: Vote { leader: Some(i),zxid: boot(),epoch: 0 },clock: 0,received: Map::new(c.servers,|j: int| blank_received()),outside: Map::new(c.servers,|j: int| blank_received()),queue: Seq::empty(),waiting: false,leading: Set::empty() }),
        msgs: Map::new(channels(c),|p: (int,int)| Seq::empty()) }
}
pub open spec fn replace(s: LState,i: int,n: LServer) -> LState { LState { nodes: s.nodes.insert(i,n),..s } }
pub open spec fn notification(n: LServer,i: int) -> Notification { Notification { source: i,role: n.role,round: n.clock,vote: n.vote } }
pub open spec fn broadcast(s: LState,i: int,m: Notification) -> LState {
    LState { msgs: Map::new(s.msgs.dom(),|p: (int,int)| if p.0 == i && p.1 != i { s.msgs[p].push(m) } else { s.msgs[p] }),..s }
}
pub open spec fn discard(s: LState,i: int,j: int) -> LState {
    LState { msgs: s.msgs.insert((i,j),if s.msgs[(i,j)].len() == 0 { Seq::empty() } else { s.msgs[(i,j)].drop_first() }),..s }
}
pub open spec fn reply(s: LState,i: int,j: int,m: Notification) -> LState {
    LState { msgs: s.msgs.insert((i,j),s.msgs[(i,j)].push(m)).insert((j,i),s.msgs[(j,i)].drop_first()),..s }
}
pub open spec fn reset(n: LServer,c: Constants,i: int,cluster: bool) -> LServer {
    LServer { role: Role::Looking,processed: latest(n.history),clock: n.clock+1,
        vote: Vote { leader: Some(i),zxid: latest(n.history).zxid,epoch: n.current },
        received: Map::new(c.servers,|j: int| blank_received()),outside: Map::new(c.servers,|j: int| blank_received()),
        queue: if cluster { seq![None] } else { Seq::empty() },waiting: false,leading: Set::empty(),..n }
}
pub open spec fn timeout(s: LState,c: Constants,i: int) -> LState {
    let n=reset(s.nodes[i],c,i,false); broadcast(replace(s,i,n),i,notification(n,i))
}
pub open spec fn put(q: Map<int,Received>,m: Notification) -> Map<int,Received> {
    if q[m.source].round <= m.round { q.insert(m.source,Received { vote: m.vote,round: m.round,role: m.role,version: if q[m.source].round < m.round { 1 } else { q[m.source].version+1 } }) } else { q }
}
pub open spec fn vote_set(c: Constants,source: int,q: Map<int,Received>,vote: Vote,round: int) -> Set<int> {
    c.servers.remove(source).filter(|j: int| q[j].vote == vote && q[j].round == round).insert(source)
}
pub open spec fn check_leader(n: LServer,i: int,q: Map<int,Received>,vote: Vote,round: int) -> bool {
    if vote.leader == Some(i) { round == n.clock } else { q[vote.leader.unwrap()].vote.leader != None && q[vote.leader.unwrap()].role == Role::Leading }
}
pub open spec fn leave(n: LServer,i: int,v: Vote,q: Set<int>,save_quorum: bool) -> LServer {
    LServer { role: if v.leader == Some(i) { Role::Leading } else { Role::Following },vote: v,leading: if save_quorum && v.leader == Some(i) { q } else { n.leading },..n }
}
pub open spec fn established(n: LServer,c: Constants,i: int,m: Notification) -> LServer {
    let received=put(n.received,m); let q1=vote_set(c,m.source,received,m.vote,m.round);
    let n1=LServer { received: if m.round == n.clock { received } else { n.received },..n };
    if m.round == n.clock && quorum(q1,c) && check_leader(n,i,received,m.vote,m.round) { leave(n1,i,m.vote,q1,true) }
    else {
        let outside=put(n.outside,m); let q2=vote_set(c,m.source,outside,m.vote,m.round); let n2=LServer { outside,..n1 };
        if quorum(q2,c) && check_leader(n,i,outside,m.vote,m.round) { LServer { clock: m.round,..leave(n2,i,m.vote,q2,true) } }
        else if m.role == Role::Leading && m.round == n.clock { leave(n2,i,m.vote,Set::empty(),false) } else { n2 }
    }
}
pub enum Action { Receive(int,int),Timeout(int),Handle(int),Wait(int) }
pub open spec fn enabled(s: LState,c: Constants,a: Action) -> bool {
    match a {
        Action::Receive(i,j) => c.servers.contains(i) && c.servers.contains(j) && s.msgs[(j,i)].len() > 0,
        Action::Timeout(i) => c.servers.contains(i) && s.nodes[i].role == Role::Looking && s.nodes[i].queue.len() == 0 && forall |j: int| #![trigger c.servers.contains(j)] c.servers.contains(j) ==> s.msgs[(j,i)].len() == 0,
        Action::Handle(i) => c.servers.contains(i) && s.nodes[i].role == Role::Looking && !s.nodes[i].waiting && s.nodes[i].queue.len() > 0,
        Action::Wait(i) => c.servers.contains(i) && s.nodes[i].role == Role::Looking && s.nodes[i].waiting,
    }
}
#[verifier::opaque]
pub open spec fn apply(s: LState,c: Constants,a: Action) -> LState {
    match a {
        Action::Receive(i,j) => {
            let n=s.nodes[i]; let m=s.msgs[(j,i)][0];
            let u=if n.role == Role::Looking { replace(s,i,LServer { queue: n.queue.filter(|m: Option<Notification>| m is Some).push(Some(m)),..n }) } else { s };
            if m.role == Role::Looking && (n.role != Role::Looking || m.round < n.clock) { reply(u,i,j,notification(n,i)) } else { discard(u,j,i) }
        },
        Action::Timeout(i) => replace(s,i,LServer { queue: s.nodes[i].queue.push(None),..s.nodes[i] }),
        Action::Handle(i) => {
            let n=s.nodes[i]; let u=match n.queue[0] {
                None => broadcast(s,i,notification(n,i)),
                Some(m) => if m.role != Role::Looking {
                    let n2=established(n,c,i,m);
                    replace(s,i,LServer { history: if n2.role == Role::Leading { init_ack(n.history,i) } else { n.history },..n2 })
                } else if m.round < n.clock { s } else {
                    let candidate=if m.round > n.clock { self_vote(n,i) } else { n.vote };
                    let better=vote_newer(c,m.vote,candidate); let v=if better { m.vote } else { candidate };
                    let received=if m.round > n.clock { Map::new(c.servers,|j: int| if j == m.source { Received { vote: m.vote,round: m.round,role: Role::Looking,version: 1 } } else { blank_received() }) } else { put(n.received,m) };
                    let n2=LServer { vote: v,clock: m.round,received,waiting: n.waiting || quorum(vote_set(c,i,received,v,m.round),c),..n };
                    let u=replace(s,i,n2);
                    if m.round > n.clock || better { broadcast(u,i,notification(n2,i)) } else { u }
                },
            };
            replace(u,i,LServer { queue: n.queue.drop_first(),..u.nodes[i] })
        },
        Action::Wait(i) => {
            let n=s.nodes[i];
            if n.queue.len() > 0 && n.queue[0] is Some {
                let m=n.queue[0].unwrap(); let better=vote_newer(c,m.vote,n.vote);
                replace(s,i,LServer { queue: if better { n.queue.drop_first().push(Some(m)) } else { n.queue.drop_first() },waiting: if better { false } else { n.waiting },..n })
            } else {
                let n2=leave(n,i,n.vote,vote_set(c,i,n.received,n.vote,n.clock),true);
                replace(s,i,LServer { history: if n2.role == Role::Leading { init_ack(n.history,i) } else { n.history },..n2 })
            }
        },
    }
}
} // verus!
