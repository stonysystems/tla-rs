//! Handwritten low-level ZooKeeper 3.7.0 benchmark with FastLeaderElection.
//! Server identifiers use integers. See the documented CleanInputBuffer({i})
//! source anomaly in the disconnected-follower crash branch.
use vstd::prelude::*;
use super::zab::{self as z,Role,Phase,Txn,Zxid,Commit,AL,Proposal,boot,zero,newer,index,next_zxid};
use super::zk_election as fle;
pub use super::zab::Constants;
verus! {
pub enum Mode { None,Diff,Trunc,Snap }
pub struct Electing { pub sid: int,pub zxid: Zxid,pub quorum: bool }
pub struct LServer { pub phase: Phase,pub accepted: int,pub committed: Commit,pub snapshot: Commit,pub initial: Seq<Txn>,
    pub learners: Set<int>,pub connecting: Set<AL>,pub electing: Set<Electing>,pub ackld: Set<AL>,pub forwarding: Set<int>,pub max_epoch: int,
    pub leader: Option<int>,pub mode: Mode,pub received_leader: bool,pub pending: Seq<Txn>,pub commits: Seq<Zxid>,pub online: bool }
pub enum Message { FollowerInfo(Zxid),LeaderInfo(Zxid),AckEpoch(Zxid,int),Diff(Zxid),Trunc(Zxid),Snap(Zxid,Seq<Txn>),
    Proposal(Zxid,int),Commit(Zxid),NewLeader(Zxid),AckLd(Zxid),UpToDate(Zxid),Ack(Zxid) }
pub struct LState { pub election: fle::LState,pub nodes: Map<int,LServer>,pub msgs: Map<(int,int),Seq<Message>>,
    pub partition: Map<(int,int),bool>,pub epoch_leader: Map<int,Set<int>>,pub proposals: Set<Proposal> }
pub open spec fn valid_constants(c: Constants) -> bool { z::valid_constants(c) && c.request_value >= 0 }
pub open spec fn initial(c: Constants) -> LState {
    let zs=z::initial(c); LState { election: fle::initial(c),nodes: Map::new(c.servers,|i: int| LServer {
        phase: Phase::Election,accepted: 0,committed: Commit { index: 1,zxid: boot() },snapshot: Commit { index: 0,zxid: zero() },initial: zs.nodes[i].history,
        learners: Set::empty(),connecting: Set::empty(),electing: Set::empty(),ackld: Set::empty(),forwarding: Set::empty(),max_epoch: 0,
        leader: None,mode: Mode::None,received_leader: false,pending: Seq::empty(),commits: Seq::empty(),online: true }),
        msgs: Map::new(z::channels(c),|p: (int,int)| Seq::empty()),partition: Map::new(z::channels(c),|p: (int,int)| false),epoch_leader: zs.epoch_leader,proposals: zs.proposals }
}
pub open spec fn unset() -> Zxid { Zxid { epoch: -1,counter: -1 } }
pub open spec fn replace(s: LState,i: int,n: LServer) -> LState { LState { nodes: s.nodes.insert(i,n),..s } }
pub open spec fn replace_e(s: LState,i: int,n: fle::LServer) -> LState { LState { election: fle::replace(s.election,i,n),..s } }
pub open spec fn send(s: LState,i: int,j: int,q: Seq<Message>) -> LState { LState { msgs: s.msgs.insert((i,j),s.msgs[(i,j)]+q),..s } }
pub open spec fn reply(s: LState,i: int,j: int,q: Seq<Message>) -> LState {
    LState { msgs: s.msgs.insert((j,i),s.msgs[(j,i)].drop_first()).insert((i,j),s.msgs[(i,j)]+q),..s }
}
pub open spec fn discard(s: LState,i: int,j: int) -> LState {
    LState { msgs: s.msgs.insert((i,j),if s.msgs[(i,j)].len() == 0 { Seq::empty() } else { s.msgs[(i,j)].drop_first() }),..s }
}
pub open spec fn broadcast(s: LState,i: int,q: Set<int>,m: Message) -> LState {
    LState { msgs: Map::new(s.msgs.dom(),|p: (int,int)| if p.0 == i && p.1 != i && q.contains(p.1) { s.msgs[p].push(m) } else { s.msgs[p] }),..s }
}
pub open spec fn discard_broadcast(s: LState,i: int,j: int,q: Set<int>,m: Message) -> LState {
    let u=broadcast(s,i,q,m); if i == j { u } else { LState { msgs: u.msgs.insert((j,i),s.msgs[(j,i)].drop_first()),..u } }
}
pub open spec fn clean(s: LState,i: int,j: int) -> LState { LState { msgs: s.msgs.insert((i,j),Seq::empty()).insert((j,i),Seq::empty()),..s } }
pub open spec fn stopped(n: LServer) -> LServer { LServer { phase: Phase::Election,leader: None,mode: Mode::None,received_leader: false,..n } }
pub open spec fn shut_follower(s: LState,c: Constants,i: int) -> LState { LState { election: fle::timeout(s.election,c,i),..replace(s,i,stopped(s.nodes[i])) } }
pub open spec fn shut_leader(s: LState,c: Constants,i: int) -> LState {
    let q=s.nodes[i].learners.insert(i);
    let nodes=Map::new(c.servers,|j: int| if q.contains(j) { stopped(s.nodes[j]) } else { s.nodes[j] });
    LState { election: fle::LState { nodes: Map::new(c.servers,|j: int| if q.contains(j) { fle::reset(s.election.nodes[j],c,j,true) } else { s.election.nodes[j] }),..s.election },
        nodes: nodes.insert(i,LServer { learners: Set::empty(),forwarding: Set::empty(),..nodes[i] }),
        msgs: Map::new(z::channels(c),|p: (int,int)| if q.contains(p.1) { Seq::empty() } else { s.msgs[p] }),..s }
}
pub open spec fn disconnect_e(q: Set<Electing>,j: int) -> Set<Electing> {
    let old=choose |e: Electing| #![trigger q.contains(e)] q.contains(e) && e.sid == j;
    if exists |e: Electing| #![trigger q.contains(e)] q.contains(e) && e.sid == j { q.remove(old).insert(Electing { zxid: unset(),..old }) } else { q }
}
pub open spec fn update_e(q: Set<Electing>,j: int,zxid: Zxid,yes: bool) -> Set<Electing> {
    let old=choose |e: Electing| #![trigger q.contains(e)] q.contains(e) && e.sid == j;
    if exists |e: Electing| #![trigger q.contains(e)] q.contains(e) && e.sid == j { q.remove(old).insert(Electing { sid: j,zxid,quorum: yes || old.quorum }) }
    else { q.insert(Electing { sid: j,zxid,quorum: yes }) }
}
pub open spec fn remove_learner(s: LState,i: int,j: int) -> LState {
    let n=s.nodes[i]; replace(s,i,LServer { learners: n.learners.remove(j),forwarding: n.forwarding.remove(j),electing: disconnect_e(n.electing,j),connecting: z::disconnect_al(n.connecting,j),ackld: z::disconnect_al(n.ackld,j),..n })
}
pub open spec fn lose_follower(s: LState,c: Constants,i: int,j: int) -> LState {
    if z::quorum(s.nodes[i].learners.remove(j),c) { clean(shut_follower(remove_learner(s,i,j),c,j),i,j) } else { shut_leader(s,c,i) }
}
pub open spec fn formed(c: Constants,i: int,q: Set<int>) -> bool { q.contains(i) && z::quorum(q,c) }
pub open spec fn election_finished(s: LState,c: Constants,i: int) -> bool { formed(c,i,s.nodes[i].electing.filter(|e: Electing| e.quorum).map(|e: Electing| e.sid)) }
pub open spec fn after_election(s: LState,i: int) -> LState {
    let n=s.nodes[i]; let e=s.election.nodes[i];
    replace(s,i,match e.role {
        Role::Leading => LServer { phase: Phase::Discovery,learners: set![i],connecting: set![AL { sid: i,connected: true }],
            electing: set![Electing { sid: i,zxid: unset(),quorum: true }],ackld: set![AL { sid: i,connected: true }],forwarding: Set::empty(),initial: e.history,max_epoch: n.accepted+1,..n },
        Role::Following => LServer { phase: Phase::Discovery,initial: e.history,pending: Seq::empty(),commits: Seq::empty(),..n },
        Role::Looking => n,
    })
}
pub open spec fn sub(h: Seq<Txn>,first: int,end: int) -> Seq<Txn> { Seq::new(if end < first { 0 } else { (end-first+1) as nat },|k: int| h[k+first-1]) }
pub open spec fn ack_prefix(h: Seq<Txn>,end: int,j: int) -> Seq<Txn> { Seq::new(h.len(),|k: int| if k < end { Txn { ack: h[k].ack.insert(j),..h[k] } } else { h[k] }) }
pub open spec fn floor_index(h: Seq<Txn>,zxid: Zxid) -> int {
    let k=index(h,zxid); let q=Set::range(1,h.len() as int+1).filter(|k: int| newer(h[k-1].zxid,zxid));
    if h.len() == 0 { 0 } else if k <= h.len() { k } else if q.is_empty() { h.len() as int } else { (choose |k: int| q.contains(k) && forall |j: int| q.contains(j) ==> k <= j)-1 }
}
pub open spec fn packets(h: Seq<Txn>,cur: int,end: int,committed: int) -> Seq<Message>
    decreases if end >= cur { end-cur+1 } else { 0 }
{
    if end < cur { Seq::empty() } else {
        let p=Message::Proposal(h[end-1].zxid,h[end-1].value);
        packets(h,cur,end-1,committed)+if end <= committed { seq![p,Message::Commit(h[end-1].zxid)] } else { seq![p] }
    }
}
pub open spec fn sync_send(s: LState,i: int,j: int,zxid: Zxid,k: int,mode: Mode) -> LState {
    let n=s.nodes[i]; let e=s.election.nodes[i]; let end=e.history.len() as int;
    let committed=if n.phase == Phase::Broadcast { n.committed.index } else { end };
    let first=match mode { Mode::Diff => Message::Diff(zxid),Mode::Trunc => Message::Trunc(zxid),_ => Message::Snap(zxid,sub(e.history,1,k)) };
    let q=seq![first]+packets(e.history,k+1,end,committed)+seq![Message::NewLeader(Zxid { epoch: n.accepted,counter: 0 })];
    let ps=Set::range(k+1,end+1).map(|k: int| Proposal { source: i,epoch: n.accepted,zxid: e.history[k-1].zxid,value: e.history[k-1].value });
    let u=replace(s,i,LServer { forwarding: n.forwarding.insert(j),..n });
    let u=if mode == Mode::Snap { u } else { replace_e(u,i,fle::LServer { history: ack_prefix(e.history,k,j),..e }) };
    send(LState { proposals: s.proposals.union(ps),..u },i,j,q)
}
pub open spec fn sync_follower(s: LState,i: int,j: int,peer: Zxid) -> LState {
    let n=s.nodes[i]; let e=s.election.nodes[i]; let min=n.snapshot.index+1;
    let max=if n.phase == Phase::Broadcast { n.committed.index } else { e.history.len() as int };
    let lo=if min > max { e.processed.zxid } else { e.history[min-1].zxid };
    let hi=if min > max { e.processed.zxid } else if max == 0 { zero() } else { e.history[max-1].zxid };
    if peer == e.processed.zxid { sync_send(s,i,j,peer,e.processed.index,Mode::Diff) }
    else if newer(peer,hi) { sync_send(s,i,j,hi,max,Mode::Trunc) }
    else if !newer(lo,peer) {
        let k=index(e.history,peer); if min <= k <= e.history.len() { sync_send(s,i,j,peer,k,Mode::Diff) }
        else { let k=floor_index(e.history,peer); sync_send(s,i,j,if k == 0 { zero() } else { e.history[k-1].zxid },k,Mode::Trunc) }
    } else { sync_send(s,i,j,e.processed.zxid,max,Mode::Snap) }
}
pub open spec fn complete_history(s: LState,i: int) -> Seq<Txn> { s.election.nodes[i].history+s.nodes[i].pending }
pub open spec fn last_queued(s: LState,i: int) -> Commit {
    if s.election.nodes[i].role == Role::Following && s.nodes[i].phase == Phase::Synchronization { fle::latest(complete_history(s,i)) } else { fle::latest(s.election.nodes[i].history) }
}
pub open spec fn last_committed(s: LState,i: int) -> Commit {
    let n=s.nodes[i]; let e=s.election.nodes[i]; let initial=n.initial.len() as int;
    if n.phase == Phase::Broadcast { n.committed }
    else if e.role == Role::Leading { Commit { index: initial,zxid: if initial == 0 { zero() } else { e.history[initial-1].zxid } } }
    else if e.role == Role::Following {
        if n.commits.len() > 0 { Commit { index: index(complete_history(s,i),n.commits.last()),zxid: n.commits.last() } }
        else if e.history.len() == initial { fle::latest(e.history) }
        else if initial < n.committed.index { n.committed }
        else { Commit { index: initial,zxid: if initial == 0 { zero() } else { e.history[initial-1].zxid } } }
    } else { n.committed }
}
pub open spec fn transaction(s: LState,i: int,k: int) -> Txn {
    if s.election.nodes[i].role == Role::Following && s.nodes[i].phase == Phase::Synchronization { complete_history(s,i)[k-1] } else { s.election.nodes[i].history[k-1] }
}
pub open spec fn committed_txns(s: LState,i: int) -> Seq<Txn> {
    let n=s.nodes[i]; let e=s.election.nodes[i];
    if e.role != Role::Following || n.phase != Phase::Synchronization { sub(e.history,1,n.committed.index) }
    else if n.commits.len() == 0 { e.history } else { sub(complete_history(s,i),1,last_committed(s,i).index) }
}
pub open spec fn commits_match(h: Seq<Txn>,q: Seq<Zxid>) -> bool { q.len() == 0 || h.len() >= q.len() && forall |k: int| 0 <= k < q.len() ==> h[h.len()-q.len()+k].zxid == #[trigger] q[k] }
pub open spec fn take_snapshot(n: LServer) -> LServer { if n.snapshot.index <= n.committed.index { LServer { snapshot: n.committed,..n } } else { n } }
pub open spec fn maybe_snapshot(n: LServer) -> LServer { if n.committed.index-n.snapshot.index >= 2 { take_snapshot(n) } else { n } }
pub open spec fn ack_messages(q: Seq<Txn>) -> Seq<Message> { Seq::new(q.len(),|k: int| Message::Ack(q[k].zxid)) }
pub enum Action { Election(fle::Action),Partition(int,int),Recover(int,int),Crash(int),Start(int),Connect(int,int),
    FollowerInfo(int,int),LeaderInfo(int,int),AckEpoch(int,int),Sync(int,int),SyncMessage(int,int),ProposalSync(int,int),CommitSync(int,int),NewLeader(int,int),AckLd(int,int),UpToDate(int,int),Request(int),Proposal(int,int),Ack(int,int),Commit(int,int),Stutter }
pub open spec fn receiver(a: Action) -> int {
    match a { Action::Election(fle::Action::Receive(i,_)) | Action::Election(fle::Action::Timeout(i)) | Action::Election(fle::Action::Handle(i)) | Action::Election(fle::Action::Wait(i)) => i,
        Action::Partition(i,_) | Action::Recover(i,_) | Action::Crash(i) | Action::Start(i) | Action::Connect(i,_) | Action::FollowerInfo(i,_) | Action::LeaderInfo(i,_) | Action::AckEpoch(i,_) | Action::Sync(i,_) | Action::SyncMessage(i,_) | Action::ProposalSync(i,_) | Action::CommitSync(i,_) | Action::NewLeader(i,_) | Action::AckLd(i,_) | Action::UpToDate(i,_) | Action::Request(i) | Action::Proposal(i,_) | Action::Ack(i,_) | Action::Commit(i,_) => i,Action::Stutter => 0 }
}
#[verifier::opaque]
pub open spec fn enabled(s: LState,c: Constants,a: Action) -> bool {
    let i=receiver(a); let n=s.nodes[i]; let e=s.election.nodes[i];
    if a == Action::Stutter { true } else { c.servers.contains(i) && (a is Start || n.online) && match a {
        Action::Stutter => true,
        Action::Election(a) => fle::enabled(s.election,c,a),
        Action::Crash(_) => true,Action::Start(_) => !n.online,
        Action::Partition(_,j) => c.servers.contains(j) && j != i && s.nodes[j].online && !(s.partition[(i,j)] && s.partition[(j,i)])
            && (e.role == Role::Leading && n.learners.contains(j) && s.election.nodes[j].role == Role::Following && s.nodes[j].leader == Some(i)
                || e.role == Role::Looking && s.election.nodes[j].role == Role::Looking && fle::id_greater(c,i,j)),
        Action::Recover(_,j) => c.servers.contains(j) && s.nodes[j].online && fle::id_greater(c,i,j) && s.partition[(i,j)] && s.partition[(j,i)],
        Action::Connect(_,j) => c.servers.contains(j) && s.nodes[j].online && e.role == Role::Leading && !n.learners.contains(j) && s.election.nodes[j].role == Role::Following && s.nodes[j].leader == None && s.election.nodes[j].vote.leader == Some(i),
        Action::Request(_) => e.role == Role::Leading && n.phase == Phase::Broadcast && z::quorum(n.forwarding.filter(|j: int| s.nodes[j].phase == Phase::Broadcast).insert(i),c),
        Action::Sync(_,j) => c.servers.contains(j) && e.role == Role::Leading && election_finished(s,c,i) && exists |x: Electing| #![trigger n.electing.contains(x)] n.electing.contains(x) && x.sid == j && x.zxid != unset() && n.learners.contains(j),
        Action::FollowerInfo(_,j) | Action::AckEpoch(_,j) | Action::AckLd(_,j) | Action::Ack(_,j) => c.servers.contains(j) && e.role == Role::Leading && n.learners.contains(j) && s.msgs[(j,i)].len() > 0 && match a {
            Action::FollowerInfo(_,_) => s.msgs[(j,i)][0] is FollowerInfo,
            Action::AckEpoch(_,_) => match s.msgs[(j,i)][0] { Message::AckEpoch(_,epoch) => election_finished(s,c,i) || epoch >= -1,_ => false },
            Action::AckLd(_,_) => s.msgs[(j,i)][0] is AckLd,_ => s.msgs[(j,i)][0] is Ack,
        },
        Action::LeaderInfo(_,j) | Action::SyncMessage(_,j) | Action::ProposalSync(_,j) | Action::CommitSync(_,j) | Action::NewLeader(_,j) | Action::UpToDate(_,j) | Action::Proposal(_,j) | Action::Commit(_,j) =>
            c.servers.contains(j) && e.role == Role::Following && n.leader == Some(j) && s.msgs[(j,i)].len() > 0 && match a {
                Action::LeaderInfo(_,_) => s.msgs[(j,i)][0] is LeaderInfo,
                Action::SyncMessage(_,_) => s.msgs[(j,i)][0] is Diff || s.msgs[(j,i)][0] is Trunc || s.msgs[(j,i)][0] is Snap,
                Action::ProposalSync(_,_) => n.phase == Phase::Synchronization && s.msgs[(j,i)][0] is Proposal,
                Action::CommitSync(_,_) => n.phase == Phase::Synchronization && s.msgs[(j,i)][0] is Commit,
                Action::NewLeader(_,_) => s.msgs[(j,i)][0] is NewLeader,
                Action::UpToDate(_,_) => s.msgs[(j,i)][0] is UpToDate,
                Action::Proposal(_,_) => n.phase == Phase::Broadcast && s.msgs[(j,i)][0] is Proposal,
                _ => n.phase == Phase::Broadcast && s.msgs[(j,i)][0] is Commit,
            },
    } }
}
#[verifier::opaque]
pub open spec fn apply(s: LState,c: Constants,a: Action) -> LState {
    let i=receiver(a); let n=s.nodes[i]; let e=s.election.nodes[i];
    match a {
        Action::Stutter => s,
        Action::Election(a) => { let u=LState { election: fle::apply(s.election,c,a),..s }; if a is Handle || a is Wait { after_election(u,i) } else { u } },
        Action::Partition(_,j) => {
            let u=if e.role == Role::Leading { lose_follower(s,c,i,j) } else { s };
            LState { partition: s.partition.insert((i,j),true).insert((j,i),true),..u }
        },
        Action::Recover(_,j) => LState { partition: s.partition.insert((i,j),false).insert((j,i),false),..s },
        Action::Crash(_) => {
            let u=match e.role { Role::Looking => s,Role::Leading => shut_leader(s,c,i),Role::Following => match n.leader {
                Some(j) => lose_follower(s,c,j,i),
                // Source calls CleanInputBuffer({i}), whose scalar comparison
                // matches no integer server. Keep the protocol messages here.
                None => shut_follower(s,c,i),
            } };
            replace(u,i,LServer { online: false,..u.nodes[i] })
        },
        Action::Start(_) => replace_e(replace(s,i,LServer { online: true,committed: n.snapshot,..n }),i,fle::LServer { processed: fle::latest(e.history),..e }),
        Action::Connect(_,j) => send(replace(replace(s,i,LServer { learners: n.learners.insert(j),..n }),j,LServer { leader: Some(i),..s.nodes[j] }),j,i,seq![Message::FollowerInfo(Zxid { epoch: s.nodes[j].accepted,counter: 0 })]),
        Action::FollowerInfo(_,j) => match s.msgs[(j,i)][0] { Message::FollowerInfo(zxid) => {
            if formed(c,i,z::al_ids(n.connecting)) { reply(s,i,j,seq![Message::LeaderInfo(Zxid { epoch: n.accepted,counter: 0 })]) }
            else {
                let connecting=z::update_al(n.connecting,j); let epoch=if zxid.epoch >= n.max_epoch { zxid.epoch+1 } else { n.max_epoch };
                let first=formed(c,i,z::al_ids(connecting)); let u=replace(s,i,LServer { connecting,max_epoch: epoch,accepted: if first { epoch } else { n.accepted },..n });
                if first { discard_broadcast(u,i,j,z::al_connected(connecting).intersect(n.learners),Message::LeaderInfo(Zxid { epoch,counter: 0 })) } else { discard(u,j,i) }
            }
        }, _ => s },
        Action::LeaderInfo(_,j) => match s.msgs[(j,i)][0] { Message::LeaderInfo(zxid) => {
            if zxid.epoch < n.accepted { clean(remove_learner(shut_follower(s,c,i),j,i),i,j) }
            else if n.phase != Phase::Discovery { discard(s,j,i) }
            else { reply(replace(s,i,LServer { accepted: zxid.epoch,phase: Phase::Synchronization,..n }),i,j,seq![Message::AckEpoch(e.processed.zxid,if zxid.epoch > n.accepted { e.current } else { -1 })]) }
        }, _ => s },
        Action::AckEpoch(_,j) => match s.msgs[(j,i)][0] { Message::AckEpoch(zxid,epoch) => {
            let finished=election_finished(s,c,i); let log_ok=!(epoch > e.current || epoch == e.current && newer(zxid,e.processed.zxid));
            if !finished && epoch > -1 && !log_ok { shut_leader(s,c,i) }
            else {
                let electing=update_e(n.electing,j,zxid,!finished && epoch > -1 && log_ok); let u=replace(s,i,LServer { electing,..n });
                if !finished && epoch > -1 && election_finished(u,c,i) {
                    let u=replace_e(replace(u,i,LServer { phase: Phase::Synchronization,..u.nodes[i] }),i,fle::LServer { current: n.accepted,..e });
                    discard(LState { epoch_leader: if s.epoch_leader.dom().contains(n.accepted) { s.epoch_leader.insert(n.accepted,s.epoch_leader[n.accepted].insert(i)) } else { s.epoch_leader },..u },j,i)
                } else { discard(u,j,i) }
            }
        }, _ => s },
        Action::Sync(_,j) => {
            let chosen=choose |x: Electing| #![trigger n.electing.contains(x)] n.electing.contains(x) && x.sid == j && x.zxid != unset() && n.learners.contains(j);
            let u=sync_follower(s,i,j,chosen.zxid); replace(u,i,LServer { electing: n.electing.remove(chosen).insert(Electing { zxid: unset(),..chosen }),..u.nodes[i] })
        },
        Action::SyncMessage(_,j) => {
            let u=if n.phase != Phase::Synchronization { s } else { match s.msgs[(j,i)][0] {
                Message::Diff(_) => replace(s,i,LServer { mode: Mode::Diff,..n }),
                Message::Trunc(zxid) => {
                    let k=index(e.history,zxid); let u=replace(s,i,LServer { mode: Mode::Trunc,..n });
                    if n.committed.index <= k <= e.history.len() {
                        let h=sub(e.history,1,k); let at=Commit { index: k,zxid };
                        replace_e(replace(u,i,LServer { initial: h,committed: at,..u.nodes[i] }),i,fle::LServer { history: h,processed: at,..e })
                    } else { u }
                },
                Message::Snap(zxid,h) => {
                    let at=Commit { index: h.len() as int,zxid };
                    replace_e(replace(s,i,LServer { mode: Mode::Snap,initial: h,committed: at,..n }),i,fle::LServer { history: h,processed: at,..e })
                }, _ => s,
            } }; discard(u,j,i)
        },
        Action::ProposalSync(_,j) => match s.msgs[(j,i)][0] { Message::Proposal(zxid,value) => {
            discard(if next_zxid(last_queued(s,i).zxid,zxid) { replace(s,i,LServer { pending: n.pending.push(Txn { zxid,value,ack: Set::empty(),epoch: n.accepted }),..n }) } else { s },j,i)
        }, _ => s },
        Action::CommitSync(_,j) => match s.msgs[(j,i)][0] { Message::Commit(zxid) => {
            let k=last_committed(s,i).index+1;
            let u=if k <= last_queued(s,i).index && next_zxid(last_committed(s,i).zxid,zxid) && zxid == transaction(s,i,k).zxid {
                if n.mode == Mode::Diff || n.received_leader { replace(s,i,LServer { commits: n.commits.push(zxid),..n }) }
                else { let h=e.history.push(n.pending[0]); let at=fle::latest(h);
                    replace_e(replace(s,i,LServer { committed: at,pending: n.pending.drop_first(),..n }),i,fle::LServer { history: h,processed: at,..e }) }
            } else { s }; discard(u,j,i)
        }, _ => s },
        Action::NewLeader(_,j) => match s.msgs[(j,i)][0] { Message::NewLeader(zxid) => {
            let sn=if n.mode == Mode::Trunc || n.mode == Mode::Snap { take_snapshot(n) } else { n };
            let u=replace_e(replace(s,i,LServer { mode: Mode::None,received_leader: true,pending: Seq::empty(),..sn }),i,fle::LServer { current: n.accepted,history: e.history+n.pending,..e });
            reply(u,i,j,seq![Message::AckLd(zxid)]+ack_messages(n.pending))
        }, _ => s },
        Action::AckLd(_,j) => match s.msgs[(j,i)][0] { Message::AckLd(zxid) => {
            let leader_zxid=Zxid { epoch: n.accepted,counter: 0 }; let m=Message::UpToDate(leader_zxid);
            if formed(c,i,z::al_ids(n.ackld)) { reply(s,i,j,seq![m]) }
            else if zxid != leader_zxid { discard(s,j,i) }
            else {
                let ackld=z::update_al(n.ackld,j); let u=replace(s,i,LServer { ackld,..n });
                if formed(c,i,z::al_ids(ackld)) {
                    let at=fle::latest(e.history);
                    let u=replace_e(replace(u,i,LServer { phase: Phase::Broadcast,committed: at,snapshot: at,..u.nodes[i] }),i,fle::LServer { processed: at,vote: fle::Vote { epoch: n.accepted,..e.vote },..e });
                    discard_broadcast(u,i,j,z::al_connected(ackld).intersect(n.learners),m)
                } else { discard(u,j,i) }
            }
        }, _ => s },
        Action::UpToDate(_,j) => {
            let matched=commits_match(committed_txns(s,i),n.commits); let at=last_committed(s,i);
            let u=replace_e(replace(s,i,LServer { phase: Phase::Broadcast,pending: Seq::empty(),commits: Seq::empty(),committed: if matched { at } else { n.committed },..n }),i,
                fle::LServer { history: e.history+n.pending,processed: if matched { at } else { e.processed },vote: fle::Vote { epoch: n.accepted,..e.vote },..e });
            reply(u,i,j,ack_messages(n.pending))
        },
        Action::Request(_) => {
            let old=fle::latest(e.history).zxid; let zxid=Zxid { epoch: e.current,counter: if old.epoch == e.current { old.counter+1 } else { 1 } };
            let u=replace_e(replace(s,i,maybe_snapshot(n)),i,fle::LServer { history: e.history.push(Txn { zxid,value: c.request_value,ack: set![i],epoch: n.accepted }),..e });
            broadcast(LState { proposals: s.proposals.insert(Proposal { source: i,epoch: n.accepted,zxid,value: c.request_value }),..u },i,n.forwarding,Message::Proposal(zxid,c.request_value))
        },
        Action::Proposal(_,j) => match s.msgs[(j,i)][0] { Message::Proposal(zxid,value) => {
            if next_zxid(last_queued(s,i).zxid,zxid) {
                let u=replace_e(replace(s,i,maybe_snapshot(n)),i,fle::LServer { history: e.history.push(Txn { zxid,value,ack: Set::empty(),epoch: n.accepted }),..e });
                reply(u,i,j,seq![Message::Ack(zxid)])
            } else { s }
        }, _ => s },
        Action::Ack(_,j) => match s.msgs[(j,i)][0] { Message::Ack(zxid) => {
            let k=index(e.history,zxid); let previous=z::maximum(Set::range(1,e.history.len() as int+1).filter(|k: int| e.history[k-1].ack.contains(j)));
            if 1 <= k <= e.history.len() && (previous == -1 || previous+1 == k) {
                let txn=Txn { ack: e.history[k-1].ack.insert(j),..e.history[k-1] }; let u=replace_e(s,i,fle::LServer { history: e.history.update(k-1,txn),..e });
                if last_committed(s,i).index < e.history.len() && newer(zxid,last_committed(s,i).zxid) && n.committed.index >= k-1 && z::quorum(txn.ack,c) {
                    let at=Commit { index: k,zxid }; let u=replace_e(replace(u,i,LServer { committed: at,..n }),i,fle::LServer { processed: at,..u.election.nodes[i] });
                    discard_broadcast(u,i,j,n.forwarding,Message::Commit(zxid))
                } else { discard(u,j,i) }
            } else { discard(s,j,i) }
        }, _ => s },
        Action::Commit(_,j) => match s.msgs[(j,i)][0] { Message::Commit(zxid) => {
            let u=if n.committed.index < e.history.len() && e.history[n.committed.index].zxid == zxid {
                let at=Commit { index: n.committed.index+1,zxid }; replace_e(replace(s,i,LServer { committed: at,..n }),i,fle::LServer { processed: at,..e })
            } else { s }; discard(u,j,i)
        }, _ => s },
    }
}
#[verifier::opaque]
pub open spec fn next(s: LState,u: LState,c: Constants) -> bool { exists |a: Action| #[trigger] enabled(s,c,a) && u == apply(s,c,a) }
// The goal definitions share the abstract Zab predicates, except Leadership1,
// which compares acceptedEpoch in this benchmark instead of currentEpoch.
pub open spec fn goal_state(s: LState) -> z::LState {
    z::LState { nodes: Map::new(s.nodes.dom(),|i: int| z::LServer { role: s.election.nodes[i].role,phase: s.nodes[i].phase,accepted: s.nodes[i].accepted,current: s.election.nodes[i].current,
        history: s.election.nodes[i].history,committed: s.nodes[i].committed,learners: s.nodes[i].learners,leader: s.nodes[i].leader,ce: Set::empty(),ae: Set::empty(),al: Set::empty(),sent: 0 }),
        oracle: None,msgs: Map::empty(),epoch_leader: s.epoch_leader,proposals: s.proposals }
}
pub open spec fn leadership1(s: LState,c: Constants) -> bool {
    let p=goal_state(s); let p=z::LState { nodes: Map::new(p.nodes.dom(),|i: int| z::LServer { current: p.nodes[i].accepted,..p.nodes[i] }),..p }; z::leadership1(p,c)
}
pub open spec fn leadership2(s: LState,c: Constants) -> bool { z::leadership2(goal_state(s),c) }
pub open spec fn prefix_consistency(s: LState,c: Constants) -> bool { z::prefix_consistency(goal_state(s),c) }
pub open spec fn integrity(s: LState,c: Constants) -> bool { z::integrity(goal_state(s),c) }
pub open spec fn agreement(s: LState,c: Constants) -> bool { z::agreement(goal_state(s),c) }
pub open spec fn total_order(s: LState,c: Constants) -> bool { z::total_order(goal_state(s),c) }
pub open spec fn local_primary_order(s: LState,c: Constants) -> bool { z::local_primary_order(goal_state(s),c) }
pub open spec fn global_primary_order(s: LState,c: Constants) -> bool { z::global_primary_order(goal_state(s),c) }
pub open spec fn primary_integrity(s: LState,c: Constants) -> bool { z::primary_integrity(goal_state(s),c) }
} // verus!
