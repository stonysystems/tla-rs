//! Handwritten ZabModel and ZabDefs from the pinned current benchmark.
//! FIFO channels, receipt records (including disconnected records), crashes,
//! and the source's passive proposal/epoch histories are retained.
use vstd::prelude::*;
verus! {
pub enum Role { Looking, Following, Leading }
pub enum Phase { Election, Discovery, Synchronization, Broadcast }
pub struct Zxid { pub epoch: int, pub counter: int }
pub struct Txn { pub zxid: Zxid, pub value: int, pub ack: Set<int>, pub epoch: int }
pub struct Commit { pub index: int, pub zxid: Zxid }
pub struct CE { pub sid: int, pub connected: bool, pub epoch: int }
pub struct AE { pub sid: int, pub connected: bool, pub epoch: int, pub history: Seq<Txn> }
pub struct AL { pub sid: int, pub connected: bool }
pub struct Proposal { pub source: int, pub epoch: int, pub zxid: Zxid, pub value: int }
pub enum Message { CEpoch(int), NewEpoch(int), AckEpoch(int,Seq<Txn>), NewLeader(int,Seq<Txn>),
    AckLd(Zxid), CommitLd(Zxid), Propose(Zxid,int), Ack(Zxid), Commit(Zxid) }
pub struct LServer {
    pub role: Role, pub phase: Phase, pub accepted: int, pub current: int,
    pub history: Seq<Txn>, pub committed: Commit, pub learners: Set<int>,
    pub ce: Set<CE>, pub ae: Set<AE>, pub al: Set<AL>, pub sent: int, pub leader: Option<int>,
}
pub struct Constants { pub servers: Set<int>, pub max_epoch: int, pub request_value: int }
pub struct LState { pub nodes: Map<int,LServer>, pub oracle: Option<int>,
    pub msgs: Map<(int,int),Seq<Message>>, pub epoch_leader: Map<int,Set<int>>, pub proposals: Set<Proposal> }
pub open spec fn valid_constants(c: Constants) -> bool { c.max_epoch > 0 }
pub open spec fn quorum(q: Set<int>,c: Constants) -> bool { q.subset_of(c.servers) && 2*q.len() > c.servers.len() }
pub open spec fn newer(a: Zxid,b: Zxid) -> bool { a.epoch > b.epoch || a.epoch == b.epoch && a.counter > b.counter }
pub open spec fn equal(a: Txn,b: Txn) -> bool { a.zxid == b.zxid && a.value == b.value }
pub open spec fn zero() -> Zxid { Zxid { epoch: 0,counter: 0 } }
pub open spec fn boot() -> Zxid { Zxid { epoch: 0,counter: 1 } }
pub open spec fn last(h: Seq<Txn>) -> Zxid { if h.len() == 0 { zero() } else { h.last().zxid } }
#[verifier::opaque]
pub open spec fn maximum(q: Set<int>) -> int { if q.is_empty() { -1 } else { choose |v: int| q.contains(v) && forall |w: int| q.contains(w) ==> w <= v } }
pub open spec fn channels(c: Constants) -> Set<(int,int)> { c.servers.map(|i: int| c.servers.map(|j: int| (i,j))).flatten() }
pub open spec fn initial(c: Constants) -> LState {
    LState { nodes: Map::new(c.servers,|i: int| LServer { role: Role::Looking,phase: Phase::Election,
        accepted: 0,current: 0,history: seq![Txn { zxid: boot(),value: 0,ack: c.servers,epoch: 0 }],
        committed: Commit { index: 1,zxid: boot() },learners: Set::empty(),ce: Set::empty(),ae: Set::empty(),al: Set::empty(),sent: 0,leader: None }),
        oracle: None,msgs: Map::new(channels(c),|p: (int,int)| Seq::empty()),
        epoch_leader: Map::new(Set::range(1,c.max_epoch+1),|e: int| Set::empty()),
        proposals: c.servers.map(|i: int| Proposal { source: i,epoch: 0,zxid: boot(),value: 0 }) }
}
pub open spec fn replace(s: LState,i: int,n: LServer) -> LState { LState { nodes: s.nodes.insert(i,n),..s } }
pub open spec fn send(s: LState,i: int,j: int,m: Message) -> LState { LState { msgs: s.msgs.insert((i,j),s.msgs[(i,j)].push(m)),..s } }
pub open spec fn discard(s: LState,i: int,j: int) -> LState {
    LState { msgs: s.msgs.insert((i,j),if s.msgs[(i,j)].len() == 0 { s.msgs[(i,j)] } else { s.msgs[(i,j)].drop_first() }),..s }
}
pub open spec fn reply(s: LState,i: int,j: int,m: Message) -> LState {
    LState { msgs: s.msgs.insert((j,i),s.msgs[(j,i)].drop_first()).insert((i,j),s.msgs[(i,j)].push(m)),..s }
}
pub open spec fn clean(s: LState,i: int,j: int) -> LState {
    LState { msgs: s.msgs.insert((i,j),Seq::empty()).insert((j,i),Seq::empty()),..s }
}
pub open spec fn clean_input(s: LState,c: Constants,q: Set<int>) -> LState {
    LState { msgs: Map::new(channels(c),|p: (int,int)| if q.contains(p.1) { Seq::empty() } else { s.msgs[p] }),..s }
}
pub open spec fn broadcast(s: LState,i: int,q: Set<int>,m: Message) -> LState {
    LState { msgs: Map::new(s.msgs.dom(),|p: (int,int)| if p.0 == i && p.1 != i && q.contains(p.1) && s.nodes[i].learners.contains(p.1) { s.msgs[p].push(m) } else { s.msgs[p] }),..s }
}
// Match the source's simultaneous EXCEPT: replacing the outgoing row wins
// if i == j, and its values are computed from the old channel map.
pub open spec fn discard_broadcast(s: LState,i: int,j: int,q: Set<int>,m: Message) -> LState {
    let t=broadcast(s,i,q,m);
    if i == j { t } else { LState { msgs: t.msgs.insert((j,i),s.msgs[(j,i)].drop_first()),..t } }
}
pub open spec fn ce_ids(q: Set<CE>) -> Set<int> { q.map(|x: CE| x.sid) }
pub open spec fn ae_ids(q: Set<AE>) -> Set<int> { q.map(|x: AE| x.sid) }
pub open spec fn al_ids(q: Set<AL>) -> Set<int> { q.map(|x: AL| x.sid) }
pub open spec fn ce_connected(q: Set<CE>) -> Set<int> { ce_ids(q.filter(|x: CE| x.connected)) }
pub open spec fn ae_connected(q: Set<AE>) -> Set<int> { ae_ids(q.filter(|x: AE| x.connected)) }
pub open spec fn al_connected(q: Set<AL>) -> Set<int> { al_ids(q.filter(|x: AL| x.connected)) }
pub open spec fn update_ce(q: Set<CE>,i: int,e: int) -> Set<CE> {
    let old=choose |r: CE| #![trigger q.contains(r)] q.contains(r) && r.sid == i;
    (if ce_ids(q).contains(i) { q.remove(old) } else { q }).insert(CE { sid: i,connected: true,epoch: e })
}
pub open spec fn update_ae(q: Set<AE>,i: int,e: int,h: Seq<Txn>) -> Set<AE> {
    let old=choose |r: AE| #![trigger q.contains(r)] q.contains(r) && r.sid == i;
    (if ae_ids(q).contains(i) { q.remove(old) } else { q }).insert(AE { sid: i,connected: true,epoch: e,history: h })
}
pub open spec fn update_al(q: Set<AL>,i: int) -> Set<AL> {
    let old=choose |r: AL| #![trigger q.contains(r)] q.contains(r) && r.sid == i;
    (if al_ids(q).contains(i) { q.remove(old) } else { q }).insert(AL { sid: i,connected: true })
}
pub open spec fn disconnect_ce(q: Set<CE>,i: int) -> Set<CE> {
    let old=choose |r: CE| #![trigger q.contains(r)] q.contains(r) && r.sid == i;
    if ce_ids(q).contains(i) { q.remove(old).insert(CE { connected: false,..old }) } else { q }
}
pub open spec fn disconnect_ae(q: Set<AE>,i: int) -> Set<AE> {
    let old=choose |r: AE| #![trigger q.contains(r)] q.contains(r) && r.sid == i;
    if ae_ids(q).contains(i) { q.remove(old).insert(AE { connected: false,..old }) } else { q }
}
pub open spec fn disconnect_al(q: Set<AL>,i: int) -> Set<AL> {
    let old=choose |r: AL| #![trigger q.contains(r)] q.contains(r) && r.sid == i;
    if al_ids(q).contains(i) { q.remove(old).insert(AL { connected: false,..old }) } else { q }
}
pub open spec fn remove_learner(s: LState,i: int,j: int) -> LState {
    let n=s.nodes[i]; replace(s,i,LServer { learners: n.learners.remove(j),ce: disconnect_ce(n.ce,j),ae: disconnect_ae(n.ae,j),al: disconnect_al(n.al,j),..n })
}
pub open spec fn shut_follower(s: LState,i: int) -> LState { replace(s,i,LServer { role: Role::Looking,phase: Phase::Election,leader: None,..s.nodes[i] }) }
pub open spec fn shut_leader(s: LState,c: Constants,i: int) -> LState {
    let q=s.nodes[i].learners;
    let nodes=Map::new(c.servers,|j: int| if q.contains(j) { LServer { role: Role::Looking,phase: Phase::Election,leader: None,..s.nodes[j] } } else { s.nodes[j] });
    clean_input(LState { nodes: nodes.insert(i,LServer { learners: Set::empty(),..nodes[i] }),..s },c,q)
}
pub open spec fn lose_follower(s: LState,c: Constants,i: int,j: int) -> LState {
    if quorum(s.nodes[i].learners.remove(j),c) { clean(shut_follower(remove_learner(s,i,j),j),i,j) } else { shut_leader(s,c,i) }
}
pub open spec fn lead(n: LServer,i: int) -> LServer {
    LServer { role: Role::Leading,phase: Phase::Discovery,learners: set![i],
        ce: set![CE { sid: i,connected: true,epoch: n.accepted }],
        ae: set![AE { sid: i,connected: true,epoch: n.current,history: n.history }],
        al: set![AL { sid: i,connected: true }],sent: 0,..n }
}
pub open spec fn records(i: int,e: int,h: Seq<Txn>) -> Set<Proposal> {
    Set::range(0,h.len() as int).map(|k: int| Proposal { source: i,epoch: e,zxid: h[k].zxid,value: h[k].value })
}
pub struct Summary { pub sid: int, pub epoch: int, pub zxid: Zxid }
pub open spec fn select_history(q: Set<AE>) -> Seq<Txn> {
    let summaries=q.map(|a: AE| Summary { sid: a.sid,epoch: a.epoch,zxid: last(a.history) });
    let selected=choose |a: Summary| summaries.contains(a) && forall |b: Summary| #![trigger summaries.contains(b)] summaries.contains(b) && b != a ==> a.epoch > b.epoch || a.epoch == b.epoch && !newer(b.zxid,a.zxid);
    let info=choose |a: AE| #![trigger q.contains(a)] q.contains(a) && a.sid == selected.sid;
    info.history
}
pub open spec fn init_ack(h: Seq<Txn>,i: int) -> Seq<Txn> { Seq::new(h.len(),|k: int| Txn { ack: set![i],..h[k] }) }
pub open spec fn update_ack(h: Seq<Txn>,i: int,z: Zxid) -> Seq<Txn> {
    let b=choose |b: int| #![trigger h[b]] 0 <= b <= h.len() && (forall |k: int| #![trigger h[k]] 0 <= k < b ==> !newer(h[k].zxid,z)) && (b < h.len() ==> newer(h[b].zxid,z));
    Seq::new(h.len(),|k: int| if k < b { Txn { ack: h[k].ack.insert(i),..h[k] } } else { h[k] })
}
pub open spec fn index(h: Seq<Txn>,z: Zxid) -> int {
    let matches=Set::range(1,h.len() as int+1).filter(|k: int| h[k-1].zxid == z);
    if z == zero() { 0 } else if matches.len() == 0 { h.len() as int+1 }
    else if matches.len() == 1 { choose |k: int| matches.contains(k) } else { -1 }
}
pub open spec fn next_zxid(a: Zxid,b: Zxid) -> bool {
    b.counter == 1 && a.epoch < b.epoch || b.counter > 1 && a.epoch == b.epoch && a.counter+1 == b.counter
}
pub open spec fn counter(n: LServer) -> int { if last(n.history).epoch == n.current { last(n.history).counter } else { 0 } }
pub enum Action { UpdateLeader(int),FollowLeader(int),Timeout(int,int),Restart(int),Connect(int,int),
    CEpoch(int,int),NewEpoch(int,int),AckEpoch(int,int),NewLeader(int,int),AckLd(int,int),CommitLd(int,int),
    Request(int),Broadcast(int),Propose(int,int),Ack(int,int),Commit(int,int),Stutter }
#[verifier::opaque]
pub open spec fn enabled(s: LState,c: Constants,a: Action) -> bool {
    match a {
        Action::Stutter => true,
        Action::UpdateLeader(i) => c.servers.contains(i) && s.nodes[i].role == Role::Looking && s.oracle != Some(i),
        Action::FollowLeader(i) => c.servers.contains(i) && s.nodes[i].role == Role::Looking && s.oracle is Some,
        Action::Restart(i) => c.servers.contains(i),
        Action::Request(i) => c.servers.contains(i) && s.nodes[i].role == Role::Leading && s.nodes[i].phase == Phase::Broadcast,
        Action::Broadcast(i) => c.servers.contains(i) && s.nodes[i].role == Role::Leading && s.nodes[i].phase == Phase::Broadcast && s.nodes[i].sent < counter(s.nodes[i]),
        Action::Timeout(i,j) => c.servers.contains(i) && c.servers.contains(j) && s.nodes[i].role == Role::Leading && s.nodes[j].role == Role::Following && s.nodes[i].learners.contains(j) && s.nodes[j].leader == Some(i),
        Action::Connect(i,j) => c.servers.contains(i) && c.servers.contains(j) && s.nodes[i].role == Role::Leading && s.nodes[j].role == Role::Following && !s.nodes[i].learners.contains(j) && s.nodes[j].leader == None && s.oracle == Some(i),
        Action::CEpoch(i,j) | Action::AckEpoch(i,j) | Action::AckLd(i,j) | Action::Ack(i,j) =>
            c.servers.contains(i) && c.servers.contains(j) && s.nodes[i].role == Role::Leading && s.nodes[i].learners.contains(j) && s.msgs[(j,i)].len() > 0 && match a {
                Action::CEpoch(_,_) => s.msgs[(j,i)][0] is CEpoch,
                Action::AckEpoch(_,_) => s.msgs[(j,i)][0] is AckEpoch,
                Action::AckLd(_,_) => s.msgs[(j,i)][0] is AckLd,
                _ => s.msgs[(j,i)][0] is Ack,
            },
        Action::NewEpoch(i,j) | Action::NewLeader(i,j) | Action::CommitLd(i,j) | Action::Propose(i,j) | Action::Commit(i,j) =>
            c.servers.contains(i) && c.servers.contains(j) && s.nodes[i].role == Role::Following && s.nodes[i].leader == Some(j) && s.msgs[(j,i)].len() > 0 && match a {
                Action::NewEpoch(_,_) => s.msgs[(j,i)][0] is NewEpoch,
                Action::NewLeader(_,_) => s.msgs[(j,i)][0] is NewLeader,
                Action::CommitLd(_,_) => s.msgs[(j,i)][0] is CommitLd,
                Action::Propose(_,_) => s.msgs[(j,i)][0] is Propose,
                _ => s.msgs[(j,i)][0] is Commit,
            },
    }
}
#[verifier::opaque]
pub open spec fn apply(s: LState,c: Constants,a: Action) -> LState {
    match a {
        Action::Stutter => s,
        Action::UpdateLeader(i) => LState { oracle: Some(i),..replace(s,i,lead(s.nodes[i],i)) },
        Action::FollowLeader(i) => replace(s,i,if s.oracle == Some(i) { lead(s.nodes[i],i) } else { LServer { role: Role::Following,phase: Phase::Discovery,..s.nodes[i] } }),
        Action::Timeout(i,j) => lose_follower(s,c,i,j),
        Action::Restart(i) => {
            let t=match s.nodes[i].role { Role::Looking => s,Role::Leading => shut_leader(s,c,i),Role::Following => match s.nodes[i].leader { None => clean_input(shut_follower(s,i),c,set![i]),Some(j) => lose_follower(s,c,j,i) } };
            replace(t,i,LServer { committed: Commit { index: 0,zxid: zero() },..t.nodes[i] })
        },
        Action::Connect(i,j) => {
            let t=replace(s,i,LServer { learners: s.nodes[i].learners.insert(j),..s.nodes[i] });
            send(replace(t,j,LServer { leader: Some(i),..t.nodes[j] }),j,i,Message::CEpoch(s.nodes[j].accepted))
        },
        Action::CEpoch(i,j) => match s.msgs[(j,i)][0] { Message::CEpoch(e) => {
            let n=s.nodes[i]; let ce=update_ce(n.ce,j,e);
            let first=!quorum(ce_ids(n.ce),c) && quorum(ce_ids(ce),c);
            let epoch=if first { maximum(ce.map(|r: CE| r.epoch))+1 } else { n.accepted };
            let t=replace(s,i,LServer { ce,accepted: epoch,..n });
            if first { discard_broadcast(t,i,j,ce_connected(ce),Message::NewEpoch(epoch)) }
            else if quorum(ce_ids(n.ce),c) { reply(t,i,j,Message::NewEpoch(epoch)) } else { discard(t,j,i) }
        }, _ => s },
        Action::NewEpoch(i,j) => match s.msgs[(j,i)][0] { Message::NewEpoch(e) => {
            let n=s.nodes[i];
            if e < n.accepted { clean(remove_learner(shut_follower(s,i),j,i),i,j) }
            else if n.phase == Phase::Discovery {
                reply(replace(s,i,LServer { accepted: e,phase: Phase::Synchronization,..n }),i,j,Message::AckEpoch(n.current,n.history))
            } else { discard(s,j,i) }
        }, _ => s },
        Action::AckEpoch(i,j) => match s.msgs[(j,i)][0] { Message::AckEpoch(e,h) => {
            let n=s.nodes[i]; let ae=update_ae(n.ae,j,e,h);
            let first=!quorum(ae_ids(n.ae),c) && quorum(ae_ids(ae),c);
            let h2=if first { init_ack(select_history(ae),i) } else { n.history };
            let t=replace(s,i,LServer { ae,history: h2,current: if first { n.accepted } else { n.current },phase: if first { Phase::Synchronization } else { n.phase },..n });
            if first || quorum(ae_ids(n.ae),c) {
                let epochs=if first && s.epoch_leader.dom().contains(n.accepted) { s.epoch_leader.insert(n.accepted,s.epoch_leader[n.accepted].insert(i)) } else { s.epoch_leader };
                let t=LState { epoch_leader: epochs,proposals: s.proposals.union(records(i,n.accepted,h2)),..t };
                if first { discard_broadcast(t,i,j,ae_connected(ae),Message::NewLeader(n.accepted,h2)) }
                else { reply(t,i,j,Message::NewLeader(n.accepted,h2)) }
            } else { discard(t,j,i) }
        }, _ => s },
        Action::NewLeader(i,j) => match s.msgs[(j,i)][0] { Message::NewLeader(e,h) => {
            let n=s.nodes[i];
            if n.accepted != e { clean(remove_learner(shut_follower(s,i),j,i),i,j) }
            else { reply(replace(s,i,LServer { current: n.accepted,history: h,..n }),i,j,Message::AckLd(last(h))) }
        }, _ => s },
        Action::AckLd(i,j) => match s.msgs[(j,i)][0] { Message::AckLd(z) => {
            let n=s.nodes[i]; let al=update_al(n.al,j);
            let first=!quorum(al_ids(n.al),c) && quorum(al_ids(al),c);
            let t=replace(s,i,LServer { al,history: update_ack(n.history,j,z),
                committed: if first { Commit { index: n.history.len() as int,zxid: last(n.history) } } else { n.committed },phase: if first { Phase::Broadcast } else { n.phase },..n });
            if first { discard_broadcast(t,i,j,al_connected(al),Message::CommitLd(last(n.history))) }
            else if quorum(al_ids(n.al),c) { reply(t,i,j,Message::CommitLd(n.committed.zxid)) } else { discard(t,j,i) }
        }, _ => s },
        Action::CommitLd(i,j) => match s.msgs[(j,i)][0] { Message::CommitLd(z) => {
            let n=s.nodes[i]; discard(replace(s,i,LServer { committed: Commit { index: index(n.history,z),zxid: z },phase: Phase::Broadcast,..n }),j,i)
        }, _ => s },
        Action::Request(i) => {
            let n=s.nodes[i]; let old=last(n.history);
            let z=Zxid { epoch: n.current,counter: if n.current == old.epoch { old.counter+1 } else { 1 } };
            replace(s,i,LServer { history: n.history.push(Txn { zxid: z,value: c.request_value,ack: set![i],epoch: n.current }),..n })
        },
        Action::Broadcast(i) => {
            let n=s.nodes[i]; let t=n.history[index(n.history,Zxid { epoch: n.current,counter: n.sent+1 })-1];
            let s1=replace(s,i,LServer { sent: n.sent+1,..n });
            broadcast(LState { proposals: s.proposals.insert(Proposal { source: i,epoch: n.current,zxid: t.zxid,value: t.value }),..s1 },i,ae_connected(n.ae),Message::Propose(t.zxid,t.value))
        },
        Action::Propose(i,j) => match s.msgs[(j,i)][0] { Message::Propose(z,v) => {
            let n=s.nodes[i]; if next_zxid(last(n.history),z) {
                reply(replace(s,i,LServer { history: n.history.push(Txn { zxid: z,value: v,ack: Set::empty(),epoch: n.current }),..n }),i,j,Message::Ack(z))
            } else { discard(s,j,i) }
        }, _ => s },
        Action::Ack(i,j) => match s.msgs[(j,i)][0] { Message::Ack(z) => {
            let n=s.nodes[i]; let k=index(n.history,z);
            let ack_index=maximum(Set::range(1,n.history.len() as int+1).filter(|k: int| n.history[k-1].ack.contains(j)));
            if 1 <= k <= n.history.len() && (ack_index == -1 || ack_index+1 == k) {
                let t=Txn { ack: n.history[k-1].ack.insert(j),..n.history[k-1] };
                let s1=replace(s,i,LServer { history: n.history.update(k-1,t),..n });
                if n.committed.index < n.history.len() && newer(z,n.committed.zxid) && n.committed.index >= k-1 && quorum(t.ack,c) {
                    let s2=replace(s1,i,LServer { committed: Commit { index: k,zxid: z },..s1.nodes[i] });
                    discard_broadcast(s2,i,j,al_connected(n.al),Message::Commit(z))
                } else { discard(s1,j,i) }
            } else { discard(s,j,i) }
        }, _ => s },
        Action::Commit(i,j) => match s.msgs[(j,i)][0] { Message::Commit(z) => {
            let n=s.nodes[i]; let t=n.history[n.committed.index];
            discard(if n.committed.index < n.history.len() && t.zxid == z {
                replace(s,i,LServer { committed: Commit { index: n.committed.index+1,zxid: t.zxid },..n })
            } else { s },j,i)
        }, _ => s },
    }
}
#[verifier::opaque]
pub open spec fn next(s: LState,t: LState,c: Constants) -> bool { exists |a: Action| #[trigger] enabled(s,c,a) && t == apply(s,c,a) }
pub open spec fn leadership1(s: LState,c: Constants) -> bool {
    forall |i: int,j: int| #![trigger c.servers.contains(i), c.servers.contains(j)] c.servers.contains(i) && c.servers.contains(j) && s.nodes[i].role == Role::Leading && s.nodes[j].role == Role::Leading
    && (s.nodes[i].phase == Phase::Synchronization || s.nodes[i].phase == Phase::Broadcast) && (s.nodes[j].phase == Phase::Synchronization || s.nodes[j].phase == Phase::Broadcast)
    && s.nodes[i].current == s.nodes[j].current ==> i == j
}
pub open spec fn leadership2(s: LState,c: Constants) -> bool { forall |e: int| 1 <= e <= c.max_epoch ==> #[trigger] s.epoch_leader[e].len() <= 1 }
pub open spec fn prefix_consistency(s: LState,c: Constants) -> bool {
    (forall |i: int| #![trigger c.servers.contains(i)] c.servers.contains(i) ==> s.nodes[i].committed.index >= 0)
    && forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && 1 <= k <= s.nodes[i].committed.index && k <= s.nodes[j].committed.index ==> #[trigger] equal(s.nodes[i].history[k-1],s.nodes[j].history[k-1])
}
pub open spec fn proposed(s: LState,t: Txn) -> bool { exists |p: Proposal| #[trigger] s.proposals.contains(p) && p.zxid == t.zxid && p.value == t.value }
pub open spec fn integrity(s: LState,c: Constants) -> bool {
    forall |i: int,k: int| c.servers.contains(i) && s.nodes[i].role == Role::Following && 1 <= k <= s.nodes[i].committed.index ==>
        #[trigger] proposed(s,s.nodes[i].history[k-1])
}
pub open spec fn contains_txn(n: LServer,t: Txn) -> bool { exists |k: int| 1 <= k <= n.committed.index && #[trigger] equal(n.history[k-1],t) }
pub open spec fn agreement(s: LState,c: Constants) -> bool {
    forall |i: int,j: int,x: int,y: int| c.servers.contains(i) && c.servers.contains(j) && s.nodes[i].role == Role::Following && s.nodes[j].role == Role::Following && 1 <= x <= s.nodes[i].committed.index && 1 <= y <= s.nodes[j].committed.index ==>
        #[trigger] contains_txn(s.nodes[j],s.nodes[i].history[x-1]) || #[trigger] contains_txn(s.nodes[i],s.nodes[j].history[y-1])
}
pub open spec fn before(n: LServer,a: Txn,b: Txn) -> bool { exists |x: int,y: int| 1 <= x < y <= n.committed.index && #[trigger] equal(n.history[x-1],a) && #[trigger] equal(n.history[y-1],b) }
pub open spec fn total_order(s: LState,c: Constants) -> bool {
    forall |i: int,j: int,x: int,y: int| c.servers.contains(i) && c.servers.contains(j) && s.nodes[j].committed.index >= 2 && 1 <= x < y <= s.nodes[i].committed.index && contains_txn(s.nodes[j],s.nodes[i].history[y-1]) ==>
        #[trigger] before(s.nodes[j],s.nodes[i].history[x-1],s.nodes[i].history[y-1])
}
pub open spec fn local_at(s: LState,i: int,e: int,j: int) -> bool {
    forall |p: Proposal,q: Proposal| #![trigger s.proposals.contains(p), s.proposals.contains(q)] s.proposals.contains(p) && s.proposals.contains(q) && p.source == i && q.source == i && p.epoch == e && q.epoch == e && (p.zxid != q.zxid || p.value != q.value) ==>
    {
        let a=if newer(p.zxid,q.zxid) { q } else { p }; let b=if newer(p.zxid,q.zxid) { p } else { q };
        let ta=Txn { zxid: a.zxid,value: a.value,ack: Set::empty(),epoch: 0 }; let tb=Txn { zxid: b.zxid,value: b.value,ack: Set::empty(),epoch: 0 };
        contains_txn(s.nodes[j],tb) ==> before(s.nodes[j],ta,tb)
    }
}
pub open spec fn local_primary_order(s: LState,c: Constants) -> bool {
    forall |i: int,e: int,j: int| c.servers.contains(i) && c.servers.contains(j) && 1 <= e <= s.nodes[i].current ==> #[trigger] local_at(s,i,e,j)
}
pub open spec fn epoch_order(n: LServer,x: int,y: int) -> bool { n.history[x-1].zxid.epoch < n.history[y-1].zxid.epoch ==> x < y }
pub open spec fn global_primary_order(s: LState,c: Constants) -> bool {
    forall |i: int,x: int,y: int| c.servers.contains(i) && s.nodes[i].committed.index >= 2 && 1 <= x <= s.nodes[i].committed.index && 1 <= y <= s.nodes[i].committed.index
        ==> #[trigger] epoch_order(s.nodes[i],x,y)
}
pub open spec fn primary_integrity(s: LState,c: Constants) -> bool {
    forall |i: int,j: int,k: int| c.servers.contains(i) && c.servers.contains(j) && s.nodes[i].role == Role::Leading && s.nodes[i].learners.contains(j) && s.nodes[j].role == Role::Following && s.nodes[j].leader == Some(i)
    && s.nodes[i].phase == Phase::Broadcast && s.nodes[j].phase == Phase::Broadcast && 1 <= k <= s.nodes[j].committed.index && s.nodes[j].history[k-1].zxid.epoch < s.nodes[i].current ==>
        #[trigger] contains_txn(s.nodes[i],s.nodes[j].history[k-1])
}
} // verus!
