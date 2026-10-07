//! Handwritten HashicorpRaftRuntime, including single-server configuration
//! changes, split vote persistence, leases, blocked disks, crashes, and histories.
use vstd::prelude::*;
use vstd::multiset::Multiset;
verus! {
pub enum Role { Follower, Candidate, Leader }
pub enum EntryKind { Value, Config }
pub struct Entry { pub term: nat, pub kind: EntryKind, pub config: Set<int>, pub value: Option<int> }
pub enum Mode { Replicate, Heartbeat }
pub enum Body {
    VoteRequest { last_term: nat, last_index: nat }, VoteResponse { granted: bool },
    AppendRequest { mode: Mode, prev: int, prev_term: nat, entries: Seq<Entry>, commit: nat },
    AppendResponse { mode: Mode, success: bool, matched: int },
}
pub struct Message { pub source: int, pub dest: int, pub term: nat, pub body: Body }
pub struct Vote { pub candidate: int, pub term: nat }
pub struct LServer {
    pub term: nat, pub voted_for: Option<int>, pub role: Role, pub log: Seq<Entry>, pub commit: nat,
    pub next_index: Map<int, int>, pub matched: Map<int, int>, pub granted: Set<int>, pub contacts: Set<int>,
    pub disk_blocked: bool, pub committed_config: Set<int>, pub latest_config: Set<int>,
    pub committed_config_index: nat, pub latest_config_index: nat, pub persisted_term: nat,
    pub persisted_vote_term: nat, pub persisted_voted_for: Option<int>, pub pending_vote: Option<Vote>,
}
pub struct Event { pub server: int, pub term: nat, pub entries: Seq<Entry> }
pub struct LState { pub nodes: Map<int, LServer>, pub messages: Multiset<Message>, pub elections: Set<Event>, pub commits: Set<Event> }
pub struct Constants { pub servers: Set<int>, pub values: ISet<int> }
pub open spec fn valid_constants(c: Constants) -> bool { !c.servers.is_empty() && !c.values.is_empty() }
pub open spec fn min(a: int, b: int) -> int { if a < b { a } else { b } }
pub open spec fn max(a: int, b: int) -> int { if a > b { a } else { b } }
pub open spec fn quorum(q: Set<int>, voters: Set<int>) -> bool { 2*q.len() > voters.len() }
pub open spec fn sub(log: Seq<Entry>, first: int, last: int) -> Seq<Entry> {
    Seq::new(if last < first { 0 } else { (last-first+1) as nat }, |i: int| log[i+first-1])
}
pub open spec fn log_term(log: Seq<Entry>, index: int) -> nat { if 1 <= index <= log.len() { log[index-1].term } else { 0 } }
pub open spec fn up_to_date(log: Seq<Entry>, term: nat, len: nat) -> bool { term > log_term(log, log.len() as int) || term == log_term(log, log.len() as int) && len >= log.len() }
pub open spec fn last_config(log: Seq<Entry>) -> nat
    decreases log.len()
{ if log.len() == 0 { 0 } else if log.last().kind == EntryKind::Config { log.len() } else { last_config(log.drop_last()) } }
pub open spec fn previous_config(log: Seq<Entry>) -> nat
    decreases log.len()
{ if log.len() == 0 { 0 } else if log.last().kind == EntryKind::Config { last_config(log.drop_last()) } else { previous_config(log.drop_last()) } }
pub open spec fn config_at(log: Seq<Entry>, index: nat, c: Constants) -> Set<int> { if index == 0 { c.servers } else { log[index-1].config } }
#[verifier::opaque]
pub open spec fn merge(old: Seq<Entry>, prev: int, entries: Seq<Entry>) -> Seq<Entry> {
    // Compare zero-based entry positions so the quantified trigger has no
    // shifted index. hashicorp_types::merge_correspondence checks equivalence
    // with the original one-based search at every valid merge boundary.
    let first = choose |k: int| 1 <= k <= entries.len()+1
        && (forall |j: int| 0 <= j < k-1 ==> prev+j < old.len() && old[prev+j].term == (#[trigger] entries[j]).term)
        && (k == entries.len()+1 || prev+k > old.len() || old[prev+k-1].term != (#[trigger] entries[k-1]).term);
    if entries.len() == 0 || first == entries.len()+1 { old }
    else { sub(old, 1, prev+first-1) + sub(entries, first, entries.len() as int) }
}
pub open spec fn initial(c: Constants) -> LState {
    LState { messages: Multiset::empty(), elections: Set::empty(), commits: Set::empty(), nodes: Map::new(c.servers, |i: int| LServer {
        term: 0, voted_for: None, role: Role::Follower, log: Seq::empty(), commit: 0,
        next_index: Map::new(c.servers, |j: int| 1), matched: Map::new(c.servers, |j: int| 0), granted: Set::empty(), contacts: Set::empty(),
        disk_blocked: false, committed_config: c.servers, latest_config: c.servers, committed_config_index: 0, latest_config_index: 0,
        persisted_term: 0, persisted_vote_term: 0, persisted_voted_for: None, pending_vote: None,
    }) }
}
pub open spec fn replace(s: LState, i: int, n: LServer) -> LState { LState { nodes: s.nodes.insert(i, n), ..s } }
pub open spec fn send(s: LState, m: Message) -> LState { LState { messages: s.messages.insert(m), ..s } }
pub open spec fn discard(s: LState, m: Message) -> LState { LState { messages: s.messages.remove(m), ..s } }
pub open spec fn reply(s: LState, m: Message, term: nat, body: Body) -> LState { send(discard(s,m), Message { source: m.dest, dest: m.source, term, body }) }
pub open spec fn higher_term(n: LServer, term: nat) -> LServer { LServer { term, role: Role::Follower, voted_for: None, persisted_term: term, ..n } }
pub open spec fn can_grant(n: LServer, m: Message, term: nat, len: nat) -> bool {
    up_to_date(n.log, term, len) && (m.term > n.term || m.term == n.term && (n.voted_for == None || n.voted_for == Some(m.source)))
}
pub open spec fn log_ok(n: LServer, prev: int, term: nat) -> bool { prev == 0 || 0 < prev <= n.log.len() && log_term(n.log, prev) == term }
pub open spec fn agree_indices(n: LServer, i: int, c: Constants) -> Set<int> {
    Set::<int>::range(n.commit as int + 1, n.log.len() as int + 1).filter(|idx: int|
        quorum(c.servers.filter(|j: int| n.matched[j] >= idx).insert(i).intersect(n.latest_config), n.latest_config) && n.log[idx-1].term == n.term)
}
#[verifier::opaque]
pub open spec fn maximum(s: Set<int>) -> int { choose |x: int| s.contains(x) && forall |y: int| s.contains(y) ==> y <= x }
pub enum Receive { FollowerRejectVote, RefuseVote, GrantVote, DeferVote, VoteResponse,
    StaleAppend, RejectAppend, AcceptAppend, ReplicateResponse, HeartbeatResponse, DropStale }
pub enum Action {
    Timeout(int), BecomeLeader(int), CompleteVote(int), CheckLease(int), DiskBlock(int), DiskUnblock(int), Crash(int), AdvanceCommit(int),
    ClientRequest { i: int, value: int }, ProposeConfig { i: int, member: int }, Replicate { i: int, j: int }, Heartbeat { i: int, j: int },
    Receive { m: Message, how: Receive }, Lose(Message), Stutter,
}
#[verifier::opaque]
pub open spec fn receive_enabled(s: LState, m: Message, how: Receive) -> bool {
    let n = s.nodes[m.dest];
    s.messages.count(m) > 0 && match how {
        Receive::DropStale => m.term < n.term,
        Receive::VoteResponse => m.body is VoteResponse && n.role == Role::Candidate,
        Receive::ReplicateResponse => match m.body { Body::AppendResponse { mode: Mode::Replicate, .. } => n.role == Role::Leader, _ => false },
        Receive::HeartbeatResponse => match m.body { Body::AppendResponse { mode: Mode::Heartbeat, .. } => n.role == Role::Leader, _ => false },
        Receive::FollowerRejectVote | Receive::RefuseVote | Receive::GrantVote | Receive::DeferVote => match m.body {
            Body::VoteRequest { last_term, last_index } => n.pending_vote is None && n.latest_config.contains(m.source) && match how {
                Receive::FollowerRejectVote => n.role == Role::Follower,
                Receive::RefuseVote => m.term < n.term || m.term >= n.term && !can_grant(n,m,last_term,last_index),
                Receive::GrantVote => m.term == n.term && can_grant(n,m,last_term,last_index),
                Receive::DeferVote => m.term > n.term && can_grant(n,m,last_term,last_index), _ => false,
            }, _ => false,
        },
        _ => match m.body {
            Body::AppendRequest { mode, prev, prev_term, .. } => (n.pending_vote is None || mode == Mode::Heartbeat) && match how {
                Receive::StaleAppend => m.term < n.term,
                Receive::RejectAppend => m.term >= n.term && !log_ok(n,prev,prev_term),
                Receive::AcceptAppend => m.term >= n.term && log_ok(n,prev,prev_term), _ => false,
            }, _ => false,
        },
    }
}
#[verifier::opaque]
pub open spec fn enabled(s: LState, c: Constants, a: Action) -> bool {
    match a {
        Action::Timeout(i) => c.servers.contains(i) && s.nodes[i].role != Role::Leader && s.nodes[i].latest_config.contains(i) && s.nodes[i].pending_vote is None,
        Action::BecomeLeader(i) => c.servers.contains(i) && s.nodes[i].role == Role::Candidate && quorum(s.nodes[i].granted.intersect(s.nodes[i].latest_config), s.nodes[i].latest_config),
        Action::CompleteVote(i) => c.servers.contains(i) && s.nodes[i].pending_vote is Some,
        Action::CheckLease(i) => c.servers.contains(i) && s.nodes[i].role == Role::Leader,
        Action::DiskBlock(i) => c.servers.contains(i) && !s.nodes[i].disk_blocked,
        Action::DiskUnblock(i) => c.servers.contains(i) && s.nodes[i].disk_blocked,
        Action::Crash(i) => c.servers.contains(i),
        Action::AdvanceCommit(i) => c.servers.contains(i) && s.nodes[i].role == Role::Leader && !agree_indices(s.nodes[i],i,c).is_empty(),
        Action::ClientRequest { i, value } => c.servers.contains(i) && c.values.contains(value) && s.nodes[i].role == Role::Leader && !s.nodes[i].disk_blocked,
        Action::ProposeConfig { i, member } => { let n=s.nodes[i]; c.servers.contains(i) && c.servers.contains(member) && n.role == Role::Leader && !n.disk_blocked
            && n.committed_config_index == n.latest_config_index && n.commit > 0 && n.log[n.commit-1].term == n.term
            && (!n.latest_config.contains(member) || n.latest_config.len() > 1) },
        Action::Replicate { i, j } => c.servers.contains(i) && c.servers.contains(j) && i != j && s.nodes[i].role == Role::Leader && !s.nodes[i].disk_blocked,
        Action::Heartbeat { i, j } => c.servers.contains(i) && c.servers.contains(j) && i != j && s.nodes[i].role == Role::Leader,
        Action::Receive { m, how } => receive_enabled(s,m,how), Action::Lose(m) => s.messages.count(m) > 0, Action::Stutter => true,
    }
}
#[verifier::opaque]
pub open spec fn receive(s: LState, c: Constants, m: Message, how: Receive) -> LState {
    let i=m.dest; let n=s.nodes[i];
    match how {
        Receive::DropStale => discard(s,m),
        Receive::FollowerRejectVote => reply(s,m,n.term,Body::VoteResponse { granted: false }),
        Receive::RefuseVote => replace(reply(s,m,max(n.term as int,m.term as int) as nat,Body::VoteResponse { granted: false }),i,
            if m.term > n.term { higher_term(n,m.term) } else { n }),
        Receive::GrantVote => replace(reply(s,m,n.term,Body::VoteResponse { granted: true }),i,
            LServer { voted_for: Some(m.source), persisted_vote_term: m.term, persisted_voted_for: Some(m.source), ..n }),
        Receive::DeferVote => replace(discard(s,m),i,LServer { term: m.term, voted_for: Some(m.source), role: Role::Follower,
            persisted_term: m.term, pending_vote: Some(Vote { candidate: m.source, term: m.term }), ..n }),
        Receive::VoteResponse => match m.body {
            Body::VoteResponse { granted } => replace(discard(s,m),i,if m.term > n.term { higher_term(n,m.term) }
                else { LServer { granted: if m.term == n.term && granted { n.granted.insert(m.source) } else { n.granted }, ..n } }), _ => s,
        },
        Receive::StaleAppend | Receive::RejectAppend | Receive::AcceptAppend => match m.body {
            Body::AppendRequest { mode, prev, prev_term, entries, commit } => {
                let updated = if m.term > n.term { higher_term(n,m.term) } else { LServer { term: m.term, role: Role::Follower, ..n } };
                if how == Receive::StaleAppend { reply(s,m,n.term,Body::AppendResponse { mode, success: false, matched: 0 }) }
                else if how == Receive::RejectAppend { replace(reply(s,m,m.term,Body::AppendResponse { mode, success: false, matched: 0 }),i,updated) }
                else {
                    let log=merge(n.log,prev,entries); let latest=last_config(log); let prior=previous_config(log);
                    let ci=if commit > n.commit { min(commit as int,log.len() as int) as nat } else { n.commit };
                    let cc=if latest <= ci { latest } else { max(prior as int,min(n.committed_config_index as int,latest as int)) as nat };
                    replace(reply(s,m,m.term,Body::AppendResponse { mode, success: true, matched: prev+entries.len() }),i,
                        LServer { log, commit: ci, latest_config: config_at(log,latest,c), latest_config_index: latest,
                            committed_config_index: cc, committed_config: config_at(log,cc,c), ..updated })
                }
            }, _ => s,
        },
        Receive::ReplicateResponse => match m.body {
            Body::AppendResponse { mode, success, matched } => replace(discard(s,m),i,
                if m.term > n.term { LServer { contacts: Set::empty(), ..higher_term(n,m.term) } }
                else if m.term == n.term { if success { LServer {
                    next_index: n.next_index.insert(m.source,max(n.next_index[m.source],matched+1)), matched: n.matched.insert(m.source,max(n.matched[m.source],matched)), contacts: n.contacts.insert(m.source), ..n }
                    } else { LServer { next_index: n.next_index.insert(m.source,max(1,n.next_index[m.source]-1)), ..n } }
                } else { n }), _ => s,
        },
        Receive::HeartbeatResponse => replace(discard(s,m),i,LServer { contacts: n.contacts.insert(m.source), ..n }),
    }
}
#[verifier::opaque]
pub open spec fn protocol_apply(s: LState, c: Constants, a: Action) -> LState {
    match a {
        Action::Timeout(i) => { let n=s.nodes[i]; let term=n.term+1;
            let messages = n.latest_config.remove(i).map(|j: int| Message { source: i, dest: j, term, body: Body::VoteRequest { last_term: log_term(n.log,n.log.len() as int), last_index: n.log.len() } });
            LState { messages: s.messages.add(Multiset::from_map(Map::new(messages, |m: Message| 1))), ..replace(s,i,LServer {
                term, role: Role::Candidate, voted_for: Some(i), granted: set![i], persisted_term: term, persisted_vote_term: term, persisted_voted_for: Some(i), ..n }) }
        },
        Action::CompleteVote(i) => { let n=s.nodes[i]; let v=n.pending_vote.unwrap();
            replace(send(s,Message { source: i,dest: v.candidate,term: v.term,body: Body::VoteResponse { granted: true } }),i,
                LServer { persisted_vote_term: v.term,persisted_voted_for: Some(v.candidate),pending_vote: None,..n }) },
        Action::BecomeLeader(i) => { let n=s.nodes[i]; replace(s,i,LServer { role: Role::Leader,
            next_index: Map::new(c.servers, |j: int| n.log.len() as int + 1),matched: Map::new(c.servers, |j: int| 0),contacts: Set::empty(),..n }) },
        Action::ClientRequest { i,value } => { let n=s.nodes[i]; replace(s,i,LServer { log: n.log.push(Entry { term: n.term,kind: EntryKind::Value,config: Set::empty(),value: Some(value) }),..n }) },
        Action::ProposeConfig { i,member } => { let n=s.nodes[i]; let config=if n.latest_config.contains(member) { n.latest_config.remove(member) } else { n.latest_config.insert(member) };
            replace(s,i,LServer { log: n.log.push(Entry { term: n.term,kind: EntryKind::Config,config,value: None }),latest_config: config,latest_config_index: n.log.len()+1,
                matched: Map::new(c.servers, |j: int| if config.contains(j) && n.latest_config.contains(j) { n.matched[j] } else { 0 }),..n }) },
        Action::Replicate { i,j } => { let n=s.nodes[i]; let prev=n.next_index[j]-1; send(s,Message { source: i,dest: j,term: n.term,
            body: Body::AppendRequest { mode: Mode::Replicate,prev,prev_term: log_term(n.log,prev),entries: if n.next_index[j] > n.log.len() { Seq::empty() } else { sub(n.log,n.next_index[j],n.log.len() as int) },commit: n.commit } }) },
        Action::Heartbeat { i,j } => send(s,Message { source: i,dest: j,term: s.nodes[i].term,
            body: Body::AppendRequest { mode: Mode::Heartbeat,prev: 0,prev_term: 0,entries: Seq::empty(),commit: 0 } }),
        Action::AdvanceCommit(i) => { let n=s.nodes[i]; let ci=maximum(agree_indices(n,i,c)) as nat;
            let cc=if n.latest_config_index <= ci { n.latest_config_index } else { n.committed_config_index }; let config=config_at(n.log,cc,c);
            replace(s,i,LServer { commit: ci,committed_config_index: cc,committed_config: config,role: if config.contains(i) { n.role } else { Role::Follower },..n }) },
        Action::CheckLease(i) => { let n=s.nodes[i]; replace(s,i,LServer { contacts: Set::empty(),role: if quorum(n.contacts.insert(i).intersect(n.latest_config),n.latest_config) { n.role } else { Role::Follower },..n }) },
        Action::DiskBlock(i) => replace(s,i,LServer { disk_blocked: true,..s.nodes[i] }),
        Action::DiskUnblock(i) => replace(s,i,LServer { disk_blocked: false,..s.nodes[i] }),
        Action::Crash(i) => { let n=s.nodes[i]; let last=last_config(n.log); let prev=previous_config(n.log);
            replace(s,i,LServer { role: Role::Follower,commit: 0,next_index: Map::new(c.servers, |j: int| 1),matched: Map::new(c.servers, |j: int| 0),granted: Set::empty(),contacts: Set::empty(),disk_blocked: false,
                term: n.persisted_term,voted_for: if n.persisted_vote_term == n.persisted_term { n.persisted_voted_for } else { None },pending_vote: None,
                latest_config: config_at(n.log,last,c),latest_config_index: last,committed_config_index: prev,committed_config: config_at(n.log,prev,c),..n }) },
        Action::Receive { m,how } => receive(s,c,m,how), Action::Lose(m) => discard(s,m), Action::Stutter => s,
    }
}
pub open spec fn apply(s: LState, c: Constants, a: Action) -> LState {
    let u=protocol_apply(s,c,a);
    LState { elections: s.elections.union(c.servers.filter(|i: int| s.nodes[i].role != Role::Leader && u.nodes[i].role == Role::Leader).map(|i: int| Event { server: i,term: u.nodes[i].term,entries: u.nodes[i].log })),
        commits: s.commits.union(c.servers.filter(|i: int| u.nodes[i].commit > s.nodes[i].commit).map(|i: int| Event { server: i,term: u.nodes[i].term,entries: sub(u.nodes[i].log,1,u.nodes[i].commit as int) })),..u }
}
#[verifier::opaque]
pub open spec fn next(s: LState,u: LState,c: Constants) -> bool { exists |a: Action| #[trigger] enabled(s,c,a) && u == apply(s,c,a) }
pub open spec fn prefix(a: Seq<Entry>,b: Seq<Entry>) -> bool { a.len() <= b.len() && a == sub(b,1,a.len() as int) }
pub open spec fn election_safety(s: LState) -> bool { forall |a: Event,b: Event| s.elections.contains(a) && s.elections.contains(b) && a.term == b.term ==> a.server == b.server }
pub open spec fn state_machine_safety(s: LState) -> bool { forall |a: Event,b: Event| s.commits.contains(a) && s.commits.contains(b) ==> prefix(a.entries,b.entries) || prefix(b.entries,a.entries) }
pub open spec fn committed_preserved(s: LState) -> bool { forall |a: Event| s.commits.contains(a) ==> prefix(a.entries,s.nodes[a.server].log) }
pub open spec fn log_matching(s: LState,c: Constants) -> bool { forall |a: int,b: int,k: int| c.servers.contains(a) && c.servers.contains(b) && 1 <= k <= s.nodes[a].log.len() && k <= s.nodes[b].log.len()
    && s.nodes[a].log[k-1].term == s.nodes[b].log[k-1].term ==> sub(s.nodes[a].log,1,k) == sub(s.nodes[b].log,1,k) }
pub open spec fn leader_completeness(s: LState) -> bool { forall |c: Event,e: Event,k: int| s.commits.contains(c) && s.elections.contains(e) && 1 <= k <= c.entries.len() && c.term < e.term
    ==> k <= e.entries.len() && (#[trigger] e.entries[k-1]) == (#[trigger] c.entries[k-1]) }
pub open spec fn pending_configs(n: LServer) -> Set<int> { Set::<int>::range(max(n.commit as int,n.committed_config_index as int)+1,n.log.len() as int+1).filter(|k: int| n.log[k-1].kind == EntryKind::Config) }
pub open spec fn configuration_safety(s: LState,c: Constants) -> bool { forall |i: int| c.servers.contains(i) && s.nodes[i].role == Role::Leader ==> pending_configs(s.nodes[i]).len() <= 1 }
} // verus!
