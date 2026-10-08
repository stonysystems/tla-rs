//! Handwritten etcd_raftModel. Network and pending messages are bags.
//! The benchmark never changes its initial configuration or learners and only
//! appends ValueEntry(0); those constant fields are represented by Constants.
//! Log entries therefore need only their term. Disk state and Ready remain explicit.
use vstd::prelude::*;
use vstd::multiset::Multiset;
verus! {
pub enum Role { Follower, Candidate, Leader }
pub enum Mode { App, Heartbeat, Snapshot }
pub enum Body {
    VoteRequest { last_term: nat, last_index: nat }, VoteResponse { granted: bool },
    AppendRequest { mode: Mode, prev: nat, prev_term: nat, entries: Seq<nat>, commit: nat },
    AppendResponse { mode: Mode, success: bool, matched: nat },
}
pub struct Message { pub source: int, pub dest: int, pub term: nat, pub body: Body }
pub struct Ballot { pub voter: int, pub term: nat, pub candidate: int }
pub struct Disk { pub term: nat, pub voted_for: Option<int>, pub log: Seq<nat>, pub commit: nat }
pub struct LServer {
    pub term: nat, pub role: Role, pub voted_for: Option<int>, pub log: Seq<nat>, pub commit: nat,
    pub responded: Set<int>, pub granted: Set<int>, pub matched: IMap<int, nat>, pub disk: Disk,
}
pub struct Constants { pub servers: ISet<int>, pub voters: Set<int> }
pub struct LState {
    pub nodes: IMap<int, LServer>, pub messages: Multiset<Message>, pub pending: Multiset<Message>,
    // Passive proof history. It records positive responses released by Ready,
    // appears in no guard, and has no effect on the protocol's other fields.
    pub votes: Set<Ballot>,
}
pub open spec fn valid_constants(c: Constants) -> bool { c.voters.to_iset().subset_of(c.servers) }
pub open spec fn quorum(q: Set<int>, c: Constants) -> bool { q.subset_of(c.voters) && 2*q.len() > c.voters.len() }
pub open spec fn agreed_indices(n: LServer,c: Constants) -> Set<int> {
    Set::<int>::range(1, n.log.len() as int + 1).filter(|index: int| quorum(c.voters.filter(|k: int| n.matched[k] >= index), c))
}
pub open spec fn last_term(log: Seq<nat>) -> nat { if log.len() == 0 { 0 } else { log.last() } }
pub open spec fn sub(log: Seq<nat>, first: int, last: int) -> Seq<nat> {
    Seq::new(if last < first { 0 } else { (last-first+1) as nat }, |i: int| log[i+first-1])
}
pub open spec fn prefix(a: Seq<nat>, b: Seq<nat>) -> bool { a.len() <= b.len() && a == sub(b, 1, a.len() as int) }
pub open spec fn max(a: nat, b: nat) -> nat { if a > b { a } else { b } }
pub open spec fn min(a: nat, b: nat) -> nat { if a < b { a } else { b } }
#[verifier::opaque]
pub open spec fn maximum(s: Set<int>) -> int { choose |x: int| s.contains(x) && forall |y: int| s.contains(y) ==> y <= x }
pub open spec fn initial(c: Constants) -> LState {
    LState { votes: Set::empty(), messages: Multiset::empty(), pending: Multiset::empty(), nodes: IMap::new(|i: int| c.servers.contains(i), |i: int| LServer {
        term: 0, role: Role::Follower, voted_for: None, log: Seq::empty(), commit: 0,
        responded: Set::empty(), granted: Set::empty(), matched: IMap::new(|j: int| c.servers.contains(j), |j: int| 0),
        disk: Disk { term: 0, voted_for: None, log: Seq::empty(), commit: 0 },
    }) }
}
pub open spec fn positive(m: Message) -> bool { m.body == Body::VoteResponse { granted: true } }
pub open spec fn ballot(m: Message) -> Ballot { Ballot { voter: m.source, term: m.term, candidate: m.dest } }
pub open spec fn released_votes(s: LState, i: int) -> Set<Ballot> {
    s.pending.dom().filter(|m: Message| m.source == i && positive(m)).map(|m: Message| ballot(m))
}
pub open spec fn replace(s: LState, i: int, n: LServer) -> LState { LState { nodes: s.nodes.insert(i, n), ..s } }
pub open spec fn send(s: LState, m: Message) -> LState { LState { pending: s.pending.insert(m), ..s } }
pub open spec fn discard(s: LState, m: Message) -> LState { LState { messages: s.messages.remove(m), ..s } }
pub open spec fn reply(s: LState, m: Message, body: Body) -> LState {
    send(discard(s, m), Message { source: m.dest, dest: m.source, term: s.nodes[m.dest].term, body })
}
pub open spec fn follower(n: LServer, term: nat) -> LServer {
    LServer { term, role: Role::Follower, voted_for: if term != n.term { None } else { n.voted_for }, ..n }
}
pub open spec fn log_ok(n: LServer, prev: nat, term: nat) -> bool {
    prev == 0 || 0 < prev <= n.log.len() && n.log[prev-1] == term
}
pub open spec fn no_conflict(n: LServer, index: nat, entries: Seq<nat>) -> bool {
    index <= n.log.len()+1
    && forall |k: int| 0 <= k < entries.len() && index+k <= n.log.len() ==> n.log[index+k-1] == entries[k]
}
pub open spec fn up_to_date(n: LServer, term: nat, len: nat) -> bool {
    term > last_term(n.log) || term == last_term(n.log) && len >= n.log.len()
}
pub open spec fn grant(n: LServer, m: Message, term: nat, len: nat) -> bool {
    m.term == n.term && up_to_date(n, term, len) && (n.voted_for == None || n.voted_for == Some(m.source))
}
pub enum Receive { UpdateTerm, VoteRequest, VoteResponse, RejectAppend, ReturnToFollower,
    AppendDone, AppendConflict, AppendExtend, AppendResponse, DropStale }
pub enum Action {
    Restart(int), Timeout(int), RequestVote { i: int, j: int }, BecomeLeader(int), ClientRequest(int),
    AdvanceCommit(int), Append { i: int, j: int, begin: nat, end: nat }, SelfAppend(int),
    Heartbeat { i: int, j: int }, Snapshot { i: int, j: int, index: nat }, Ready(int), StepDown(int),
    Receive { m: Message, how: Receive }, Duplicate(Message), Drop(Message), Stutter,
}
#[verifier::opaque]
pub open spec fn receive_enabled(s: LState, m: Message, how: Receive) -> bool {
    let n = s.nodes[m.dest];
    s.messages.count(m) > 0 && match how {
        Receive::UpdateTerm => m.term > n.term,
        Receive::DropStale => m.term < n.term && (m.body is VoteResponse || m.body is AppendResponse),
        Receive::VoteRequest => m.body is VoteRequest && m.term <= n.term,
        Receive::VoteResponse => m.body is VoteResponse && m.term == n.term,
        Receive::AppendResponse => m.body is AppendResponse && m.term == n.term,
        _ => match m.body {
            Body::AppendRequest { mode, prev, prev_term, entries, commit } => {
                let index = prev+1;
                m.term <= n.term && match how {
                    Receive::RejectAppend => m.term < n.term || m.term == n.term && n.role == Role::Follower && !log_ok(n, prev, prev_term),
                    Receive::ReturnToFollower => m.term == n.term && n.role == Role::Candidate,
                    _ => m.term == n.term && n.role == Role::Follower && log_ok(n, prev, prev_term) && match how {
                        Receive::AppendDone => index <= n.commit || index > n.commit && (entries.len() == 0 || prev+entries.len() <= n.log.len() && no_conflict(n, index, entries)),
                        Receive::AppendConflict => entries.len() > 0 && index > n.commit && !no_conflict(n, index, entries),
                        Receive::AppendExtend => entries.len() > 0 && index > n.commit && no_conflict(n, index, entries),
                        _ => false,
                    },
                }
            }, _ => false,
        },
    }
}
#[verifier::opaque]
pub open spec fn enabled(s: LState, c: Constants, a: Action) -> bool {
    match a {
        Action::Restart(i) | Action::Ready(i) => c.servers.contains(i),
        Action::Timeout(i) => c.servers.contains(i) && c.voters.contains(i) && s.nodes[i].role != Role::Leader,
        Action::RequestVote { i, j } => c.servers.contains(i) && c.servers.contains(j) && s.nodes[i].role == Role::Candidate && c.voters.contains(j) && !s.nodes[i].responded.contains(j),
        Action::BecomeLeader(i) => c.servers.contains(i) && s.nodes[i].role == Role::Candidate && quorum(s.nodes[i].granted, c),
        Action::ClientRequest(i) | Action::AdvanceCommit(i) | Action::SelfAppend(i) => c.servers.contains(i) && s.nodes[i].role == Role::Leader,
        Action::Append { i, j, begin, end } => c.servers.contains(i) && c.servers.contains(j) && i != j && c.voters.contains(j) && s.nodes[i].role == Role::Leader
            && s.nodes[i].matched[j]+1 <= begin <= end <= s.nodes[i].log.len()+1,
        Action::Heartbeat { i, j } => c.servers.contains(i) && c.servers.contains(j) && i != j && c.voters.contains(j) && s.nodes[i].role == Role::Leader,
        Action::Snapshot { i, j, index } => c.servers.contains(i) && c.servers.contains(j) && i != j && c.voters.contains(j) && s.nodes[i].role == Role::Leader && 1 <= index <= s.nodes[i].commit,
        Action::StepDown(i) => c.servers.contains(i) && s.nodes[i].role != Role::Follower,
        Action::Receive { m, how } => receive_enabled(s, m, how),
        Action::Duplicate(m) | Action::Drop(m) => s.messages.count(m) == 1,
        Action::Stutter => true,
    }
}
pub open spec fn send_append(s: LState, i: int, j: int, mode: Mode, begin: nat, end: nat) -> LState {
    let n = s.nodes[i]; let prev = (begin-1) as nat; let last = min(n.log.len(), (end-1) as nat);
    send(s, Message { source: i, dest: j, term: n.term,
        body: Body::AppendRequest { mode, prev, prev_term: if 0 < prev <= n.log.len() { n.log[prev-1] } else { 0 },
            entries: sub(n.log, begin as int, last as int), commit: if mode == Mode::Heartbeat { min(n.commit, n.matched[j]) } else { min(n.commit, last) } } })
}
#[verifier::opaque]
pub open spec fn receive(s: LState, m: Message, how: Receive) -> LState {
    let i = m.dest; let j = m.source; let n = s.nodes[i];
    match how {
        Receive::UpdateTerm => replace(s, i, follower(n, m.term)),
        Receive::DropStale => discard(s, m),
        Receive::ReturnToFollower => replace(s, i, LServer { role: Role::Follower, ..n }),
        Receive::VoteRequest => match m.body {
            Body::VoteRequest { last_term, last_index } => {
                let yes = grant(n, m, last_term, last_index);
                replace(reply(s, m, Body::VoteResponse { granted: yes }), i,
                    LServer { voted_for: if yes { Some(j) } else { n.voted_for }, ..n })
            }, _ => s,
        },
        Receive::VoteResponse => match m.body {
            Body::VoteResponse { granted } => replace(discard(s, m), i,
                LServer { responded: n.responded.insert(j), granted: if granted { n.granted.insert(j) } else { n.granted }, ..n }), _ => s,
        },
        Receive::RejectAppend => reply(s, m, Body::AppendResponse { mode: Mode::App, success: false, matched: 0 }),
        Receive::AppendResponse => match m.body {
            Body::AppendResponse { mode, success, matched } => replace(discard(s, m), i,
                LServer { matched: if success { n.matched.insert(j, max(n.matched[j], matched)) } else { n.matched }, ..n }), _ => s,
        },
        _ => match m.body {
            Body::AppendRequest { mode, prev, prev_term, entries, commit } => {
                let index = prev+1;
                match how {
                    Receive::AppendDone => {
                        let ci = if index <= n.commit { if mode == Mode::Heartbeat { max(n.commit, commit) } else { n.commit } }
                            else { max(n.commit, min(commit, prev+entries.len())) };
                        replace(reply(s, m, Body::AppendResponse { mode, success: true,
                            matched: if mode == Mode::Heartbeat || index > n.commit { prev+entries.len() } else { n.commit } }), i,
                            LServer { commit: ci, ..n })
                    },
                    Receive::AppendConflict => replace(s, i, LServer { log: sub(n.log, 1, n.log.len()-1), ..n }),
                    Receive::AppendExtend => replace(s, i, LServer { log: n.log + sub(entries, n.log.len()-index+2, entries.len() as int), ..n }),
                    _ => s,
                }
            }, _ => s,
        },
    }
}
#[verifier::opaque]
pub open spec fn apply(s: LState, c: Constants, a: Action) -> LState {
    match a {
        Action::Restart(i) => { let n = s.nodes[i]; LState {
            pending: s.pending.filter(|m: Message| m.source != i),
            ..replace(s, i, LServer { term: n.disk.term, role: Role::Follower, voted_for: n.disk.voted_for, log: n.disk.log, commit: n.disk.commit,
                responded: Set::empty(), granted: Set::empty(), matched: IMap::new(|j: int| c.servers.contains(j), |j: int| 0), ..n }) } },
        Action::Timeout(i) => { let n = s.nodes[i]; replace(s, i, LServer { role: Role::Candidate, term: n.term+1, voted_for: Some(i), responded: Set::empty(), granted: Set::empty(), ..n }) },
        Action::RequestVote { i, j } => send(s, Message { source: i, dest: j, term: s.nodes[i].term,
            body: if i == j { Body::VoteResponse { granted: true } } else { Body::VoteRequest { last_term: last_term(s.nodes[i].log), last_index: s.nodes[i].log.len() } } }),
        Action::BecomeLeader(i) => { let n = s.nodes[i]; replace(s, i, LServer { role: Role::Leader,
            matched: IMap::new(|j: int| c.servers.contains(j), |j: int| if j == i { n.log.len() } else { 0 }), ..n }) },
        Action::ClientRequest(i) => { let n = s.nodes[i]; replace(s, i, LServer { log: n.log.push(n.term), ..n }) },
        Action::AdvanceCommit(i) => { let n = s.nodes[i];
            let agreed = agreed_indices(n,c);
            let ci = if !agreed.is_empty() && n.log[maximum(agreed)-1] == n.term { maximum(agreed) as nat } else { n.commit };
            replace(s, i, LServer { commit: max(n.commit, ci), ..n })
        },
        Action::Append { i, j, begin, end } => send_append(s, i, j, Mode::App, begin, end),
        Action::Heartbeat { i, j } => send_append(s, i, j, Mode::Heartbeat, 1, 1),
        Action::Snapshot { i, j, index } => send_append(s, i, j, Mode::Snapshot, 1, index+1),
        Action::SelfAppend(i) => send(s, Message { source: i, dest: i, term: s.nodes[i].term,
            body: Body::AppendResponse { mode: Mode::App, success: true, matched: s.nodes[i].log.len() } }),
        Action::Ready(i) => { let n = s.nodes[i]; LState {
            votes: s.votes.union(released_votes(s, i)),
            messages: s.messages.add(s.pending.filter(|m: Message| m.source == i)), pending: s.pending.filter(|m: Message| m.source != i),
            ..replace(s, i, LServer { disk: Disk { term: n.term, voted_for: n.voted_for, log: n.log, commit: n.commit }, ..n }) } },
        Action::StepDown(i) => replace(s, i, follower(s.nodes[i], s.nodes[i].term)),
        Action::Receive { m, how } => receive(s, m, how),
        Action::Duplicate(m) => LState { messages: s.messages.insert(m), ..s },
        Action::Drop(m) => discard(s, m), Action::Stutter => s,
    }
}
#[verifier::opaque]
pub open spec fn next(s: LState, u: LState, c: Constants) -> bool {
    exists |a: Action| #[trigger] enabled(s, c, a) && u == apply(s, c, a)
}
pub open spec fn committed(n: LServer) -> Seq<nat> { sub(n.log, 1, n.commit as int) }
pub open spec fn log_inv(s: LState, c: Constants) -> bool {
    forall |i: int, j: int| c.servers.contains(i) && c.servers.contains(j) ==> prefix(committed(s.nodes[i]), committed(s.nodes[j])) || prefix(committed(s.nodes[j]), committed(s.nodes[i]))
}
pub open spec fn more_than_one_leader(s: LState, c: Constants) -> bool {
    forall |i: int, j: int| #![trigger c.servers.contains(i), c.servers.contains(j)] c.servers.contains(i) && c.servers.contains(j) && s.nodes[i].role == Role::Leader && s.nodes[j].role == Role::Leader && s.nodes[i].term == s.nodes[j].term ==> i == j
}
pub open spec fn term_positions(n: LServer, term: nat) -> Set<int> {
    Set::<int>::range(1, n.log.len() as int + 1).filter(|k: int| n.log[k-1] == term)
}
pub open spec fn max_term_index(n: LServer, term: nat) -> int {
    let positions = term_positions(n,term);
    if positions.is_empty() { 0 } else { maximum(positions) }
}
pub open spec fn election_safety(s: LState, c: Constants) -> bool {
    forall |i: int, j: int| c.servers.contains(i) && c.servers.contains(j) && s.nodes[i].role == Role::Leader ==> max_term_index(s.nodes[i], s.nodes[i].term) >= max_term_index(s.nodes[j], s.nodes[i].term)
}
pub open spec fn log_matching(s: LState, c: Constants) -> bool {
    forall |i: int, j: int, k: int| #![trigger c.servers.contains(i), sub(s.nodes[j].log, 1, k)] #![trigger c.servers.contains(j), sub(s.nodes[i].log, 1, k)] c.servers.contains(i) && c.servers.contains(j) && 1 <= k <= s.nodes[i].log.len() && k <= s.nodes[j].log.len()
        && s.nodes[i].log[k-1] == s.nodes[j].log[k-1] ==> sub(s.nodes[i].log, 1, k) == sub(s.nodes[j].log, 1, k)
}
pub open spec fn quorum_log(s: LState, c: Constants) -> bool {
    forall |i: int, q: Set<int>| c.servers.contains(i) && quorum(q, c) ==> exists |j: int| #![trigger q.contains(j)] q.contains(j) && prefix(committed(s.nodes[i]), s.nodes[j].log)
}
pub open spec fn more_up_to_date(s: LState, c: Constants) -> bool {
    forall |i: int, j: int| #![trigger prefix(committed(s.nodes[j]), s.nodes[i].log)] c.servers.contains(i) && c.servers.contains(j) && up_to_date(s.nodes[j], last_term(s.nodes[i].log), s.nodes[i].log.len()) ==> prefix(committed(s.nodes[j]), s.nodes[i].log)
}
pub open spec fn leader_completeness(s: LState, c: Constants) -> bool {
    forall |i: int, l: int, k: int| c.servers.contains(i) && c.servers.contains(l) && 0 <= k < s.nodes[i].commit
        && s.nodes[l].role == Role::Leader && s.nodes[l].term > (#[trigger] s.nodes[i].log[k]) ==> (#[trigger] s.nodes[l].log[k]) == s.nodes[i].log[k]
}
pub open spec fn committed_is_durable(s: LState, c: Constants) -> bool {
    forall |i: int| #![trigger c.servers.contains(i)] c.servers.contains(i) && s.nodes[i].role == Role::Leader ==> s.nodes[i].commit <= s.nodes[i].disk.log.len()
}
} // verus!
