//! Concrete creation times for log entries and uninterrupted leadership terms.
//! All witnesses are extracted from the original behavior, without new guards.
use vstd::prelude::*;
use super::hashicorp::{*,sub};
use super::hashicorp_config as configs;
use super::hashicorp_types as types;
use super::hashicorp_votes as votes;
use super::temporal::Behavior;
verus! {
pub open spec fn step(b: Behavior<LState>,c: Constants,t: int) -> Action {
    choose |a: Action| #[trigger] enabled(b[t],c,a) && b[t+1] == apply(b[t],c,a)
}
pub proof fn step_valid(b: Behavior<LState>,c: Constants,t: int)
    requires configs::safety_spec(b,c),t >= 0
    ensures enabled(b[t],c,step(b,c,t)),b[t+1] == apply(b[t],c,step(b,c,t))
{ assert(next(b[t],b[t+1],c)); reveal(next); }
pub open spec fn rank(r: Role) -> nat { match r { Role::Candidate => 2,Role::Leader => 1,Role::Follower => 0 } }
pub proof fn local_step(s: LState,c: Constants,a: Action,i: int)
    requires s.nodes.dom() == c.servers,votes::node(s.nodes[i],i),enabled(s,c,a),c.servers.contains(i)
    ensures s.nodes[i].term <= apply(s,c,a).nodes[i].term,
        s.nodes[i].term == apply(s,c,a).nodes[i].term ==> rank(apply(s,c,a).nodes[i].role) <= rank(s.nodes[i].role),
        s.nodes[i].term == apply(s,c,a).nodes[i].term && s.nodes[i].role == Role::Leader && apply(s,c,a).nodes[i].role == Role::Leader
            ==> prefix(s.nodes[i].log,apply(s,c,a).nodes[i].log)
{
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
    assert(sub(s.nodes[i].log,1,s.nodes[i].log.len() as int) =~= s.nodes[i].log);
    if let Action::ClientRequest { i: writer,.. } | Action::ProposeConfig { i: writer,.. } = a {
        if writer == i { assert(sub(apply(s,c,a).nodes[i].log,1,s.nodes[i].log.len() as int) =~= s.nodes[i].log); }
    }
}
pub proof fn term_role_interval(b: Behavior<LState>,c: Constants,i: int,lo: int,hi: int)
    requires configs::safety_spec(b,c),c.servers.contains(i),0 <= lo <= hi
    ensures b[lo].nodes[i].term <= b[hi].nodes[i].term,
        b[lo].nodes[i].term == b[hi].nodes[i].term ==> rank(b[hi].nodes[i].role) <= rank(b[lo].nodes[i].role)
    decreases hi-lo
{
    if hi > lo {
        let p=hi-1; term_role_interval(b,c,i,lo,p); let g=votes::safety_at(b,c,p);
        assert(votes::node(g.state.nodes[i],i)); step_valid(b,c,p); local_step(b[p],c,step(b,c,p),i);
    }
}
pub proof fn continuous(b: Behavior<LState>,c: Constants,i: int,lo: int,hi: int)
    requires configs::safety_spec(b,c),c.servers.contains(i),0 <= lo <= hi,
        b[lo].nodes[i].role == Role::Leader,b[hi].nodes[i].role == Role::Leader,b[lo].nodes[i].term == b[hi].nodes[i].term
    ensures prefix(b[lo].nodes[i].log,b[hi].nodes[i].log),
        forall |t: int| lo <= t <= hi ==> (#[trigger] b[t]).nodes[i].role == Role::Leader && b[t].nodes[i].term == b[hi].nodes[i].term
    decreases hi-lo
{
    if hi > lo {
        let p=hi-1; term_role_interval(b,c,i,lo,p); term_role_interval(b,c,i,p,hi);
        assert(b[p].nodes[i].term == b[hi].nodes[i].term && b[p].nodes[i].role == Role::Leader);
        continuous(b,c,i,lo,p); let g=votes::safety_at(b,c,p); assert(votes::node(g.state.nodes[i],i));
        step_valid(b,c,p); local_step(b[p],c,step(b,c,p),i);
        assert(sub(b[hi].nodes[i].log,1,b[lo].nodes[i].log.len() as int) =~= b[lo].nodes[i].log);
    } else { assert(sub(b[hi].nodes[i].log,1,b[lo].nodes[i].log.len() as int) =~= b[lo].nodes[i].log); }
}
pub open spec fn segment(m: Message,h: Seq<Entry>) -> bool {
    m.body is AppendRequest && m.body->AppendRequest_prev >= 0
    && m.body->AppendRequest_prev_term == log_term(h,m.body->AppendRequest_prev)
    && (m.body->AppendRequest_entries.len() > 0 ==> {
        let p=m.body->AppendRequest_prev; p < h.len() && m.body->AppendRequest_entries == sub(h,p+1,h.len() as int)
    })
}
pub proof fn append_creation(s: LState,c: Constants,a: Action,m: Message)
    requires types::inductive(s,c),enabled(s,c,a),s.messages.count(m) == 0,apply(s,c,a).messages.count(m) > 0,m.body is AppendRequest
    ensures c.servers.contains(m.source),s.nodes[m.source].role == Role::Leader,s.nodes[m.source].term == m.term,
        segment(m,s.nodes[m.source].log),m.source != m.dest,m.body->AppendRequest_commit <= s.nodes[m.source].commit,
        m.body->AppendRequest_mode == Mode::Replicate ==> m.body->AppendRequest_prev == s.nodes[m.source].next_index[m.dest]-1,
        m.body->AppendRequest_mode == Mode::Replicate && m.body->AppendRequest_entries.len() == 0 ==> s.nodes[m.source].log.len() <= m.body->AppendRequest_prev,
        m.body->AppendRequest_mode == Mode::Heartbeat ==> m.body->AppendRequest_prev == 0 && m.body->AppendRequest_entries.len() == 0 && m.body->AppendRequest_commit == 0
{
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    if let Action::Timeout(i) = a {
        let q=s.nodes[i].latest_config.remove(i).map(|j: int| Message { source: i,dest: j,term: s.nodes[i].term+1,body: Body::VoteRequest {
            last_term: log_term(s.nodes[i].log,s.nodes[i].log.len() as int),last_index: s.nodes[i].log.len() } });
        assert(q.contains(m)); assert(false);
    }
    assert(types::node(s.nodes[m.source],c));
}
pub proof fn request_origin(b: Behavior<LState>,c: Constants,time: int,m: Message) -> (at: int)
    requires configs::safety_spec(b,c),time >= 0,b[time].messages.count(m) > 0,m.body is AppendRequest
    ensures 0 <= at < time,c.servers.contains(m.source),b[at].nodes[m.source].role == Role::Leader,b[at].nodes[m.source].term == m.term,
        segment(m,b[at].nodes[m.source].log),m.source != m.dest,m.body->AppendRequest_commit <= b[at].nodes[m.source].commit,
        m.body->AppendRequest_mode == Mode::Replicate ==> m.body->AppendRequest_prev == b[at].nodes[m.source].next_index[m.dest]-1,
        m.body->AppendRequest_mode == Mode::Replicate && m.body->AppendRequest_entries.len() == 0 ==> b[at].nodes[m.source].log.len() <= m.body->AppendRequest_prev,
        m.body->AppendRequest_mode == Mode::Heartbeat ==> m.body->AppendRequest_prev == 0 && m.body->AppendRequest_entries.len() == 0 && m.body->AppendRequest_commit == 0
    decreases time
{
    if time == 0 { broadcast use vstd::multiset::group_multiset_axioms; assert(false); 0 }
    else {
        let p=time-1;
        if b[p].messages.count(m) > 0 { request_origin(b,c,p,m) }
        else { types::safety_at(b,c,p); step_valid(b,c,p); append_creation(b[p],c,step(b,c,p),m); p }
    }
}
pub proof fn merged_entry(old: Seq<Entry>,prev: int,entries: Seq<Entry>,k: int)
    requires 0 <= prev <= old.len(),0 <= k < merge(old,prev,entries).len()
    ensures k < old.len() && merge(old,prev,entries)[k] == old[k]
        || prev <= k < prev+entries.len() && merge(old,prev,entries)[k] == entries[k-prev]
{
    types::first_mismatch(old,prev,entries,1); reveal(merge);
    let first=choose |j: int| 1 <= j <= entries.len()+1
        && (forall |q: int| 0 <= q < j-1 ==> prev+q < old.len() && old[prev+q].term == (#[trigger] entries[q]).term)
        && (j == entries.len()+1 || prev+j > old.len() || old[prev+j-1].term != (#[trigger] entries[j-1]).term);
    if first > 1 && first <= entries.len() { assert(prev+first-2 < old.len() && old[prev+first-2].term == entries[first-2].term); }
}
pub open spec fn creates(a: Action,i: int) -> bool {
    match a { Action::ClientRequest { i: writer,.. } | Action::ProposeConfig { i: writer,.. } => i == writer,_ => false }
}
pub open spec fn created(b: Behavior<LState>,c: Constants,t: int,i: int,k: int,e: Entry) -> bool {
    c.servers.contains(i) && creates(step(b,c,t),i) && b[t].nodes[i].role == Role::Leader && b[t].nodes[i].term == e.term
    && k == b[t].nodes[i].log.len() && b[t+1].nodes[i].log.len() == k+1 && b[t+1].nodes[i].log[k] == e
}
pub proof fn entry_origin(b: Behavior<LState>,c: Constants,time: int,i: int,k: int) -> (origin: (int,int))
    requires configs::safety_spec(b,c),time >= 0,c.servers.contains(i),0 <= k < b[time].nodes[i].log.len()
    ensures 0 <= origin.0 < time,created(b,c,origin.0,origin.1,k,b[time].nodes[i].log[k])
    decreases time
{
    if time == 0 { assert(false); (0,i) }
    else {
        let p=time-1; step_valid(b,c,p); let a=step(b,c,p); let s=b[p]; let u=b[time];
        let n=s.nodes[i]; let h=u.nodes[i].log;
        if k < n.log.len() && h[k] == n.log[k] { entry_origin(b,c,p,i,k) }
        else {
            reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
            if creates(a,i) {
                assert(k == n.log.len()); assert(created(b,c,p,i,k,h[k])); (p,i)
            } else {
                assert(a is Receive); let m=a->Receive_m; let how=a->Receive_how;
                assert(m.dest == i && how == Receive::AcceptAppend && m.body is AppendRequest);
                let sent=request_origin(b,c,p,m); let prev=m.body->AppendRequest_prev; let entries=m.body->AppendRequest_entries;
                assert(0 <= prev <= n.log.len()); merged_entry(n.log,prev,entries,k);
                assert(prev <= k < prev+entries.len() && h[k] == entries[k-prev]);
                assert(k < b[sent].nodes[m.source].log.len() && b[sent].nodes[m.source].log[k] == h[k]);
                entry_origin(b,c,sent,m.source,k)
            }
        }
    }
}
} // verus!
