//! Replication acknowledgments refer to actual append receptions.
//! A leader's next and matched indices stay within its own growing log.
use vstd::prelude::*;
use super::hashicorp::*;
use super::hashicorp_config as configs;
use super::hashicorp_types as types;
use super::hashicorp_history::{self as history,step};
use super::temporal::Behavior;
verus! {
pub open spec fn positive(m: Message) -> bool {
    match m.body { Body::AppendResponse { mode: Mode::Replicate,success: true,.. } => true,_ => false }
}
pub open spec fn response(request: Message,reply: Message) -> bool {
    request.body is AppendRequest && request.body->AppendRequest_mode == Mode::Replicate
    && request.source == reply.dest && request.dest == reply.source && request.term == reply.term
    && reply.body == Body::AppendResponse { mode: Mode::Replicate,success: true,matched: request.body->AppendRequest_prev+request.body->AppendRequest_entries.len() }
}
pub proof fn response_creation(s: LState,c: Constants,a: Action,m: Message) -> (request: Message)
    requires enabled(s,c,a),s.messages.count(m) == 0,apply(s,c,a).messages.count(m) > 0,positive(m)
    ensures a == (Action::Receive { m: request,how: Receive::AcceptAppend }),response(request,m),s.messages.count(request) > 0,
        apply(s,c,a).nodes[m.source].log == merge(s.nodes[m.source].log,request.body->AppendRequest_prev,request.body->AppendRequest_entries),
        apply(s,c,a).nodes[m.source].term == m.term,apply(s,c,a).nodes[m.source].role == Role::Follower
{
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    if let Action::Timeout(i) = a {
        let q=s.nodes[i].latest_config.remove(i).map(|j: int| Message { source: i,dest: j,term: s.nodes[i].term+1,body: Body::VoteRequest {
            last_term: log_term(s.nodes[i].log,s.nodes[i].log.len() as int),last_index: s.nodes[i].log.len() } });
        assert(q.contains(m)); assert(false);
    }
    assert(a is Receive); a->Receive_m
}
pub proof fn response_origin(b: Behavior<LState>,c: Constants,time: int,m: Message) -> (origin: (int,Message))
    requires configs::safety_spec(b,c),time >= 0,b[time].messages.count(m) > 0,positive(m)
    ensures 0 <= origin.0 < time,step(b,c,origin.0) == (Action::Receive { m: origin.1,how: Receive::AcceptAppend }),response(origin.1,m),
        b[origin.0].messages.count(origin.1) > 0,
        b[origin.0+1].nodes[m.source].log == merge(b[origin.0].nodes[m.source].log,origin.1.body->AppendRequest_prev,origin.1.body->AppendRequest_entries),
        b[origin.0+1].nodes[m.source].term == m.term,b[origin.0+1].nodes[m.source].role == Role::Follower
    decreases time
{
    if time == 0 { broadcast use vstd::multiset::group_multiset_axioms; assert(false); (0,m) }
    else {
        let p=time-1;
        if b[p].messages.count(m) > 0 { response_origin(b,c,p,m) }
        else { history::step_valid(b,c,p); let request=response_creation(b[p],c,step(b,c,p),m); (p,request) }
    }
}
pub open spec fn node(n: LServer,c: Constants) -> bool {
    n.role == Role::Leader ==>
        (forall |j: int| c.servers.contains(j) ==> 1 <= (#[trigger] n.next_index[j]) <= n.log.len()+1)
        && (forall |j: int| c.servers.contains(j) ==> 0 <= (#[trigger] n.matched[j]) <= n.log.len())
}
pub open spec fn incoming_bound(s: LState,a: Action,i: int) -> bool {
    match a {
        Action::Receive { m,how: Receive::ReplicateResponse } => m.dest == i && positive(m) && m.term == s.nodes[i].term ==>
            m.body->AppendResponse_matched <= s.nodes[i].log.len(),
        _ => true,
    }
}
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires types::inductive(s,c),node(s.nodes[i],c),enabled(s,c,a),c.servers.contains(i),incoming_bound(s,a,i)
    ensures node(apply(s,c,a).nodes[i],c)
{
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
    let n=s.nodes[i]; let u=apply(s,c,a).nodes[i];
    assert(types::node(n,c));
    assert forall |j: int| u.role == Role::Leader && c.servers.contains(j) implies
        1 <= (#[trigger] u.next_index[j]) <= u.log.len()+1 by {
        if n.role == Role::Leader { assert(1 <= n.next_index[j] <= n.log.len()+1); }
    }
    assert forall |j: int| u.role == Role::Leader && c.servers.contains(j) implies
        0 <= (#[trigger] u.matched[j]) <= u.log.len() by {
        if n.role == Role::Leader { assert(0 <= n.matched[j] <= n.log.len()); }
    }
}
pub proof fn bounds_at(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires configs::safety_spec(b,c),time >= 0,c.servers.contains(i)
    ensures node(b[time].nodes[i],c)
    decreases time
{
    if time > 0 {
        let p=time-1; bounds_at(b,c,p,i); history::step_valid(b,c,p); types::safety_at(b,c,p); let a=step(b,c,p);
        if let Action::Receive { m,how: Receive::ReplicateResponse } = a {
            if m.dest == i && positive(m) && m.term == b[p].nodes[i].term {
                reveal(enabled); reveal(receive_enabled);
                let ack=response_origin(b,c,p,m); let request=ack.1; let sent=history::request_origin(b,c,ack.0,request);
                assert(request.source == i); bounds_at(b,c,sent,i);
                assert(c.servers.contains(m.source)) by { assert(types::message(m,c)); }
                assert(1 <= b[sent].nodes[i].next_index[m.source] <= b[sent].nodes[i].log.len()+1);
                assert(m.body->AppendResponse_matched <= b[sent].nodes[i].log.len());
                history::continuous(b,c,i,sent,p);
            }
        }
        assert(incoming_bound(b[p],a,i)); preserve_node(b[p],c,a,i);
    }
}
pub proof fn request_bound(b: Behavior<LState>,c: Constants,time: int,m: Message) -> (at: int)
    requires configs::safety_spec(b,c),time >= 0,b[time].messages.count(m) > 0,m.body is AppendRequest
    ensures 0 <= at < time,c.servers.contains(m.source),b[at].nodes[m.source].role == Role::Leader,b[at].nodes[m.source].term == m.term,
        history::segment(m,b[at].nodes[m.source].log),m.source != m.dest,
        0 <= m.body->AppendRequest_prev <= b[at].nodes[m.source].log.len(),
        m.body->AppendRequest_prev+m.body->AppendRequest_entries.len() <= b[at].nodes[m.source].log.len(),
        m.body->AppendRequest_mode == Mode::Replicate ==> m.body->AppendRequest_prev+m.body->AppendRequest_entries.len() == b[at].nodes[m.source].log.len(),
        m.body->AppendRequest_commit <= b[at].nodes[m.source].commit,
        m.body->AppendRequest_mode == Mode::Heartbeat ==> m.body->AppendRequest_entries.len() == 0 && m.body->AppendRequest_commit == 0
{
    let at=history::request_origin(b,c,time,m); bounds_at(b,c,at,m.source); types::safety_at(b,c,time); assert(types::message(m,c));
    assert(1 <= b[at].nodes[m.source].next_index[m.dest] <= b[at].nodes[m.source].log.len()+1); at
}
pub proof fn merge_length(old: Seq<Entry>,prev: int,entries: Seq<Entry>)
    requires 0 <= prev <= old.len()
    ensures prev+entries.len() <= merge(old,prev,entries).len()
{
    types::first_mismatch(old,prev,entries,1); reveal(merge);
    let first=choose |j: int| 1 <= j <= entries.len()+1
        && (forall |q: int| 0 <= q < j-1 ==> prev+q < old.len() && old[prev+q].term == (#[trigger] entries[q]).term)
        && (j == entries.len()+1 || prev+j > old.len() || old[prev+j-1].term != (#[trigger] entries[j-1]).term);
    if first == entries.len()+1 && entries.len() > 0 {
        assert(prev+entries.len()-1 < old.len() && old[prev+entries.len()-1].term == entries[entries.len()-1].term);
    }
}
pub proof fn merged_terms(old: Seq<Entry>,prev: int,entries: Seq<Entry>,k: int)
    requires 0 <= prev <= old.len(),0 <= k < entries.len()
    ensures (merge(old,prev,entries)[prev+k]).term == entries[k].term
{
    types::first_mismatch(old,prev,entries,1); reveal(merge);
    let first=choose |j: int| 1 <= j <= entries.len()+1
        && (forall |q: int| 0 <= q < j-1 ==> prev+q < old.len() && old[prev+q].term == (#[trigger] entries[q]).term)
        && (j == entries.len()+1 || prev+j > old.len() || old[prev+j-1].term != (#[trigger] entries[j-1]).term);
    if k < first-1 { assert(prev+k < old.len() && old[prev+k].term == entries[k].term); }
}
pub proof fn acknowledgment_bound(b: Behavior<LState>,c: Constants,time: int,m: Message) -> (at: int)
    requires configs::safety_spec(b,c),time >= 0,b[time].messages.count(m) > 0,positive(m)
    ensures 0 <= at < time,0 <= m.body->AppendResponse_matched <= b[at+1].nodes[m.source].log.len(),
        b[at+1].nodes[m.source].term == m.term,b[at+1].nodes[m.source].role == Role::Follower
{
    let origin=response_origin(b,c,time,m); let at=origin.0; let request=origin.1;
    history::step_valid(b,c,at); types::safety_at(b,c,at); assert(types::message(request,c));
    reveal(enabled); reveal(receive_enabled);
    merge_length(b[at].nodes[m.source].log,request.body->AppendRequest_prev,request.body->AppendRequest_entries);
    at
}
} // verus!
