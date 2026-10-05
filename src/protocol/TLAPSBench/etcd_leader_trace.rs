//! Same-term leader observations belong to one continuous leadership interval.
use vstd::prelude::*;
use super::etcd::*;
use super::etcd_election as election;
use super::etcd_origins as origins;
use super::etcd_logs as logs;
use super::etcd_vote_witness as votes;
use super::etcd_match_witness as matches;
use super::etcd_transmissions as events;
use super::temporal::Behavior;
verus! {
pub proof fn continuous(b: Behavior<LState>,c: Constants,i: int,lo: int,hi: int)
    requires election::safety_spec(b,c),c.servers.contains(i),0 <= lo <= hi,
        b[lo].nodes[i].role == Role::Leader,b[hi].nodes[i].role == Role::Leader,b[lo].nodes[i].term == b[hi].nodes[i].term
    ensures matches::leading(b,i,b[hi].nodes[i].term,lo,hi),logs::prefix_of(b[lo].nodes[i].log,b[hi].nodes[i].log)
{
    let t=b[hi].nodes[i].term; let start=matches::epoch_start(b,c,hi,i);
    origins::safety_at(b,c,lo); origins::leader_persisted(b[lo],c,i);
    if start >= lo { votes::persisted_candidate_interval(b,c,i,t,lo,start); assert(false); }
    assert(matches::leading(b,i,t,lo,hi)); matches::leader_log_interval(b,c,i,t,lo,hi);
}
pub proof fn append_creation(s: LState,c: Constants,a: Action,m: Message)
    requires enabled(s,c,a),s.pending.count(m) == 0,apply(s,c,a).pending.count(m) > 0,m.body is AppendRequest
    ensures c.servers.contains(m.source),s.nodes[m.source].role == Role::Leader,s.nodes[m.source].term == m.term,
        logs::segment(m,s.nodes[m.source].log),
        m.source != m.dest,m.body->AppendRequest_commit <= s.nodes[m.source].commit,
        m.body->AppendRequest_mode == Mode::Heartbeat ==> m.body->AppendRequest_prev == 0 && m.body->AppendRequest_entries.len() == 0
            && m.body->AppendRequest_commit <= s.nodes[m.source].matched[m.dest]
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
}
pub proof fn request_origin(b: Behavior<LState>,c: Constants,k: int,m: Message) -> (j: int)
    requires election::safety_spec(b,c),k >= 0,b[k].messages.count(m) > 0,m.body is AppendRequest
    ensures 0 <= j < k,c.servers.contains(m.source),b[j].nodes[m.source].role == Role::Leader,b[j].nodes[m.source].term == m.term,
        logs::segment(m,b[j].nodes[m.source].log),
        m.source != m.dest,m.body->AppendRequest_commit <= b[j].nodes[m.source].commit,
        m.body->AppendRequest_mode == Mode::Heartbeat ==> m.body->AppendRequest_prev == 0 && m.body->AppendRequest_entries.len() == 0
            && m.body->AppendRequest_commit <= b[j].nodes[m.source].matched[m.dest]
{
    let release=events::release_origin(b,c,k,m); let create=events::pending_origin(b,c,release,m);
    events::step_valid(b,c,create); assert(b[create+1].pending.count(m) > 0);
    append_creation(b[create],c,events::step(b,c,create),m); create
}
pub proof fn source_still_leads(b: Behavior<LState>,c: Constants,time: int,receive: int,m: Message)
    requires election::safety_spec(b,c),0 <= receive <= time,b[receive].messages.count(m) > 0,m.body is AppendRequest,
        b[time].nodes[m.source].role == Role::Leader,b[time].nodes[m.source].term == m.term
    ensures b[receive].nodes[m.source].role == Role::Leader,b[receive].nodes[m.source].term == m.term,
        logs::prefix_of(b[receive].nodes[m.source].log,b[time].nodes[m.source].log)
{
    let create=request_origin(b,c,receive,m); continuous(b,c,m.source,create,time);
    assert(b[receive].nodes[m.source].role == Role::Leader && b[receive].nodes[m.source].term == m.term);
    continuous(b,c,m.source,receive,time);
}
} // verus!
