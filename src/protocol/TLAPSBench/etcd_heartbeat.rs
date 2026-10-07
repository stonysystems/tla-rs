//! Heartbeat match indices certify retained prefixes or durable commit counters.
use vstd::prelude::*;
use super::etcd::{*,sub};
use super::etcd_election as election;
use super::etcd_logs as logs;
use super::etcd_sent as sent;
use super::etcd_acknowledgments as acks;
use super::etcd_ack_prefixes as prefixes;
use super::etcd_match_witness as matches;
use super::etcd_leader_trace as leaders;
use super::etcd_transmissions as events;
use super::etcd_persistence as persistence;
use super::etcd_history_trace as trace;
use super::etcd_commit_history::Decision;
use super::etcd_stable_prefixes as stable;
use super::temporal::Behavior;
verus! {
pub proof fn peer_ack(b: Behavior<LState>,c: Constants,time: int,i: int,j: int,k: int) -> (w: (int,int,int,Message))
    requires election::safety_spec(b,c),time >= 0,c.servers.contains(i),c.servers.contains(j),i != j,
        b[time].nodes[i].role == Role::Leader,k > 0,b[time].nodes[i].matched[j] >= k
    ensures 0 <= w.0 < w.1 < w.2 < time,w.3.source == j,w.3.dest == i,w.3.term == b[time].nodes[i].term,
        acks::success(w.3),w.3.body->AppendResponse_matched >= k,
        events::step(b,c,w.1) == Action::Ready(j),b[w.0].pending.count(w.3) == 0,
        forall |r: int| w.0 < r <= w.1 ==> #[trigger] b[r].pending.count(w.3) > 0
{
    let start=matches::epoch_start(b,c,time,i); events::step_valid(b,c,start); reveal(apply);
    assert(b[start+1].nodes[i].matched[j] == 0);
    let x=matches::match_since(b,c,i,j,k,b[time].nodes[i].term,start+1,time);
    let release=events::release_origin(b,c,x.0,x.1); let create=events::pending_origin(b,c,release,x.1);
    (create,release,x.0,x.1)
}
pub proof fn prefix_or_counter(b: Behavior<LState>,c: Constants,time: int,create: int,m: Message,k: int)
    requires election::safety_spec(b,c),0 <= create < time,c.servers.contains(m.dest),
        b[time].nodes[m.dest].role == Role::Leader,b[time].nodes[m.dest].term == m.term,
        0 < k <= b[time].nodes[m.dest].log.len(),acks::success(m),m.body->AppendResponse_matched >= k,
        b[create].pending.count(m) == 0,b[create+1].pending.count(m) > 0
    ensures logs::prefix_of(sub(b[time].nodes[m.dest].log,1,k),b[create+1].nodes[m.source].log)
        || b[create].nodes[m.source].commit >= k
{
    events::step_valid(b,c,create); trace::valid(b,c,create); let s=b[create]; let a=events::step(b,c,create);
    prefixes::success_creation(s,c,a,m);
    if a == Action::SelfAppend(m.source) {
        leaders::continuous(b,c,m.source,create,time); prefixes::shorten(s.nodes[m.source].log,b[time].nodes[m.dest].log,k);
    } else {
        let p=choose |p: Message| a == (Action::Receive { m: p,how: Receive::AppendDone })
            && p.body is AppendRequest && p.source == m.dest && p.dest == m.source && p.term == m.term
            && m.body->AppendResponse_mode == p.body->AppendRequest_mode
            && m.body->AppendResponse_matched == if p.body->AppendRequest_mode == Mode::Heartbeat || p.body->AppendRequest_prev+1 > s.nodes[m.source].commit {
                p.body->AppendRequest_prev+p.body->AppendRequest_entries.len()
            } else { s.nodes[m.source].commit };
        reveal(enabled); reveal(receive_enabled); leaders::request_origin(b,c,create,p);
        assert(p.body->AppendRequest_mode != Mode::Heartbeat);
        if p.body->AppendRequest_prev+1 > s.nodes[m.source].commit {
            leaders::source_still_leads(b,c,time,create,p); assert(sent::live(s,p)); assert(election::message_wf(p,c));
            let g=trace::at(b,c,create).logs; assert(logs::represented(g,s.nodes[m.dest].log));
            prefixes::normal_prefix(g,c,p,s.nodes[m.dest].log);
            let h=sub(s.nodes[m.dest].log,1,(p.body->AppendRequest_prev+p.body->AppendRequest_entries.len()) as int);
            assert(logs::prefix_of(h,s.nodes[m.dest].log)); logs::prefix_transitive(h,s.nodes[m.dest].log,b[time].nodes[m.dest].log);
            prefixes::shorten(h,b[time].nodes[m.dest].log,k);
            logs::prefix_transitive(sub(b[time].nodes[m.dest].log,1,k),h,s.nodes[m.source].log);
        }
    }
}
pub proof fn pending_commit(b: Behavior<LState>,c: Constants,m: Message,lo: int,hi: int)
    requires election::safety_spec(b,c),c.servers.contains(m.source),0 <= lo <= hi,
        forall |r: int| lo < r <= hi ==> #[trigger] b[r].pending.count(m) > 0
    ensures b[lo].nodes[m.source].commit <= b[hi].nodes[m.source].commit
    decreases hi-lo
{
    if hi > lo {
        pending_commit(b,c,m,lo,hi-1); events::step_valid(b,c,hi-1); persistence::safety_at(b,c,hi-1);
        assert(b[hi].pending.count(m) > 0); events::pending_survives(b[hi-1],c,events::step(b,c,hi-1),m);
        persistence::commit_monotone(b[hi-1],c,events::step(b,c,hi-1),m.source);
    }
}
pub proof fn disk_commit(b: Behavior<LState>,c: Constants,i: int,lo: int,hi: int)
    requires election::safety_spec(b,c),c.servers.contains(i),0 <= lo <= hi
    ensures b[lo].nodes[i].disk.commit <= b[hi].nodes[i].disk.commit
    decreases hi-lo
{
    if hi > lo {
        disk_commit(b,c,i,lo,hi-1); events::step_valid(b,c,hi-1); persistence::safety_at(b,c,hi-1);
        persistence::commit_monotone(b[hi-1],c,events::step(b,c,hi-1),i);
    }
}
pub proof fn released_counter(b: Behavior<LState>,c: Constants,m: Message,create: int,release: int,end: int)
    requires election::safety_spec(b,c),c.servers.contains(m.source),0 <= create < release < end,
        events::step(b,c,release) == Action::Ready(m.source),
        forall |r: int| create < r <= release ==> #[trigger] b[r].pending.count(m) > 0
    ensures b[create].nodes[m.source].commit <= b[end].nodes[m.source].commit
{
    pending_commit(b,c,m,create,release); events::step_valid(b,c,release); reveal(apply);
    disk_commit(b,c,m.source,release+1,end); persistence::safety_at(b,c,end); assert(persistence::node(b[end],c,m.source));
}
pub proof fn matched_retained(b: Behavior<LState>,c: Constants,horizon: int,send: int,end: int,i: int,j: int,d: Decision,k: int)
    requires election::safety_spec(b,c),0 <= send <= end <= horizon,c.servers.contains(i),c.servers.contains(j),i != j,
        b[send].nodes[i].role == Role::Leader,b[send].nodes[i].matched[j] >= k,0 < k <= b[send].nodes[i].log.len(),
        trace::at(b,c,horizon).decisions.contains(d),d.term <= b[send].nodes[i].term,
        logs::prefix_of(sub(b[send].nodes[i].log,1,k),d.log)
    ensures b[end].nodes[j].commit >= k || logs::prefix_of(sub(b[send].nodes[i].log,1,k),b[end].nodes[j].log)
{
    let w=peer_ack(b,c,send,i,j,k); assert(b[w.0+1].pending.count(w.3) > 0);
    prefix_or_counter(b,c,send,w.0,w.3,k);
    if b[w.0].nodes[j].commit >= k { released_counter(b,c,w.3,w.0,w.1,end); }
    else { stable::acknowledgment_retained(b,c,horizon,d,sub(b[send].nodes[i].log,1,k),w.0+1,w.1,end,w.3); }
}
} // verus!
