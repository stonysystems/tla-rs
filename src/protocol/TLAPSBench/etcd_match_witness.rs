//! A current-term match index comes from an actual released acknowledgment.
use vstd::prelude::*;
use super::etcd::*;
use super::etcd_election as election;
use super::etcd_candidates as candidates;
use super::etcd_logs as logs;
use super::etcd_transmissions as events;
use super::temporal::Behavior;
verus! {
pub open spec fn leading(b: Behavior<LState>,i: int,t: nat,lo: int,hi: int) -> bool {
    forall |r: int| lo <= r <= hi ==> (#[trigger] b[r].nodes[i]).role == Role::Leader && b[r].nodes[i].term == t
}
pub proof fn epoch_start(b: Behavior<LState>,c: Constants,k: int,i: int) -> (j: int)
    requires election::safety_spec(b,c),k >= 0,c.servers.contains(i),b[k].nodes[i].role == Role::Leader
    ensures 0 <= j < k,events::step(b,c,j) == Action::BecomeLeader(i),b[j].nodes[i].role == Role::Candidate,
        b[j].nodes[i].term == b[k].nodes[i].term,leading(b,i,b[k].nodes[i].term,j+1,k)
    decreases k
{
    if k == 0 { assert(false); arbitrary() }
    else {
        let p=k-1; events::step_valid(b,c,p); let a=events::step(b,c,p);
        reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
        if b[p].nodes[i].role == Role::Leader {
            assert(b[p].nodes[i].term == b[k].nodes[i].term); let j=epoch_start(b,c,p,i);
            assert forall |r: int| j+1 <= r <= k implies (#[trigger] b[r].nodes[i]).role == Role::Leader && b[r].nodes[i].term == b[k].nodes[i].term by {
                if r < k { assert(b[r].nodes[i].role == Role::Leader && b[r].nodes[i].term == b[p].nodes[i].term); }
            }
            j
        } else { assert(a == Action::BecomeLeader(i)); p }
    }
}
pub proof fn leader_log_step(s: LState,c: Constants,a: Action,i: int)
    requires enabled(s,c,a),s.nodes[i].role == Role::Leader,apply(s,c,a).nodes[i].role == Role::Leader,
        s.nodes[i].term == apply(s,c,a).nodes[i].term
    ensures logs::prefix_of(s.nodes[i].log,apply(s,c,a).nodes[i].log)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
}
pub proof fn leader_log_interval(b: Behavior<LState>,c: Constants,i: int,t: nat,lo: int,hi: int)
    requires election::safety_spec(b,c),0 <= lo <= hi,leading(b,i,t,lo,hi)
    ensures logs::prefix_of(b[lo].nodes[i].log,b[hi].nodes[i].log)
    decreases hi-lo
{
    if hi > lo {
        leader_log_interval(b,c,i,t,lo,hi-1); events::step_valid(b,c,hi-1);
        assert(b[hi-1].nodes[i].role == Role::Leader && b[hi-1].nodes[i].term == t);
        assert(b[hi].nodes[i].role == Role::Leader && b[hi].nodes[i].term == t);
        leader_log_step(b[hi-1],c,events::step(b,c,hi-1),i);
        logs::prefix_transitive(b[lo].nodes[i].log,b[hi-1].nodes[i].log,b[hi].nodes[i].log);
    }
}
pub proof fn matching_step(s: LState,c: Constants,a: Action,i: int,j: int,k: int) -> (m: Message)
    requires enabled(s,c,a),s.nodes[i].role == Role::Leader,apply(s,c,a).nodes[i].role == Role::Leader,
        s.nodes[i].term == apply(s,c,a).nodes[i].term,s.nodes[i].matched[j] < k <= apply(s,c,a).nodes[i].matched[j]
    ensures a == (Action::Receive { m,how: Receive::AppendResponse }),s.messages.count(m) > 0,
        m.source == j,m.dest == i,m.term == s.nodes[i].term,m.body is AppendResponse,m.body->AppendResponse_success,m.body->AppendResponse_matched >= k
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    if let Action::Receive { m,how } = a { m } else { assert(false); arbitrary() }
}
pub proof fn match_since(b: Behavior<LState>,c: Constants,i: int,j: int,k: int,t: nat,lo: int,hi: int) -> (w: (int,Message))
    requires election::safety_spec(b,c),0 <= lo <= hi,leading(b,i,t,lo,hi),b[lo].nodes[i].matched[j] < k,b[hi].nodes[i].matched[j] >= k
    ensures lo <= w.0 < hi,events::step(b,c,w.0) == (Action::Receive { m: w.1,how: Receive::AppendResponse }),b[w.0].messages.count(w.1) > 0,
        w.1.source == j,w.1.dest == i,w.1.term == t,w.1.body is AppendResponse,w.1.body->AppendResponse_success,w.1.body->AppendResponse_matched >= k
    decreases hi-lo
{
    if hi == lo { assert(false); arbitrary() }
    else {
        let p=hi-1; events::step_valid(b,c,p);
        if b[p].nodes[i].matched[j] >= k { match_since(b,c,i,j,k,t,lo,p) }
        else {
            assert(b[p].nodes[i].role == Role::Leader && b[p].nodes[i].term == t);
            assert(b[hi].nodes[i].role == Role::Leader && b[hi].nodes[i].term == t);
            let m=matching_step(b[p],c,events::step(b,c,p),i,j,k); (p,m)
        }
    }
}
pub proof fn current_term_match(b: Behavior<LState>,c: Constants,time: int,i: int,j: int,k: int) -> (w: (int,Message))
    requires election::safety_spec(b,c),time >= 0,c.servers.contains(i),c.servers.contains(j),b[time].nodes[i].role == Role::Leader,
        1 <= k <= b[time].nodes[i].log.len(),b[time].nodes[i].log[k-1] == b[time].nodes[i].term,b[time].nodes[i].matched[j] >= k
    ensures 0 <= w.0 < time,events::step(b,c,w.0) == (Action::Receive { m: w.1,how: Receive::AppendResponse }),b[w.0].messages.count(w.1) > 0,
        w.1.source == j,w.1.dest == i,w.1.term == b[time].nodes[i].term,w.1.body is AppendResponse,w.1.body->AppendResponse_success,w.1.body->AppendResponse_matched >= k
{
    let start=epoch_start(b,c,time,i); let t=b[time].nodes[i].term;
    events::step_valid(b,c,start); candidates::safety_at(b,c,start); assert(candidates::candidate(b[start].nodes[i]));
    leader_log_interval(b,c,i,t,start+1,time); reveal(apply);
    if b[start+1].nodes[i].matched[j] >= k {
        assert(j == i && k <= b[start].nodes[i].log.len());
        assert(b[start].nodes[i].log[k-1] < t);
        assert(b[start+1].nodes[i].log[k-1] == b[time].nodes[i].log[k-1]); assert(false);
    }
    match_since(b,c,i,j,k,t,start+1,time)
}
pub proof fn acknowledgment_origin(b: Behavior<LState>,c: Constants,time: int,i: int,j: int,k: int) -> (w: (int,int,int,Message))
    requires election::safety_spec(b,c),time >= 0,c.servers.contains(i),c.servers.contains(j),b[time].nodes[i].role == Role::Leader,
        1 <= k <= b[time].nodes[i].log.len(),b[time].nodes[i].log[k-1] == b[time].nodes[i].term,b[time].nodes[i].matched[j] >= k
    ensures 0 <= w.0 < w.1 < w.2 < time,b[w.0].nodes[j].term == b[time].nodes[i].term,
        w.3.source == j,w.3.dest == i,w.3.term == b[time].nodes[i].term,w.3.body is AppendResponse,w.3.body->AppendResponse_success,w.3.body->AppendResponse_matched >= k,
        events::step(b,c,w.1) == Action::Ready(j),events::step(b,c,w.2) == (Action::Receive { m: w.3,how: Receive::AppendResponse }),
        b[w.0].pending.count(w.3) == 0,forall |r: int| w.0 < r <= w.1 ==> #[trigger] b[r].pending.count(w.3) > 0
{
    let x=current_term_match(b,c,time,i,j,k); let release=events::release_origin(b,c,x.0,x.1);
    let create=events::pending_origin(b,c,release,x.1); (create,release,x.0,x.1)
}
} // verus!
