//! The log prefix certified when a successful acknowledgment is created.
//! The source's commit-index fallback is traced to a prior direct decision.
use vstd::prelude::*;
use super::etcd::{*,sub};
use super::etcd_election as election;
use super::etcd_origins as origins;
use super::etcd_logs as logs;
use super::etcd_sent as sent;
use super::etcd_acknowledgments as acks;
use super::etcd_commit_history::{self as history,Decision};
use super::etcd_decision_owners as owners;
use super::etcd_history_trace as trace;
use super::etcd_leader_trace as leaders;
use super::etcd_transmissions as events;
use super::etcd_match_witness as matches;
use super::temporal::Behavior;
verus! {
pub proof fn success_creation(s: LState,c: Constants,a: Action,m: Message)
    requires election::inductive(s,c),enabled(s,c,a),s.pending.count(m) == 0,apply(s,c,a).pending.count(m) > 0,acks::success(m)
    ensures c.servers.contains(m.source),c.servers.contains(m.dest),m.term == s.nodes[m.source].term,
        s.nodes[m.source].log == apply(s,c,a).nodes[m.source].log,
        a == Action::SelfAppend(m.source) && m.source == m.dest && s.nodes[m.source].role == Role::Leader && m.body->AppendResponse_matched == s.nodes[m.source].log.len()
        || exists |packet: Message| a == (Action::Receive { m: packet,how: Receive::AppendDone })
            && packet.body is AppendRequest && packet.source == m.dest && packet.dest == m.source && packet.term == m.term
            && m.body->AppendResponse_mode == packet.body->AppendRequest_mode
            && m.body->AppendResponse_matched == if packet.body->AppendRequest_mode == Mode::Heartbeat || packet.body->AppendRequest_prev+1 > s.nodes[m.source].commit {
                packet.body->AppendRequest_prev+packet.body->AppendRequest_entries.len()
            } else { s.nodes[m.source].commit }
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    if let Action::Receive { m: packet,how } = a {
        assert(election::message_wf(packet,c));
        assert(packet.body is AppendRequest && packet.source == m.dest && packet.dest == m.source && packet.term == m.term
            && m.body->AppendResponse_mode == packet.body->AppendRequest_mode
            && m.body->AppendResponse_matched == if packet.body->AppendRequest_mode == Mode::Heartbeat || packet.body->AppendRequest_prev+1 > s.nodes[m.source].commit {
                packet.body->AppendRequest_prev+packet.body->AppendRequest_entries.len()
            } else { s.nodes[m.source].commit });
    }
}
pub proof fn normal_prefix(g: logs::ProofState,c: Constants,m: Message,h: Seq<nat>)
    requires logs::inductive(g,c),receive_enabled(g.state,m,Receive::AppendDone),m.body is AppendRequest,
        election::message_wf(m,c),logs::represented(g,h),logs::segment(m,h),
        m.body->AppendRequest_prev+1 > g.state.nodes[m.dest].commit
    ensures logs::prefix_of(sub(h,1,(m.body->AppendRequest_prev+m.body->AppendRequest_entries.len()) as int),g.state.nodes[m.dest].log)
{
    reveal(receive_enabled);
    let n=g.state.nodes[m.dest]; let p=m.body->AppendRequest_prev; let e=m.body->AppendRequest_entries;
    let x=logs::representing(g,n.log); let y=logs::representing(g,h);
    assert(logs::matching(y,x)); logs::matching_prefix(h,n.log,y,x);
    let end=p+e.len(); let prefix=sub(h,1,end as int);
    if p > 0 { assert(h[p-1] == n.log[p-1]); }
    assert forall |k: int| 0 <= k < prefix.len() implies #[trigger] prefix[k] == #[trigger] n.log[k] by {
        if k < p { assert(h[k] == n.log[k]); }
        else { assert(e[k-p] == h[k]); assert(n.log[k] == e[k-p]); }
    }
}
pub proof fn shorten(a: Seq<nat>,b: Seq<nat>,k: int)
    requires logs::prefix_of(a,b),0 <= k <= a.len()
    ensures sub(a,1,k) == sub(b,1,k),logs::prefix_of(sub(b,1,k),a)
{ assert(sub(a,1,k) =~= sub(b,1,k)); }
pub proof fn fallback_lower(b: Behavior<LState>,c: Constants,time: int,create: int,m: Message,k: int) -> (d: Decision)
    requires election::safety_spec(b,c),0 <= create <= time,c.servers.contains(m.dest),
        b[time].nodes[m.dest].role == Role::Leader,b[time].nodes[m.dest].term == m.term,
        b[time].nodes[m.dest].commit < k,history::has_commit(trace::at(b,c,create),m.term,k as nat),k > 0
    ensures trace::at(b,c,time).decisions.contains(d),d.term < m.term,d.log.len() >= k
{
    trace::valid(b,c,create); trace::valid(b,c,time); trace::monotone(b,c,create,time);
    let d=choose |d: Decision| trace::at(b,c,create).decisions.contains(d) && d.term <= m.term && d.log.len() >= k;
    let g=trace::at(b,c,time); assert(g.decisions.contains(d)); assert(history::decision_valid(g,c,d));
    if d.term == m.term {
        origins::leader_persisted(b[time],c,m.dest); origins::unique_certificate(b[time],c,m.term,m.dest,d.leader);
        assert(owners::retained(g,d)); assert(false);
    }
    d
}
pub proof fn created_prefix_or_prior(b: Behavior<LState>,c: Constants,time: int,create: int,m: Message,k: int)
    requires election::safety_spec(b,c),0 <= create < time,c.servers.contains(m.dest),
        b[time].nodes[m.dest].role == Role::Leader,b[time].nodes[m.dest].term == m.term,
        b[time].nodes[m.dest].commit < k <= b[time].nodes[m.dest].log.len(),k > 0,
        acks::success(m),m.body->AppendResponse_matched >= k,b[create].pending.count(m) == 0,b[create+1].pending.count(m) > 0
    ensures logs::prefix_of(sub(b[time].nodes[m.dest].log,1,k),b[create].nodes[m.source].log)
        || exists |d: Decision| trace::at(b,c,time).decisions.contains(d) && d.term < m.term && d.log.len() >= k
{
    events::step_valid(b,c,create); let a=events::step(b,c,create); let s=b[create];
    trace::valid(b,c,create); success_creation(s,c,a,m); let g=trace::at(b,c,create);
    if a == Action::SelfAppend(m.source) {
        reveal(enabled); leaders::continuous(b,c,m.source,create,time); shorten(s.nodes[m.source].log,b[time].nodes[m.dest].log,k);
    } else {
        let packet=choose |packet: Message| a == (Action::Receive { m: packet,how: Receive::AppendDone })
            && packet.body is AppendRequest && packet.source == m.dest && packet.dest == m.source && packet.term == m.term
            && m.body->AppendResponse_mode == packet.body->AppendRequest_mode
            && m.body->AppendResponse_matched == if packet.body->AppendRequest_mode == Mode::Heartbeat || packet.body->AppendRequest_prev+1 > s.nodes[m.source].commit {
                packet.body->AppendRequest_prev+packet.body->AppendRequest_entries.len()
            } else { s.nodes[m.source].commit };
        reveal(enabled); reveal(receive_enabled);
        leaders::request_origin(b,c,create,packet);
        assert(packet.body->AppendRequest_mode != Mode::Heartbeat);
        if packet.body->AppendRequest_prev+1 <= s.nodes[m.source].commit {
            assert(history::node(g,m.source));
            history::commit_monotone(g,g,m.term,s.nodes[m.source].commit,m.term,k as nat);
            let d=fallback_lower(b,c,time,create,m,k);
        } else {
            leaders::source_still_leads(b,c,time,create,packet);
            assert(sent::live(s,packet)); assert(election::message_wf(packet,c));
            assert(logs::represented(g.logs,s.nodes[m.dest].log));
            normal_prefix(g.logs,c,packet,s.nodes[m.dest].log);
            let end=packet.body->AppendRequest_prev+packet.body->AppendRequest_entries.len();
            let h=sub(s.nodes[m.dest].log,1,end as int);
            assert(logs::prefix_of(h,s.nodes[m.dest].log));
            logs::prefix_transitive(h,s.nodes[m.dest].log,b[time].nodes[m.dest].log);
            shorten(h,b[time].nodes[m.dest].log,k);
            logs::prefix_transitive(sub(b[time].nodes[m.dest].log,1,k),h,s.nodes[m.source].log);
        }
    }
}
// Prefix retention of lower-term decisions is discharged separately. This
// lemma exposes that obligation rather than assuming it in the protocol.
pub proof fn acknowledgment_prefix(b: Behavior<LState>,c: Constants,time: int,i: int,j: int,k: int) -> (w: (int,int,int,Message))
    requires election::safety_spec(b,c),time >= 0,c.servers.contains(i),c.servers.contains(j),b[time].nodes[i].role == Role::Leader,
        b[time].nodes[i].commit < k <= b[time].nodes[i].log.len(),k > 0,b[time].nodes[i].log[k-1] == b[time].nodes[i].term,b[time].nodes[i].matched[j] >= k,
        forall |d: Decision| trace::at(b,c,time).decisions.contains(d) && d.term < b[time].nodes[i].term ==> #[trigger] logs::prefix_of(d.log,b[time].nodes[i].log)
    ensures 0 <= w.0 < w.1 < w.2 < time,b[w.0].nodes[j].term == b[time].nodes[i].term,
        w.3.source == j,w.3.dest == i,w.3.term == b[time].nodes[i].term,acks::success(w.3),w.3.body->AppendResponse_matched >= k,
        events::step(b,c,w.1) == Action::Ready(j),events::step(b,c,w.2) == (Action::Receive { m: w.3,how: Receive::AppendResponse }),
        logs::prefix_of(sub(b[time].nodes[i].log,1,k),b[w.0+1].nodes[j].log),
        forall |r: int| w.0 < r <= w.1 ==> #[trigger] b[r].pending.count(w.3) > 0
{
    let w=matches::acknowledgment_origin(b,c,time,i,j,k); assert(b[w.0+1].pending.count(w.3) > 0);
    created_prefix_or_prior(b,c,time,w.0,w.3,k);
    if !logs::prefix_of(sub(b[time].nodes[i].log,1,k),b[w.0].nodes[j].log) {
        let d=choose |d: Decision| trace::at(b,c,time).decisions.contains(d) && d.term < w.3.term && d.log.len() >= k;
        trace::valid(b,c,time); assert(history::decision_valid(trace::at(b,c,time),c,d));
        assert(logs::prefix_of(d.log,b[time].nodes[i].log)); assert(d.log[k-1] == b[time].nodes[i].log[k-1]);
        assert(d.log[k-1] <= d.term); assert(false);
    }
    events::step_valid(b,c,w.0); election::safety_at(b,c,w.0); success_creation(b[w.0],c,events::step(b,c,w.0),w.3); w
}
} // verus!
