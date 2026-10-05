//! Every live and persisted commit prefix is covered by an actual direct decision.
use vstd::prelude::*;
use super::etcd::{*,sub};
use super::etcd_election as election;
use super::etcd_logs as logs;
use super::etcd_ack_prefixes as prefixes;
use super::etcd_history_trace as trace;
use super::etcd_commit_history::{self as history,ProofState,Decision,state};
use super::etcd_transmissions as events;
use super::etcd_leader_trace as leaders;
use super::etcd_heartbeat as heartbeat;
use super::etcd_durability as durability;
use super::temporal::Behavior;
verus! {
pub open spec fn covered(g: ProofState,h: Seq<nat>,term: nat) -> bool {
    h.len() == 0 || exists |d: Decision| g.decisions.contains(d) && d.term <= term && #[trigger] logs::prefix_of(h,d.log)
}
pub open spec fn node(g: ProofState,i: int) -> bool {
    let n=state(g).nodes[i];
    n.commit <= n.log.len() && covered(g,committed(n),n.term)
    && n.disk.commit <= n.disk.log.len() && covered(g,sub(n.disk.log,1,n.disk.commit as int),n.disk.term)
}
pub open spec fn inductive(g: ProofState,c: Constants) -> bool {
    forall |i: int| c.servers.contains(i) ==> #[trigger] node(g,i)
}
pub proof fn smaller(g: ProofState,h: Seq<nat>,v: Seq<nat>,term: nat)
    requires covered(g,v,term),logs::prefix_of(h,v)
    ensures covered(g,h,term)
{
    if h.len() > 0 {
        let d=choose |d: Decision| g.decisions.contains(d) && d.term <= term && #[trigger] logs::prefix_of(v,d.log);
        logs::prefix_transitive(h,v,d.log);
    }
}
pub proof fn monotone(g: ProofState,u: ProofState,h: Seq<nat>,term: nat,next_term: nat)
    requires covered(g,h,term),g.decisions.subset_of(u.decisions),term <= next_term
    ensures covered(u,h,next_term)
{
    if h.len() > 0 {
        let d=choose |d: Decision| g.decisions.contains(d) && d.term <= term && #[trigger] logs::prefix_of(h,d.log);
        assert(u.decisions.contains(d));
    }
}
pub proof fn conflict_preserves_committed(n: LServer,m: Message)
    requires n.commit <= n.log.len(),m.body is AppendRequest,m.body->AppendRequest_prev+1 > n.commit,
        log_ok(n,m.body->AppendRequest_prev,m.body->AppendRequest_prev_term),
        !no_conflict(n,m.body->AppendRequest_prev+1,m.body->AppendRequest_entries)
    ensures n.log.len() > n.commit
{
    let p=m.body->AppendRequest_prev; let e=m.body->AppendRequest_entries;
    if n.log.len() <= n.commit { assert(p == n.log.len()); assert(no_conflict(n,p+1,e)); assert(false); }
}
pub proof fn receive_commit(b: Behavior<LState>,c: Constants,time: int,m: Message)
    requires election::safety_spec(b,c),time >= 0,events::step(b,c,time) == (Action::Receive { m,how: Receive::AppendDone }),
        b[time+1].nodes[m.dest].commit > b[time].nodes[m.dest].commit,
        forall |r: int| 0 <= r <= time ==> #[trigger] inductive(trace::at(b,c,r),c)
    ensures b[time+1].nodes[m.dest].commit <= b[time+1].nodes[m.dest].log.len(),
        covered(trace::at(b,c,time+1),committed(b[time+1].nodes[m.dest]),b[time+1].nodes[m.dest].term)
{
    events::step_valid(b,c,time); trace::valid(b,c,time); trace::valid(b,c,time+1);
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    assert(m.body is AppendRequest); let create=leaders::request_origin(b,c,time,m);
    let src=b[create].nodes[m.source]; let n=b[time].nodes[m.dest]; let v=b[time+1].nodes[m.dest]; let k=v.commit as int;
    assert(0 < k <= m.body->AppendRequest_commit); trace::valid(b,c,create); let g=trace::at(b,c,create);
    assert(inductive(g,c)); assert(node(g,m.source)); assert(covered(g,committed(src),src.term));
    let h=sub(src.log,1,k); assert(logs::prefix_of(h,committed(src))); smaller(g,h,committed(src),src.term);
    let d=choose |d: Decision| g.decisions.contains(d) && d.term <= src.term && #[trigger] logs::prefix_of(h,d.log);
    trace::monotone(b,c,create,time); assert(trace::at(b,c,time).decisions.contains(d));
    assert(election::message_wf(m,c));
    if m.body->AppendRequest_mode == Mode::Heartbeat {
        heartbeat::matched_retained(b,c,time,create,time,m.source,m.dest,d,k);
        assert(logs::prefix_of(h,n.log));
    } else {
        assert(m.body->AppendRequest_prev+1 > n.commit);
        trace::live_log(b,c,create,m.source); trace::monotone(b,c,create,time);
        let old=trace::at(b,c,time).logs;
        assert(old.created.contains(src.log)); assert(logs::prefix_of(src.log,src.log)); assert(logs::represented(old,src.log));
        prefixes::normal_prefix(old,c,m,src.log);
        let end=m.body->AppendRequest_prev+m.body->AppendRequest_entries.len(); let received=sub(src.log,1,end as int);
        assert(logs::prefix_of(h,received)); logs::prefix_transitive(h,received,n.log);
    }
    assert(committed(v) =~= h);
    trace::monotone(b,c,create,time+1); monotone(g,trace::at(b,c,time+1),h,src.term,v.term);
}
pub proof fn preserve_node(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires election::safety_spec(b,c),time >= 0,c.servers.contains(i),
        forall |r: int| 0 <= r <= time ==> #[trigger] inductive(trace::at(b,c,r),c)
    ensures node(trace::at(b,c,time+1),i)
{
    events::step_valid(b,c,time); trace::valid(b,c,time); trace::valid(b,c,time+1);
    let g=trace::at(b,c,time); let u=trace::at(b,c,time+1); let a=events::step(b,c,time); let s=b[time]; let n=s.nodes[i]; let v=b[time+1].nodes[i];
    assert(inductive(g,c)); assert(node(g,i)); trace::monotone(b,c,time,time+1);
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    if a == Action::Restart(i) {
        monotone(g,u,sub(n.disk.log,1,n.disk.commit as int),n.disk.term,v.term);
    } else if a == Action::AdvanceCommit(i) && v.commit > n.commit {
        durability::leader_commit_bound(b,c,time+1,i); let d=history::record(s,c,i,v.commit);
        assert(u.decisions.contains(d)); assert(d.log == committed(v)); assert(logs::prefix_of(committed(v),d.log));
        assert(covered(u,committed(v),v.term));
    } else if v.commit > n.commit {
        if let Action::Receive { m,how } = a { receive_commit(b,c,time,m); } else { assert(false); }
    } else {
        if let Action::Receive { m,how } = a {
            if m.dest == i && how == Receive::AppendConflict { conflict_preserves_committed(n,m); }
        }
        assert(v.commit == n.commit); assert(v.commit <= v.log.len()); assert(committed(v) =~= committed(n));
        monotone(g,u,committed(n),n.term,v.term);
    }
    if a == Action::Ready(i) { monotone(g,u,committed(n),n.term,v.disk.term); }
    else { monotone(g,u,sub(n.disk.log,1,n.disk.commit as int),n.disk.term,v.disk.term); }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,time: int)
    requires election::safety_spec(b,c),time >= 0
    ensures inductive(trace::at(b,c,time),c),forall |r: int| 0 <= r <= time ==> #[trigger] inductive(trace::at(b,c,r),c)
    decreases time
{
    if time == 0 { trace::valid(b,c,0); }
    else {
        safety_at(b,c,time-1);
        assert forall |i: int| c.servers.contains(i) implies #[trigger] node(trace::at(b,c,time),i) by { preserve_node(b,c,time-1,i); }
    }
    assert forall |r: int| 0 <= r <= time implies #[trigger] inductive(trace::at(b,c,r),c) by {
        if r < time { assert(inductive(trace::at(b,c,r),c)); }
    }
}
} // verus!
