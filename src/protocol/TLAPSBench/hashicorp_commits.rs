//! Concrete receipt witnesses for the quorums used by leader commit advances.
//! Prefix certificates below a term bound depend explicitly on leader uniqueness.
use vstd::prelude::*;
use super::hashicorp::{*,sub};
use super::hashicorp_config as configs;
use super::hashicorp_types as types;
use super::hashicorp_order as order;
use super::hashicorp_history::{self as history,step};
use super::hashicorp_replication as replication;
use super::hashicorp_prefixes as prefixes;
use super::temporal::Behavior;
verus! {
pub proof fn match_origin(b: Behavior<LState>,c: Constants,time: int,i: int,j: int,index: int) -> (origin: (int,Message))
    requires configs::safety_spec(b,c),time >= 0,c.servers.contains(i),c.servers.contains(j),i != j,
        b[time].nodes[i].role == Role::Leader,0 < index <= b[time].nodes[i].matched[j]
    ensures 0 <= origin.0 < time,step(b,c,origin.0) == (Action::Receive { m: origin.1,how: Receive::ReplicateResponse }),
        b[origin.0].messages.count(origin.1) > 0,replication::positive(origin.1),origin.1.source == j,origin.1.dest == i,
        origin.1.term == b[time].nodes[i].term,origin.1.body->AppendResponse_matched >= index,
        b[origin.0].nodes[i].role == Role::Leader,b[origin.0].nodes[i].term == b[time].nodes[i].term
    decreases time
{
    if time == 0 { assert(false); (0,arbitrary()) }
    else {
        let p=time-1; history::step_valid(b,c,p); let a=step(b,c,p);
        reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
        if b[p].nodes[i].role == Role::Leader && b[p].nodes[i].term == b[time].nodes[i].term && b[p].nodes[i].matched[j] >= index {
            match_origin(b,c,p,i,j,index)
        } else { assert(a is Receive); (p,a->Receive_m) }
    }
}
pub proof fn acknowledged_prefix(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,time: int,m: Message) -> (origin: (int,int))
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),0 <= time <= horizon,
        b[time].messages.count(m) > 0,replication::positive(m),m.term < bound
    ensures 0 <= origin.1 < origin.0 < time,c.servers.contains(m.source),c.servers.contains(m.dest),
        b[origin.1].nodes[m.dest].role == Role::Leader,b[origin.1].nodes[m.dest].term == m.term,
        0 <= m.body->AppendResponse_matched <= b[origin.0+1].nodes[m.source].log.len(),
        m.body->AppendResponse_matched <= b[origin.1].nodes[m.dest].log.len(),
        b[origin.0+1].nodes[m.source].term == m.term,
        sub(b[origin.0+1].nodes[m.source].log,1,m.body->AppendResponse_matched)
            == sub(b[origin.1].nodes[m.dest].log,1,m.body->AppendResponse_matched)
{
    let ack=replication::response_origin(b,c,time,m); let at=ack.0; let request=ack.1;
    let sent=replication::request_bound(b,c,at,request); let index=m.body->AppendResponse_matched;
    types::safety_at(b,c,time); assert(types::message(m,c));
    types::safety_at(b,c,at); assert(types::message(request,c)); history::step_valid(b,c,at);
    reveal(enabled); reveal(receive_enabled);
    let prev=request.body->AppendRequest_prev; let entries=request.body->AppendRequest_entries;
    let old=b[at].nodes[m.source].log; let source=b[sent].nodes[m.dest].log; let stored=b[at+1].nodes[m.source].log;
    replication::merge_length(old,prev,entries);
    if index > 0 {
        if entries.len() > 0 {
            replication::merged_terms(old,prev,entries,entries.len() as int-1);
            assert(source[index-1] == entries[entries.len()-1]);
        } else { reveal(merge); assert(stored == old); }
        assert(stored[index-1].term == source[index-1].term);
        let g=order::safety_at(b,c,sent); assert(order::node(g.state.nodes[m.dest])); assert(source[index-1].term <= m.term);
        prefixes::log_matching_below(b,c,horizon,bound,at+1,sent,m.source,m.dest,index-1);
    } else { assert(sub(stored,1,index) =~= sub(source,1,index)); }
    (at,sent)
}
pub proof fn match_prefix(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,time: int,i: int,j: int,index: int) -> (at: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),0 <= time <= horizon,
        c.servers.contains(i),c.servers.contains(j),i != j,b[time].nodes[i].role == Role::Leader,
        b[time].nodes[i].term < bound,0 < index <= b[time].nodes[i].matched[j]
    ensures 0 <= at < time,index <= b[at+1].nodes[j].log.len(),index <= b[time].nodes[i].log.len(),
        b[at+1].nodes[j].term == b[time].nodes[i].term,
        sub(b[at+1].nodes[j].log,1,index) == sub(b[time].nodes[i].log,1,index)
{
    let consumed=match_origin(b,c,time,i,j,index); let m=consumed.1;
    let received=acknowledged_prefix(b,c,horizon,bound,consumed.0,m); let at=received.0; let sent=received.1;
    history::continuous(b,c,i,sent,time);
    assert(sub(b[at+1].nodes[j].log,1,index) =~= sub(b[time].nodes[i].log,1,index)) by {
        assert forall |k: int| 0 <= k < index implies (#[trigger] sub(b[at+1].nodes[j].log,1,index)[k]) == sub(b[time].nodes[i].log,1,index)[k] by {
            assert(sub(b[at+1].nodes[j].log,1,m.body->AppendResponse_matched)[k] == sub(b[sent].nodes[i].log,1,m.body->AppendResponse_matched)[k]);
            assert(sub(b[time].nodes[i].log,1,b[sent].nodes[i].log.len() as int)[k] == b[sent].nodes[i].log[k]);
        }
    }
    at
}
pub proof fn maximum_correct(q: Set<int>)
    requires !q.is_empty()
    ensures q.contains(maximum(q)),forall |x: int| q.contains(x) ==> x <= maximum(q)
    decreases q.len()
{
    let x=q.choose(); let rest=q.remove(x);
    let m=if rest.is_empty() { x } else { maximum_correct(rest); if x > maximum(rest) { x } else { maximum(rest) } };
    assert(q.contains(m)); assert forall |y: int| q.contains(y) implies y <= m by { if y != x { assert(rest.contains(y)); } }
    assert(exists |z: int| q.contains(z) && forall |y: int| q.contains(y) ==> y <= z); reveal(maximum);
}
pub open spec fn voters(n: LServer,c: Constants,i: int,index: int) -> Set<int> {
    c.servers.filter(|j: int| n.matched[j] >= index).insert(i).intersect(n.latest_config)
}
pub proof fn decision_certificate(b: Behavior<LState>,c: Constants,time: int,i: int)
    requires configs::safety_spec(b,c),time >= 0,step(b,c,time) == Action::AdvanceCommit(i)
    ensures c.servers.contains(i),b[time].nodes[i].role == Role::Leader,
        b[time].nodes[i].commit < b[time+1].nodes[i].commit <= b[time].nodes[i].log.len(),
        b[time].nodes[i].log[b[time+1].nodes[i].commit-1].term == b[time].nodes[i].term,
        quorum(voters(b[time].nodes[i],c,i,b[time+1].nodes[i].commit as int),b[time].nodes[i].latest_config),
        voters(b[time].nodes[i],c,i,b[time+1].nodes[i].commit as int).subset_of(c.servers),
        b[time+1].nodes[i].log == b[time].nodes[i].log,
        b[time+1].commits.contains(Event { server: i,term: b[time].nodes[i].term,entries: sub(b[time].nodes[i].log,1,b[time+1].nodes[i].commit as int) })
{
    history::step_valid(b,c,time); reveal(enabled); reveal(protocol_apply);
    types::safety_at(b,c,time); assert(types::node(b[time].nodes[i],c));
    maximum_correct(agree_indices(b[time].nodes[i],i,c));
    broadcast use Set::lemma_map_contains;
    let changed=c.servers.filter(|j: int| b[time+1].nodes[j].commit > b[time].nodes[j].commit);
    assert(changed.contains(i));
    assert(changed.map(|j: int| Event { server: j,term: b[time+1].nodes[j].term,entries: sub(b[time+1].nodes[j].log,1,b[time+1].nodes[j].commit as int) })
        .contains(Event { server: i,term: b[time].nodes[i].term,entries: sub(b[time].nodes[i].log,1,b[time+1].nodes[i].commit as int) }));
}
pub proof fn decision_voter(b: Behavior<LState>,c: Constants,horizon: int,bound: nat,time: int,i: int,j: int) -> (at: int)
    requires configs::safety_spec(b,c),prefixes::unique_below(b,c,horizon,bound),0 <= time <= horizon,
        step(b,c,time) == Action::AdvanceCommit(i),b[time].nodes[i].term < bound,
        voters(b[time].nodes[i],c,i,b[time+1].nodes[i].commit as int).contains(j)
    ensures 0 <= at <= time,c.servers.contains(j),b[time+1].nodes[i].commit <= b[at].nodes[j].log.len(),
        b[at].nodes[j].term == b[time].nodes[i].term,
        sub(b[at].nodes[j].log,1,b[time+1].nodes[i].commit as int) == sub(b[time].nodes[i].log,1,b[time+1].nodes[i].commit as int)
{
    decision_certificate(b,c,time,i); let index=b[time+1].nodes[i].commit as int;
    if i == j { time }
    else { let received=match_prefix(b,c,horizon,bound,time,i,j,index); received+1 }
}
} // verus!
