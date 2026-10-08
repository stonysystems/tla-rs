//! FIFO proposals are preceded by the new-leader synchronization they require.
use vstd::prelude::*;
use super::zab::*;
use super::zab_connections as connections;
use super::zab_epochs as epochs;
use super::zab_phases as phases;
use super::zab_receipts as receipts;
use super::temporal::Behavior;
verus! {
pub open spec fn leader_message(m: Message,e: int) -> bool { match m { Message::NewLeader(epoch,_) => epoch == e,_ => false } }
pub open spec fn pending(q: Seq<Message>,e: int,limit: int) -> bool {
    0 <= limit <= q.len() && exists |k: int| 0 <= k < limit && #[trigger] leader_message(q[k],e)
}
pub proof fn pending_push(q: Seq<Message>,e: int,limit: int,m: Message)
    ensures pending(q,e,limit) ==> pending(q.push(m),e,limit),
        leader_message(m,e) ==> pending(q.push(m),e,q.len() as int+1)
{
    if pending(q,e,limit) {
        let k=choose |k: int| #![trigger q[k]] 0 <= k < limit && leader_message(q[k],e);
        assert(leader_message(q.push(m)[k],e));
    }
    if leader_message(m,e) { assert(leader_message(q.push(m)[q.len() as int],e)); }
}
pub proof fn pending_tail(q: Seq<Message>,e: int,limit: int)
    requires pending(q,e,limit),!leader_message(q[0],e)
    ensures pending(q.drop_first(),e,limit-1)
{
    let k=choose |k: int| #![trigger q[k]] 0 <= k < limit && leader_message(q[k],e);
    assert(k > 0); assert(leader_message(q.drop_first()[k-1],e));
}
pub open spec fn ready(s: LState,c: Constants,i: int,j: int) -> bool {
    s.nodes[i].role == Role::Leading && s.nodes[i].phase != Phase::Discovery && ae_connected(s.nodes[i].ae).contains(j) ==>
        s.nodes[j].current == s.nodes[i].current || pending(s.msgs[(i,j)],s.nodes[i].current,s.msgs[(i,j)].len() as int)
}
pub open spec fn fifo(s: LState,c: Constants,i: int,j: int) -> bool {
    forall |k: int| 0 <= k < s.msgs[(i,j)].len() && (#[trigger] s.msgs[(i,j)][k]) is Propose ==>
        s.nodes[j].current == s.nodes[i].current || pending(s.msgs[(i,j)],s.nodes[i].current,k)
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    receipts::inductive(s,c)
    && (forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) ==> #[trigger] ready(s,c,i,j))
    && (forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) ==> #[trigger] fifo(s,c,i,j))
}
pub proof fn initial_inductive(c: Constants)
    ensures inductive(initial(c),c)
{
    receipts::initial_inductive(c);
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] ready(initial(c),c,i,j) by {}
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] fifo(initial(c),c,i,j) by { connections::channel_pair(c,i,j); }
}
pub proof fn connected_ae(s: LState,c: Constants,i: int,j: int)
    requires receipts::inductive(s,c),c.servers.contains(i),c.servers.contains(j),s.nodes[i].role == Role::Leading,ae_connected(s.nodes[i].ae).contains(j)
    ensures s.nodes[i].learners.contains(j),s.nodes[j].accepted == s.nodes[i].accepted
{
    receipts::facts(s,c,i,j);
    let r=choose |r: AE| #![trigger s.nodes[i].ae.contains(r)] s.nodes[i].ae.contains(r) && r.connected && r.sid == j;
    assert(s.nodes[i].ae.contains(r) && r.connected && r.sid == j);
}
pub proof fn connected_change(q: Set<AE>,who: int,e: int,h: Seq<Txn>)
    ensures ae_connected(disconnect_ae(q,who)).subset_of(ae_connected(q)),
        ae_connected(update_ae(q,who,e,h)).subset_of(ae_connected(q).insert(who))
{
    assert forall |j: int| #![trigger ae_connected(q).contains(j)] ae_connected(disconnect_ae(q,who)).contains(j) implies ae_connected(q).contains(j) by {
        let r=choose |r: AE| #![trigger disconnect_ae(q,who).contains(r)] disconnect_ae(q,who).contains(r) && r.connected && r.sid == j;
        assert(q.contains(r) && r.connected); assert(q.filter(|x: AE| x.connected).contains(r));
    }
    assert forall |j: int| #![trigger ae_connected(q).insert(who).contains(j)] ae_connected(update_ae(q,who,e,h)).contains(j) implies ae_connected(q).insert(who).contains(j) by {
        let r=choose |r: AE| #![trigger update_ae(q,who,e,h).contains(r)] update_ae(q,who,e,h).contains(r) && r.connected && r.sid == j;
        if j != who { assert(q.contains(r) && r.connected); assert(q.filter(|x: AE| x.connected).contains(r)); }
    }
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn preserve_ready(s: LState,c: Constants,a: Action,i: int,j: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j)
    ensures ready(apply(s,c,a),c,i,j)
{
    hide(update_ack);
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,j); connections::channel_pair(c,i,j);
    assert(ready(s,c,i,j));
    receipts::preserve(s,c,a); let u=apply(s,c,a);
    if u.nodes[i].role == Role::Leading && u.nodes[i].phase != Phase::Discovery && ae_connected(u.nodes[i].ae).contains(j) { connected_ae(u,c,i,j); }
    if s.nodes[i].role == Role::Leading && ae_connected(s.nodes[i].ae).contains(j) { connected_ae(s,c,i,j); }
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            receipts::facts(s,c,x,y); receipts::facts(s,c,i,x); receipts::facts(s,c,i,y); receipts::facts(s,c,j,x); receipts::facts(s,c,j,y);
            connected_change(s.nodes[x].ae,y,0,Seq::empty()); connected_change(s.nodes[y].ae,x,0,Seq::empty());
            if a == Action::AckEpoch(x,y) { if let Message::AckEpoch(e,h)=s.msgs[(y,x)][0] { connected_change(s.nodes[x].ae,y,e,h); } }
        },
        Action::Restart(x) => { receipts::facts(s,c,i,x); receipts::facts(s,c,j,x); if let Some(y)=s.nodes[x].leader { receipts::facts(s,c,x,y); receipts::facts(s,c,i,y); receipts::facts(s,c,j,y); connected_change(s.nodes[y].ae,x,0,Seq::empty()); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { receipts::facts(s,c,i,x); receipts::facts(s,c,j,x); },
        _ => {},
    }
    if pending(s.msgs[(i,j)],s.nodes[i].current,s.msgs[(i,j)].len() as int) {
        let k=choose |k: int| #![trigger s.msgs[(i,j)][k]] 0 <= k < s.msgs[(i,j)].len() && leader_message(s.msgs[(i,j)][k],s.nodes[i].current);
        assert(phases::packet(s,c,i,j,s.msgs[(i,j)][k])); assert(epochs::packet(s,c,i,j,s.msgs[(i,j)][k]));
        if k > 0 { assert(leader_message(s.msgs[(i,j)].drop_first()[k-1],s.nodes[i].current)); }
        if k < u.msgs[(i,j)].len() && leader_message(u.msgs[(i,j)][k],u.nodes[i].current) {
            assert(pending(u.msgs[(i,j)],u.nodes[i].current,u.msgs[(i,j)].len() as int));
        }
        if k > 0 && k-1 < u.msgs[(i,j)].len() && leader_message(u.msgs[(i,j)][k-1],u.nodes[i].current) {
            assert(pending(u.msgs[(i,j)],u.nodes[i].current,u.msgs[(i,j)].len() as int));
        }
    }
    let last=u.msgs[(i,j)].len() as int-1;
    if last >= 0 && leader_message(u.msgs[(i,j)][last],u.nodes[i].current) {
        assert(pending(u.msgs[(i,j)],u.nodes[i].current,u.msgs[(i,j)].len() as int));
    }
    if u.nodes[i].role == Role::Leading && u.nodes[i].phase != Phase::Discovery && ae_connected(u.nodes[i].ae).contains(j) && u.nodes[j].current != u.nodes[i].current {
        assert(pending(u.msgs[(i,j)],u.nodes[i].current,u.msgs[(i,j)].len() as int));
    }
}
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub proof fn preserve_position(s: LState,c: Constants,a: Action,i: int,j: int,k: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i),c.servers.contains(j),0 <= k < apply(s,c,a).msgs[(i,j)].len(),apply(s,c,a).msgs[(i,j)][k] is Propose
    ensures apply(s,c,a).nodes[j].current == apply(s,c,a).nodes[i].current || pending(apply(s,c,a).msgs[(i,j)],apply(s,c,a).nodes[i].current,k)
{
    hide(update_ack);
    reveal(enabled); reveal(apply); receipts::facts(s,c,i,j); connections::channel_pair(c,i,j);
    assert(ready(s,c,i,j) && fifo(s,c,i,j));
    receipts::preserve(s,c,a); let u=apply(s,c,a);
    assert(phases::packet(u,c,i,j,u.msgs[(i,j)][k]));
    match a {
        Action::Timeout(x,y) | Action::Connect(x,y) | Action::CEpoch(x,y) | Action::NewEpoch(x,y) | Action::AckEpoch(x,y) | Action::NewLeader(x,y) | Action::AckLd(x,y) | Action::CommitLd(x,y) | Action::Propose(x,y) | Action::Ack(x,y) | Action::Commit(x,y) => {
            receipts::facts(s,c,x,y); receipts::facts(s,c,i,x); receipts::facts(s,c,i,y); receipts::facts(s,c,j,x); receipts::facts(s,c,j,y);
        },
        Action::Restart(x) => { receipts::facts(s,c,i,x); receipts::facts(s,c,j,x); if let Some(y)=s.nodes[x].leader { receipts::facts(s,c,x,y); receipts::facts(s,c,i,y); receipts::facts(s,c,j,y); } },
        Action::UpdateLeader(x) | Action::FollowLeader(x) | Action::Request(x) | Action::Broadcast(x) => { receipts::facts(s,c,i,x); receipts::facts(s,c,j,x); },
        _ => {},
    }
    let q=s.msgs[(i,j)]; let e=s.nodes[i].current;
    if k < q.len() && q[k] is Propose { assert(phases::packet(s,c,i,j,q[k])); assert(s.nodes[j].current == e || pending(q,e,k)); }
    if k+1 < q.len() && q[k+1] is Propose { assert(phases::packet(s,c,i,j,q[k+1])); assert(s.nodes[j].current == e || pending(q,e,k+1)); }
    if pending(q,e,k) { let p=choose |p: int| #![trigger q[p]] 0 <= p < k && leader_message(q[p],e); assert(leader_message(q.push(u.msgs[(i,j)].last())[p],e)); }
    if pending(q,e,k+1) && !leader_message(q[0],e) { pending_tail(q,e,k+1); }
    if pending(q,e,q.len() as int) { let p=choose |p: int| #![trigger q[p]] 0 <= p < q.len() && leader_message(q[p],e); assert(leader_message(q.push(u.msgs[(i,j)].last())[p],e)); }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    receipts::preserve(s,c,a); let u=apply(s,c,a);
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] ready(u,c,i,j) by { preserve_ready(s,c,a,i,j); }
    assert forall |i: int,j: int| c.servers.contains(i) && c.servers.contains(j) implies #[trigger] fifo(u,c,i,j) by {
        assert forall |k: int| 0 <= k < u.msgs[(i,j)].len() && (#[trigger] u.msgs[(i,j)][k]) is Propose implies
            u.nodes[j].current == u.nodes[i].current || pending(u.msgs[(i,j)],u.nodes[i].current,k) by { preserve_position(s,c,a,i,j,k); }
    }
}
pub proof fn at(b: Behavior<LState>,c: Constants,k: int)
    requires connections::safety_spec(b,c),k >= 0
    ensures inductive(b[k],c)
    decreases k
{
    if k == 0 { initial_inductive(c); }
    else {
        at(b,c,k-1); let time=k-1; assert(next(b[time],b[time+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[time],c,a) && b[time+1] == apply(b[time],c,a);
        preserve(b[time],c,a);
    }
}
} // verus!
