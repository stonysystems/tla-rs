//! Election notifications, votes, and receipt maps refer only to configured servers.
use vstd::prelude::*;
use super::zk_election::*;
use super::zab::{Constants,Role,channels};
use super::zab_connections::channel_pair;
verus! {
broadcast use { vstd::map_lib::group_map_properties, vstd::set_lib::group_set_lib_default, vstd::seq_lib::group_seq_properties, vstd::seq_lib::group_filter_ensures };
pub open spec fn vote(v: Vote,c: Constants) -> bool { v.leader is Some && c.servers.contains(v.leader.unwrap()) }
pub open spec fn packet(m: Notification,c: Constants) -> bool {
    c.servers.contains(m.source) && vote(m.vote,c) && (m.role == Role::Leading ==> m.vote.leader == Some(m.source))
}
pub open spec fn node(n: LServer,c: Constants,i: int) -> bool {
    vote(n.vote,c) && (n.role == Role::Leading ==> n.vote.leader == Some(i)) && (n.role == Role::Following ==> n.vote.leader != Some(i))
    && n.received.dom() == c.servers && n.outside.dom() == c.servers && n.leading.subset_of(c.servers)
    && forall |p: int| 0 <= p < n.queue.len() && (#[trigger] n.queue[p]) is Some ==> packet(n.queue[p].unwrap(),c)
}
pub open spec fn cell(s: LState,c: Constants,i: int,j: int,p: int) -> bool { packet(s.msgs[(i,j)][p],c) && s.msgs[(i,j)][p].source == i }
pub open spec fn safe(s: LState,c: Constants) -> bool {
    s.nodes.dom() == c.servers && s.msgs.dom() == channels(c)
    && (forall |i: int| c.servers.contains(i) ==> #[trigger] node(s.nodes[i],c,i))
    && forall |i: int,j: int,p: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= p < s.msgs[(i,j)].len()
        ==> #[trigger] cell(s,c,i,j,p)
}
pub proof fn initial_safe(c: Constants)
    ensures safe(initial(c),c)
{
    let s=initial(c); assert(s.nodes.dom() =~= c.servers); assert(s.msgs.dom() =~= channels(c));
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(s.nodes[i],c,i) by {
        assert(s.nodes[i].received.dom() =~= c.servers); assert(s.nodes[i].outside.dom() =~= c.servers);
    }
    assert forall |i: int,j: int,p: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= p < s.msgs[(i,j)].len()
        implies #[trigger] cell(s,c,i,j,p) by { channel_pair(c,i,j); }
}
pub proof fn notification_ok(n: LServer,c: Constants,i: int)
    requires c.servers.contains(i),node(n,c,i)
    ensures packet(notification(n,i),c),notification(n,i).source == i
{}
pub proof fn reset_ok(n: LServer,c: Constants,i: int,cluster: bool)
    requires c.servers.contains(i),node(n,c,i)
    ensures node(reset(n,c,i,cluster),c,i)
{
    assert(reset(n,c,i,cluster).received.dom() =~= c.servers); assert(reset(n,c,i,cluster).outside.dom() =~= c.servers);
}
pub proof fn established_ok(n: LServer,c: Constants,i: int,m: Notification)
    requires c.servers.contains(i),node(n,c,i),packet(m,c),n.role == Role::Looking
    ensures node(established(n,c,i,m),c,i)
{
    assert(put(n.received,m).dom() =~= c.servers); assert(put(n.outside,m).dom() =~= c.servers);
    assert(vote_set(c,m.source,put(n.received,m),m.vote,m.round).subset_of(c.servers));
    assert(vote_set(c,m.source,put(n.outside,m),m.vote,m.round).subset_of(c.servers));
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires safe(s,c),enabled(s,c,a)
    ensures safe(apply(s,c,a),c)
{
    reveal(apply); let u=apply(s,c,a);
    match a {
        Action::Receive(i,j) => { channel_pair(c,i,j); channel_pair(c,j,i); assert(node(s.nodes[i],c,i)); assert(cell(s,c,j,i,0)); notification_ok(s.nodes[i],c,i); },
        Action::Handle(i) => {
            assert(node(s.nodes[i],c,i)); let n=s.nodes[i];
            if n.queue[0] is Some {
                let m=n.queue[0].unwrap(); assert(packet(m,c)); established_ok(n,c,i,m);
                assert(put(n.received,m).dom() =~= c.servers);
                assert(Map::new(c.servers,|j: int| if j == m.source { Received { vote: m.vote,round: m.round,role: Role::Looking,version: 1 } } else { blank_received() }).dom() =~= c.servers);
            }
        },
        Action::Wait(i) | Action::Timeout(i) => { assert(node(s.nodes[i],c,i)); },
    }
    assert(u.nodes.dom() =~= c.servers); assert(u.msgs.dom() =~= channels(c));
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u.nodes[i],c,i) by {
        assert(node(s.nodes[i],c,i));
        match a {
            Action::Receive(ai,j) => {
                if i == ai && s.nodes[i].role == Role::Looking {
                    let n=s.nodes[i]; let f=|m: Option<Notification>| m is Some;
                    assert forall |p: int| 0 <= p < u.nodes[i].queue.len() && (#[trigger] u.nodes[i].queue[p]) is Some implies packet(u.nodes[i].queue[p].unwrap(),c) by {
                        if p < n.queue.filter(f).len() {
                            let e=u.nodes[i].queue[p]; assert(n.queue.filter(f).contains(e)); n.queue.lemma_filter_contains_rev(f,e);
                            let q=choose |q: int| 0 <= q < n.queue.len() && n.queue[q] == e;
                        }
                    }
                }
            },
            Action::Handle(ai) => {
                if i == ai {
                    let n=s.nodes[i];
                    assert forall |p: int| 0 <= p < u.nodes[i].queue.len() && (#[trigger] u.nodes[i].queue[p]) is Some implies packet(u.nodes[i].queue[p].unwrap(),c) by { assert(u.nodes[i].queue[p] == n.queue[p+1]); }
                }
            },
            Action::Wait(ai) => {
                if i == ai {
                    let n=s.nodes[i];
                    assert forall |p: int| 0 <= p < u.nodes[i].queue.len() && (#[trigger] u.nodes[i].queue[p]) is Some implies packet(u.nodes[i].queue[p].unwrap(),c) by {
                        if n.queue.len() > 0 && n.queue[0] is Some {
                            if p < n.queue.len()-1 { assert(u.nodes[i].queue[p] == n.queue[p+1]); } else { assert(u.nodes[i].queue[p] == n.queue[0]); }
                        }
                    }
                }
            },
            _ => {},
        }
    }
    assert forall |i: int,j: int,p: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= p < u.msgs[(i,j)].len()
        implies #[trigger] cell(u,c,i,j,p) by {
        channel_pair(c,i,j);
        match a {
            Action::Receive(ai,aj) => {
                if i == ai && j == aj && i != j && p == s.msgs[(i,j)].len() { assert(u.msgs[(i,j)][p] == notification(s.nodes[i],i)); assert(node(s.nodes[i],c,i)); notification_ok(s.nodes[i],c,i); }
                else if i == aj && j == ai { assert(u.msgs[(i,j)][p] == s.msgs[(i,j)][p+1]); assert(cell(s,c,i,j,p+1)); }
                else { assert(u.msgs[(i,j)][p] == s.msgs[(i,j)][p]); assert(cell(s,c,i,j,p)); }
            },
            Action::Handle(ai) => {
                if p < s.msgs[(i,j)].len() { assert(u.msgs[(i,j)][p] == s.msgs[(i,j)][p]); assert(cell(s,c,i,j,p)); }
                else {
                    assert(i == ai); let m=u.msgs[(i,j)][p]; assert(m == notification(u.nodes[i],i)); assert(node(u.nodes[i],c,i)); notification_ok(u.nodes[i],c,i);
                }
            },
            _ => { assert(u.msgs[(i,j)][p] == s.msgs[(i,j)][p]); assert(cell(s,c,i,j,p)); },
        }
    }
}
pub proof fn same_messages(s: LState,u: LState,c: Constants)
    requires safe(s,c),s.msgs == u.msgs
    ensures u.msgs.dom() == channels(c),forall |i: int,j: int,p: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= p < u.msgs[(i,j)].len() ==> #[trigger] cell(u,c,i,j,p)
{
    assert forall |i: int,j: int,p: int| c.servers.contains(i) && c.servers.contains(j) && 0 <= p < u.msgs[(i,j)].len() implies #[trigger] cell(u,c,i,j,p) by { assert(cell(s,c,i,j,p)); }
}
pub proof fn replace_ok(s: LState,c: Constants,i: int,n: LServer)
    requires safe(s,c),c.servers.contains(i),node(n,c,i)
    ensures safe(replace(s,i,n),c)
{
    let u=replace(s,i,n); assert(u.nodes.dom() =~= c.servers); same_messages(s,u,c);
    assert forall |j: int| c.servers.contains(j) implies #[trigger] node(u.nodes[j],c,j) by { if j != i { assert(node(s.nodes[j],c,j)); } }
}
pub proof fn broadcast_ok(s: LState,c: Constants,i: int,m: Notification)
    requires safe(s,c),c.servers.contains(i),packet(m,c),m.source == i
    ensures safe(broadcast(s,i,m),c)
{
    let u=broadcast(s,i,m); assert(u.msgs.dom() =~= channels(c));
    assert forall |j: int,k: int,p: int| c.servers.contains(j) && c.servers.contains(k) && 0 <= p < u.msgs[(j,k)].len()
        implies #[trigger] cell(u,c,j,k,p) by {
        channel_pair(c,j,k); if p < s.msgs[(j,k)].len() { assert(u.msgs[(j,k)][p] == s.msgs[(j,k)][p]); assert(cell(s,c,j,k,p)); }
        else { assert(j == i); assert(u.msgs[(j,k)][p] == m); }
    }
}
pub proof fn timeout_ok(s: LState,c: Constants,i: int)
    requires safe(s,c),c.servers.contains(i)
    ensures safe(timeout(s,c,i),c)
{
    assert(node(s.nodes[i],c,i)); reset_ok(s.nodes[i],c,i,false); let n=reset(s.nodes[i],c,i,false);
    replace_ok(s,c,i,n); notification_ok(n,c,i); broadcast_ok(replace(s,i,n),c,i,notification(n,i));
}
pub proof fn current_frame(s: LState,c: Constants,a: Action,i: int)
    requires safe(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures apply(s,c,a).nodes[i].current == s.nodes[i].current
{
    reveal(apply);
}
pub proof fn history_frame(s: LState,c: Constants,a: Action,i: int)
    requires safe(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures super::zab_log_math::same(s.nodes[i].history,apply(s,c,a).nodes[i].history)
{
    reveal(apply); let old=s.nodes[i].history; let new=apply(s,c,a).nodes[i].history;
    assert forall |p: int| 0 <= p < old.len() implies #[trigger] super::zab::equal(old[p],new[p]) by {}
}
} // verus!
