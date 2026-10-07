//! Retention of a prefix while all applicable append histories are compatible.
//! The compatibility premise is an obligation for the cross-term election proof.
use vstd::prelude::*;
use super::etcd::{*,sub};
use super::etcd_election as election;
use super::etcd_logs as logs;
use super::etcd_transmissions as events;
use super::temporal::Behavior;
verus! {
pub open spec fn compatible(h: Seq<nat>,v: Seq<nat>) -> bool { logs::prefix_of(h,v) || logs::prefix_of(v,h) }
pub open spec fn packet(h: Seq<nat>,m: Message) -> bool {
    exists |v: Seq<nat>| logs::segment(m,v) && #[trigger] compatible(h,v)
}
pub open spec fn applicable(s: LState,i: int,h: Seq<nat>,bound: nat) -> bool {
    forall |m: Message| #[trigger] s.messages.count(m) > 0 && m.dest == i && m.term == s.nodes[i].term && m.term <= bound && m.body is AppendRequest ==> packet(h,m)
}
pub open spec fn live(s: LState,i: int,h: Seq<nat>,bound: nat) -> bool {
    s.nodes[i].term <= bound ==> logs::prefix_of(h,s.nodes[i].log)
}
pub open spec fn durable(s: LState,i: int,h: Seq<nat>,bound: nat) -> bool {
    s.nodes[i].disk.term <= bound ==> logs::prefix_of(h,s.nodes[i].disk.log)
}
pub proof fn equal_overlap(h: Seq<nat>,v: Seq<nat>,k: int)
    requires compatible(h,v),0 <= k < h.len(),k < v.len()
    ensures h[k] == v[k]
{}
pub proof fn conflict_above_prefix(n: LServer,m: Message,h: Seq<nat>,v: Seq<nat>)
    requires logs::prefix_of(h,n.log),logs::segment(m,v),compatible(h,v),m.body is AppendRequest,
        log_ok(n,m.body->AppendRequest_prev,m.body->AppendRequest_prev_term),
        !no_conflict(n,m.body->AppendRequest_prev+1,m.body->AppendRequest_entries)
    ensures n.log.len() > h.len()
{
    let prev=m.body->AppendRequest_prev; let entries=m.body->AppendRequest_entries;
    if n.log.len() <= h.len() {
        assert(n.log.len() == h.len());
        assert forall |k: int| 0 <= k < entries.len() && prev+1+k <= n.log.len() implies n.log[prev+k] == #[trigger] entries[k] by {
            assert(entries[k] == v[prev+k]); equal_overlap(h,v,prev+k); assert(h[prev+k] == n.log[prev+k]);
        }
        assert(no_conflict(n,prev+1,entries)); assert(false);
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action,i: int,h: Seq<nat>,bound: nat)
    requires election::inductive(s,c),enabled(s,c,a),c.servers.contains(i),live(s,i,h,bound),applicable(s,i,h,bound),
        a == Action::Restart(i) ==> durable(s,i,h,bound)
    ensures live(apply(s,c,a),i,h,bound),
        durable(s,i,h,bound) ==> durable(apply(s,c,a),i,h,bound)
{
    reveal(enabled); reveal(apply); reveal(receive_enabled); reveal(receive);
    let n=s.nodes[i]; let u=apply(s,c,a); assert(election::node_inv(s,c,i));
    if u.nodes[i].term <= bound {
        if let Action::Receive { m,how } = a {
            if m.dest == i && how == Receive::AppendConflict {
                assert(packet(h,m)); let v=choose |v: Seq<nat>| logs::segment(m,v) && #[trigger] compatible(h,v);
                conflict_above_prefix(n,m,h,v);
                assert(logs::prefix_of(h,sub(n.log,1,n.log.len()-1)));
            }
        }
        assert forall |k: int| 0 <= k < h.len() implies #[trigger] h[k] == #[trigger] u.nodes[i].log[k] by {
            if a == Action::Restart(i) { assert(h[k] == n.disk.log[k]); }
            else { assert(h[k] == n.log[k]); }
        }
    }
}
pub proof fn durable_interval(b: Behavior<LState>,c: Constants,i: int,h: Seq<nat>,bound: nat,lo: int,hi: int)
    requires election::safety_spec(b,c),c.servers.contains(i),0 <= lo <= hi,live(b[lo],i,h,bound),durable(b[lo],i,h,bound),
        forall |r: int| lo <= r < hi ==> #[trigger] applicable(b[r],i,h,bound)
    ensures live(b[hi],i,h,bound),durable(b[hi],i,h,bound)
    decreases hi-lo
{
    if hi > lo {
        durable_interval(b,c,i,h,bound,lo,hi-1); events::step_valid(b,c,hi-1); election::safety_at(b,c,hi-1);
        preserve(b[hi-1],c,events::step(b,c,hi-1),i,h,bound);
    }
}
pub proof fn pending_interval(b: Behavior<LState>,c: Constants,i: int,h: Seq<nat>,bound: nat,lo: int,hi: int,m: Message)
    requires election::safety_spec(b,c),c.servers.contains(i),0 <= lo <= hi,live(b[lo],i,h,bound),m.source == i,
        forall |r: int| lo <= r < hi ==> #[trigger] applicable(b[r],i,h,bound),
        forall |r: int| lo < r <= hi ==> #[trigger] b[r].pending.count(m) > 0
    ensures live(b[hi],i,h,bound)
    decreases hi-lo
{
    if hi > lo {
        pending_interval(b,c,i,h,bound,lo,hi-1,m); events::step_valid(b,c,hi-1); election::safety_at(b,c,hi-1);
        assert(b[hi].pending.count(m) > 0); events::pending_survives(b[hi-1],c,events::step(b,c,hi-1),m);
        preserve(b[hi-1],c,events::step(b,c,hi-1),i,h,bound);
    }
}
// A value held when an acknowledgment is formed is protected until a later
// vote, even if that acknowledgment's Ready occurs after the vote grant.
pub proof fn acknowledgment_to_vote(b: Behavior<LState>,c: Constants,i: int,h: Seq<nat>,bound: nat,start: int,release: int,grant: int,m: Message)
    requires election::safety_spec(b,c),c.servers.contains(i),0 <= start <= release,start <= grant,m.source == i,
        live(b[start],i,h,bound),events::step(b,c,release) == Action::Ready(i),
        forall |r: int| start < r <= release ==> #[trigger] b[r].pending.count(m) > 0,
        forall |r: int| start <= r < grant ==> #[trigger] applicable(b[r],i,h,bound),
        b[grant].nodes[i].term <= bound
    ensures logs::prefix_of(h,b[grant].nodes[i].log)
{
    if grant <= release { pending_interval(b,c,i,h,bound,start,grant,m); }
    else {
        pending_interval(b,c,i,h,bound,start,release,m); events::step_valid(b,c,release); election::safety_at(b,c,release);
        reveal(apply);
        assert(live(b[release+1],i,h,bound) && durable(b[release+1],i,h,bound));
        durable_interval(b,c,i,h,bound,release+1,grant);
    }
}
} // verus!
