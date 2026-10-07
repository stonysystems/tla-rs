//! Configuration, channel, and log-merge facts for the HashiCorp model.
use vstd::prelude::*;
use super::hashicorp::{*,sub};
use super::hashicorp_config as configs;
use super::temporal::Behavior;
verus! {
pub open spec fn entry(e: Entry,c: Constants) -> bool {
    e.kind == EntryKind::Config ==> !e.config.is_empty() && e.config.subset_of(c.servers)
}
pub open spec fn log(h: Seq<Entry>,c: Constants) -> bool {
    forall |k: int| 0 <= k < h.len() ==> #[trigger] entry(h[k],c)
}
pub open spec fn node(n: LServer,c: Constants) -> bool {
    log(n.log,c) && n.latest_config == config_at(n.log,last_config(n.log),c)
    && !n.latest_config.is_empty() && n.latest_config.subset_of(c.servers)
    && n.next_index.dom() == c.servers && n.matched.dom() == c.servers
    && (forall |j: int| c.servers.contains(j) ==> #[trigger] n.next_index[j] >= 1)
    && n.granted.subset_of(c.servers) && n.contacts.subset_of(c.servers)
    && (n.pending_vote is Some ==> c.servers.contains(n.pending_vote.unwrap().candidate))
    && (n.voted_for is Some ==> c.servers.contains(n.voted_for.unwrap()))
    && (n.persisted_voted_for is Some ==> c.servers.contains(n.persisted_voted_for.unwrap()))
}
pub open spec fn message(m: Message,c: Constants) -> bool {
    c.servers.contains(m.source) && c.servers.contains(m.dest)
    && match m.body {
        Body::AppendRequest { prev,entries,.. } => prev >= 0 && log(entries,c),
        Body::AppendResponse { matched,.. } => matched >= 0,
        _ => true,
    }
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    valid_constants(c) && s.nodes.dom() == c.servers
    && (forall |i: int| c.servers.contains(i) ==> #[trigger] node(s.nodes[i],c))
    && (forall |m: Message| #[trigger] s.messages.count(m) > 0 ==> message(m,c))
}
pub open spec fn merge_point(old: Seq<Entry>,prev: int,entries: Seq<Entry>,k: int) -> bool {
    1 <= k <= entries.len()+1
    && (forall |j: int| 0 <= j < k-1 ==> prev+j < old.len() && old[prev+j].term == (#[trigger] entries[j]).term)
    && (k == entries.len()+1 || prev+k > old.len() || old[prev+k-1].term != (#[trigger] entries[k-1]).term)
}
pub proof fn first_mismatch(old: Seq<Entry>,prev: int,entries: Seq<Entry>,start: int) -> (k: int)
    requires 0 <= prev <= old.len(),1 <= start <= entries.len()+1,
        forall |j: int| 0 <= j < start-1 ==> prev+j < old.len() && old[prev+j].term == (#[trigger] entries[j]).term
    ensures merge_point(old,prev,entries,k)
    decreases entries.len()+1-start
{
    if start <= entries.len() && prev+start <= old.len() && old[prev+start-1].term == entries[start-1].term {
        assert forall |j: int| 0 <= j < start implies prev+j < old.len() && old[prev+j].term == (#[trigger] entries[j]).term by {
            if j < start-1 { assert(old[prev+j].term == entries[j].term); }
        }
        first_mismatch(old,prev,entries,start+1)
    } else { start }
}
pub proof fn merge_log(old: Seq<Entry>,prev: int,entries: Seq<Entry>,c: Constants)
    requires log(old,c),log(entries,c),0 <= prev <= old.len()
    ensures log(merge(old,prev,entries),c)
{
    first_mismatch(old,prev,entries,1); reveal(merge);
    let first=choose |k: int| 1 <= k <= entries.len()+1
        && (forall |j: int| 0 <= j < k-1 ==> prev+j < old.len() && old[prev+j].term == (#[trigger] entries[j]).term)
        && (k == entries.len()+1 || prev+k > old.len() || old[prev+k-1].term != (#[trigger] entries[k-1]).term);
    assert(merge_point(old,prev,entries,first));
    if entries.len() > 0 && first != entries.len()+1 {
        if first > 1 { assert(old[prev+first-2].term == entries[first-2].term); assert(prev+first-1 <= old.len()); }
        let out=merge(old,prev,entries);
        assert forall |k: int| 0 <= k < out.len() implies #[trigger] entry(out[k],c) by {
            if k < prev+first-1 { assert(entry(old[k],c)); }
            else { assert(entry(entries[k-prev],c)); }
        }
    }
}
pub open spec fn original_point(old: Seq<Entry>,prev: int,entries: Seq<Entry>,k: int) -> bool {
    1 <= k <= entries.len()+1
    && (forall |j: int| 1 <= j < k ==> prev+j <= old.len() && old[prev+j-1].term == (#[trigger] entries[j-1]).term)
    && (k == entries.len()+1 || prev+k > old.len() || old[prev+k-1].term != (#[trigger] entries[k-1]).term)
}
pub open spec fn original_merge(old: Seq<Entry>,prev: int,entries: Seq<Entry>) -> Seq<Entry> {
    let first=choose |k: int| original_point(old,prev,entries,k);
    if entries.len() == 0 || first == entries.len()+1 { old }
    else { sub(old,1,prev+first-1)+sub(entries,first,entries.len() as int) }
}
pub proof fn point_correspondence(old: Seq<Entry>,prev: int,entries: Seq<Entry>,k: int)
    requires merge_point(old,prev,entries,k)
    ensures original_point(old,prev,entries,k)
{
    assert forall |j: int| 1 <= j < k implies prev+j <= old.len() && old[prev+j-1].term == (#[trigger] entries[j-1]).term by {
        assert(prev+(j-1) < old.len() && old[prev+(j-1)].term == entries[j-1].term);
    }
}
pub proof fn merge_correspondence(old: Seq<Entry>,prev: int,entries: Seq<Entry>)
    requires 0 <= prev <= old.len()
    ensures merge(old,prev,entries) == original_merge(old,prev,entries)
{
    let witness=first_mismatch(old,prev,entries,1); point_correspondence(old,prev,entries,witness);
    reveal(merge);
    let first=choose |k: int| 1 <= k <= entries.len()+1
        && (forall |j: int| 0 <= j < k-1 ==> prev+j < old.len() && old[prev+j].term == (#[trigger] entries[j]).term)
        && (k == entries.len()+1 || prev+k > old.len() || old[prev+k-1].term != (#[trigger] entries[k-1]).term);
    let original=choose |k: int| original_point(old,prev,entries,k);
    assert(merge_point(old,prev,entries,first));
    assert(original_point(old,prev,entries,original));
    if first < original {
        assert(old[prev+first-1].term == entries[first-1].term);
        assert(prev+first <= old.len()); assert(false);
    } else if original < first {
        assert(old[prev+original-1].term == entries[original-1].term);
        assert(prev+original <= old.len()); assert(false);
    }
    assert(first == original);
}
pub proof fn last_config_valid(h: Seq<Entry>)
    ensures last_config(h) <= h.len(),last_config(h) > 0 ==> h[last_config(h)-1].kind == EntryKind::Config
    decreases h.len()
{
    if h.len() > 0 {
        last_config_valid(h.drop_last());
        if h.last().kind != EntryKind::Config && last_config(h) > 0 {
            assert(h[last_config(h)-1] == h.drop_last()[last_config(h)-1]);
        }
    }
}
pub proof fn last_config_members(h: Seq<Entry>,c: Constants)
    requires log(h,c),valid_constants(c)
    ensures !config_at(h,last_config(h),c).is_empty(),config_at(h,last_config(h),c).subset_of(c.servers)
{
    last_config_valid(h);
    if last_config(h) > 0 { assert(entry(h[last_config(h)-1],c)); }
}
pub proof fn initial_inductive(c: Constants)
    requires valid_constants(c)
    ensures inductive(initial(c),c)
{ broadcast use vstd::multiset::group_multiset_axioms; }
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures node(apply(s,c,a).nodes[i],c)
{
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
    let n=s.nodes[i]; let u=apply(s,c,a); assert(node(n,c)); last_config_valid(n.log);
    match a {
        Action::ClientRequest { i: j,value } => if i == j {
            let e=Entry { term: n.term,kind: EntryKind::Value,config: Set::empty(),value: Some(value) };
            configs::push_config_positions(n.log,e);
            assert(log(n.log.push(e),c));
            assert(config_at(n.log.push(e),last_config(n.log.push(e)),c) == n.latest_config);
            assert(u.nodes[i].log == n.log.push(e));
            assert(node(u.nodes[i],c));
        } else { assert(u.nodes[i] == n); assert(node(u.nodes[i],c)); },
        Action::ProposeConfig { i: j,member } => if i == j {
            let q=if n.latest_config.contains(member) { n.latest_config.remove(member) } else { n.latest_config.insert(member) };
            let e=Entry { term: n.term,kind: EntryKind::Config,config: q,value: None };
            if n.latest_config.contains(member) {
                assert(n.latest_config.remove(member).len() == n.latest_config.len()-1);
            }
            assert(entry(e,c)); configs::push_config_positions(n.log,e); assert(log(n.log.push(e),c));
        },
        Action::Receive { m,how } => {
            assert(message(m,c));
            if m.dest == i && how == Receive::AcceptAppend {
                merge_log(n.log,m.body->AppendRequest_prev,m.body->AppendRequest_entries,c);
                last_config_members(u.nodes[i].log,c);
            }
        },
        Action::Crash(j) => if i == j { last_config_members(n.log,c); },
        _ => {},
    }
    assert(u.nodes[i].next_index.dom() =~= c.servers);
}
pub proof fn preserve_message(s: LState,c: Constants,a: Action,m: Message)
    requires inductive(s,c),enabled(s,c,a),apply(s,c,a).messages.count(m) > 0
    ensures message(m,c)
{
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive);
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use Set::lemma_map_contains;
    if s.messages.count(m) > 0 { assert(message(m,c)); }
    else {
        if let Action::Receive { m: old,how } = a { assert(message(old,c)); }
        match a {
            Action::Timeout(i) => {
                assert(node(s.nodes[i],c));
                let q=s.nodes[i].latest_config.remove(i).map(|j: int| Message { source: i,dest: j,term: s.nodes[i].term+1,body: Body::VoteRequest {
                    last_term: log_term(s.nodes[i].log,s.nodes[i].log.len() as int),last_index: s.nodes[i].log.len() } });
                assert(q.contains(m));
            },
            Action::Replicate { i,j } => { assert(node(s.nodes[i],c)); },
            Action::CompleteVote(i) => { assert(node(s.nodes[i],c)); },
            _ => {},
        }
    }
}
pub proof fn preserve(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    reveal(enabled); reveal(protocol_apply); reveal(receive_enabled); reveal(receive); let u=apply(s,c,a);
    if let Action::Receive { m,how } = a { assert(message(m,c)); }
    assert(u.nodes.dom() =~= c.servers);
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node(u.nodes[i],c) by { preserve_node(s,c,a,i); }
    assert forall |m: Message| #[trigger] u.messages.count(m) > 0 implies message(m,c) by { preserve_message(s,c,a,m); }
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,time: int)
    requires configs::safety_spec(b,c),time >= 0
    ensures inductive(b[time],c)
    decreases time
{
    if time == 0 { initial_inductive(c); }
    else {
        safety_at(b,c,time-1); let p=time-1; assert(next(b[p],b[p+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[time-1],c,a) && b[time] == apply(b[time-1],c,a);
        preserve(b[time-1],c,a);
    }
}
} // verus!
