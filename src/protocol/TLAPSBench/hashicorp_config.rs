use vstd::prelude::*;
use super::hashicorp::*;
use super::temporal::Behavior;
verus! {
pub proof fn config_positions(log: Seq<Entry>)
    ensures previous_config(log) <= last_config(log) <= log.len(),
        forall |k: int| 1 <= k <= log.len() && (#[trigger] log[k-1]).kind == EntryKind::Config ==>
            k <= last_config(log) && (k == last_config(log) || k <= previous_config(log))
    decreases log.len()
{
    if log.len() > 0 {
        config_positions(log.drop_last());
        assert forall |k: int| 1 <= k <= log.len() && (#[trigger] log[k-1]).kind == EntryKind::Config implies
            k <= last_config(log) && (k == last_config(log) || k <= previous_config(log)) by {
            if k < log.len() { assert(log.drop_last()[k-1] == log[k-1]); }
        }
    }
}
pub proof fn push_config_positions(log: Seq<Entry>, e: Entry)
    ensures last_config(log.push(e)) == if e.kind == EntryKind::Config { log.len()+1 } else { last_config(log) },
        previous_config(log.push(e)) == if e.kind == EntryKind::Config { last_config(log) } else { previous_config(log) }
{
    assert(log.push(e).drop_last() =~= log);
}
pub open spec fn node_inv(n: LServer) -> bool {
    n.latest_config_index == last_config(n.log) && previous_config(n.log) <= n.committed_config_index <= n.latest_config_index
}
pub open spec fn inductive(s: LState,c: Constants) -> bool {
    forall |i: int| c.servers.contains(i) ==> #[trigger] node_inv(s.nodes[i])
}
pub proof fn initial_inductive(c: Constants)
    ensures inductive(initial(c),c)
{}
pub proof fn preserve_node(s: LState,c: Constants,a: Action,i: int)
    requires inductive(s,c),enabled(s,c,a),c.servers.contains(i)
    ensures node_inv(apply(s,c,a).nodes[i])
{
    reveal(enabled); reveal(protocol_apply); reveal(receive); reveal(receive_enabled);
    let n=s.nodes[i]; let u=apply(s,c,a);
    assert(node_inv(n));
    config_positions(n.log);
    config_positions(u.nodes[i].log);
    match a {
        Action::ClientRequest { i: j,value } => if i == j {
            push_config_positions(n.log,Entry { term: n.term,kind: EntryKind::Value,config: Set::empty(),value: Some(value) });
        },
        Action::ProposeConfig { i: j,member } => if i == j {
            let config=if n.latest_config.contains(member) { n.latest_config.remove(member) } else { n.latest_config.insert(member) };
            push_config_positions(n.log,Entry { term: n.term,kind: EntryKind::Config,config,value: None });
        }, _ => {},
    }
}
pub proof fn preserve_inductive(s: LState,c: Constants,a: Action)
    requires inductive(s,c),enabled(s,c,a)
    ensures inductive(apply(s,c,a),c)
{
    assert forall |i: int| c.servers.contains(i) implies #[trigger] node_inv(apply(s,c,a).nodes[i]) by { preserve_node(s,c,a,i); }
}
pub proof fn pending_at_most_one(n: LServer)
    requires node_inv(n)
    ensures pending_configs(n).len() <= 1
{
    config_positions(n.log);
    let singleton=set![last_config(n.log) as int];
    assert(pending_configs(n).subset_of(singleton)) by {
        assert forall |k: int| #![trigger singleton.contains(k)] pending_configs(n).contains(k) implies singleton.contains(k) by {
            assert(k == last_config(n.log));
        }
    }
    vstd::set_lib::lemma_len_subset(pending_configs(n),singleton);
}
pub proof fn configuration_from_inductive(s: LState,c: Constants)
    requires inductive(s,c)
    ensures configuration_safety(s,c)
{
    assert forall |i: int| #![trigger c.servers.contains(i)] c.servers.contains(i) && s.nodes[i].role == Role::Leader implies pending_configs(s.nodes[i]).len() <= 1 by { pending_at_most_one(s.nodes[i]); }
}
pub open spec fn safety_spec(b: Behavior<LState>,c: Constants) -> bool {
    valid_constants(c) && b[0] == initial(c)
    && (forall |k: int| k >= 0 ==> b.dom().contains(k))
    && forall |k: int| k >= 0 ==> #[trigger] next(b[k],b[k+1],c)
}
pub proof fn safety_at(b: Behavior<LState>,c: Constants,k: int)
    requires safety_spec(b,c),k >= 0
    ensures inductive(b[k],c),configuration_safety(b[k],c)
    decreases k
{
    if k == 0 { initial_inductive(c); }
    else {
        safety_at(b,c,k-1); let i=k-1;
        assert(next(b[i],b[i+1],c)); reveal(next);
        let a=choose |a: Action| #[trigger] enabled(b[i],c,a) && b[i+1] == apply(b[i],c,a);
        preserve_inductive(b[i],c,a);
    }
    configuration_from_inductive(b[k],c);
}
pub proof fn configuration_safety_correct(b: Behavior<LState>,c: Constants)
    requires safety_spec(b,c)
    ensures forall |k: int| k >= 0 ==> #[trigger] configuration_safety(b[k],c)
{
    assert forall |k: int| k >= 0 implies #[trigger] configuration_safety(b[k],c) by { safety_at(b,c,k); }
}
} // verus!
