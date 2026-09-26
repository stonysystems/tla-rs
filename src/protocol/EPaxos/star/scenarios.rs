//! A concrete reachable commit, execution, reboot, and recovery.
//! This witness checks that the safety model permits useful executions.
use super::types::*;
use super::model::*;
use super::recovery::*;
use super::execution::*;
use super::behavior::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub open spec fn example_constants() -> Constants {
    Constants { n: 3, f: 1, e: 0, conflict: |a: int, b: int| true }
}

pub open spec fn example_id() -> Instance { Instance { owner: 0, slot: 0 } }

pub open spec fn example_attrs() -> Attributes {
    Attributes { payload: Payload::Command { value: 10 }, deps: Set::empty() }
}

pub proof fn lemma_extend_trace(states: Seq<State>, after: State, c: Constants, a: Action)
    requires behavior(states, c), step(states.last(), after, c, a)
    ensures behavior(states.push(after), c)
{
    reveal(behavior);
    reveal(next);
    assert(next(states.last(), after, c));
    assert forall |i: int| 0 <= i < states.push(after).len() - 1
        implies #[trigger] next(states.push(after)[i], states.push(after)[i + 1], c) by {
        if i < states.len() - 1 {
            assert(next(states[i], states[i + 1], c));
        }
    }
}

pub proof fn lemma_broadcast_contains(c: Constants, p: Packet, dst: int)
    requires member(c, dst)
    ensures broadcast(c, p).contains(Packet { dst, ..p })
{
    broadcast use group_set_lib_default;
    let f = |node: int| Packet { dst: node, ..p };
    assert(members(c).contains(dst));
    assert(f(dst) == (Packet { dst, ..p }));
    members(c).lemma_map_contains(f, Packet { dst, ..p });
}

pub proof fn lemma_example_fast_commit() -> (trace: Seq<State>)
    ensures behavior(trace, example_constants()), trace.len() == 5,
        trace.last().nodes.len() == 3,
        record(trace.last().nodes[0], example_id()).phase is Committed,
        record(trace.last().nodes[0], example_id()).attrs == example_attrs(),
        record(trace.last().nodes[0], example_id()).promise == 0,
        record(trace.last().nodes[0], example_id()).accepted_ballot == 0,
        trace.last().nodes[0].executed == Seq::<Instance>::empty(),
        record(trace.last().nodes[1], example_id()).promise == 0,
        record(trace.last().nodes[1], example_id()).accepted_ballot == 0,
{
    broadcast use group_set_lib_default;
    let c = example_constants();
    let id = example_id();
    let attrs = example_attrs();
    let s0 = State { nodes: Seq::new(3, |i: int| empty_node()), network: Set::empty(), submitted: Map::empty() };
    assert(init(s0, c));
    let r = Record { phase: Phase::PreAccepted, attrs, original: attrs.payload,
        initial_deps: attrs.deps, ..empty_record() };
    let request = packet(Kind::PreAccept, 0, 0, id, 0, attrs);
    let ack0 = packet(Kind::PreAcceptOk, 0, 0, id, 0, attrs);
    let n0 = Node { log: Map::empty().insert(id, r), next_slot: 1,
        attempts: Map::empty().insert(id, attempt(0, Stage::Initial, attrs)), ..empty_node() };
    let s1 = State { submitted: s0.submitted.insert(id, attrs),
        ..replace_node(s0, 0, n0, broadcast(c, request).insert(ack0)) };
    assert(known_conflicts(c, empty_node(), id, attrs.payload) =~= Set::empty());
    assert(attrs.deps.union(known_conflicts(c, empty_node(), id, attrs.payload)) =~= attrs.deps);
    assert(submit(s0, s1, c, 0, 10));
    let ack1 = packet(Kind::PreAcceptOk, 1, 0, id, 0, attrs);
    let ack2 = packet(Kind::PreAcceptOk, 2, 0, id, 0, attrs);
    let p1 = Packet { dst: 1, ..request };
    let p2 = Packet { dst: 2, ..request };
    lemma_broadcast_contains(c, request, 1);
    lemma_broadcast_contains(c, request, 2);
    let s2 = replace_node(s1, 1, Node { log: Map::empty().insert(id, r), ..empty_node() }, set![ack1]);
    let s3 = replace_node(s2, 2, Node { log: Map::empty().insert(id, r), ..empty_node() }, set![ack2]);
    assert(preaccept(s1, s2, c, p1));
    assert(preaccept(s2, s3, c, p2));
    let batch = map![0int => ack0, 1int => ack1, 2int => ack2];
    assert(batch.dom() =~= set![0int, 1int, 2int]);
    assert(batch.dom() =~= members(c));
    assert(batch.dom().len() == 3);
    assert(union_reply_deps(batch) =~= Set::<Instance>::empty());
    let s4 = publish(s3, c, 0, id, 0, attrs, true);
    assert(finish_preaccept(s3, s4, c, 0, id, batch));
    reveal(step);
    reveal(behavior);
    let t0 = seq![s0];
    assert(behavior(t0, c));
    lemma_extend_trace(t0, s1, c, Action::Submit { node: 0, value: 10 });
    lemma_extend_trace(t0.push(s1), s2, c, Action::PreAccept { packet: p1 });
    lemma_extend_trace(t0.push(s1).push(s2), s3, c, Action::PreAccept { packet: p2 });
    lemma_extend_trace(t0.push(s1).push(s2).push(s3), s4, c,
        Action::FinishPreAccept { node: 0, id, batch });
    t0.push(s1).push(s2).push(s3).push(s4)
}

pub proof fn lemma_example_execute(trace: Seq<State>) -> (after: Seq<State>)
    requires behavior(trace, example_constants()), trace.len() > 0,
        trace.last().nodes.len() == 3,
        record(trace.last().nodes[0], example_id()).phase is Committed,
        record(trace.last().nodes[0], example_id()).attrs == example_attrs(),
        trace.last().nodes[0].executed == Seq::<Instance>::empty(),
    ensures behavior(after, example_constants()), after.len() == trace.len() + 1,
        after.last().nodes.len() == 3,
        after.last().nodes[0].executed == seq![example_id()],
        after.last().nodes[0].log == trace.last().nodes[0].log,
        after.last().nodes[1] == trace.last().nodes[1],
{
    let c = example_constants();
    let id = example_id();
    let s = trace.last();
    let n = s.nodes[0];
    let component = seq![id];
    let walk = seq![id];
    assert(path(n, component.to_set(), walk, id, id));
    assert(connected(n, component.to_set(), id, id));
    assert(ready_component(n, component));
    let s_ = replace_node(s, 0, Node { executed: n.executed + component, ..n }, Set::empty());
    assert(s_.nodes[0].executed =~= component);
    reveal(step);
    lemma_extend_trace(trace, s_, c, Action::Execute { node: 0, component });
    trace.push(s_)
}

/// A ten-state execution recovers the same command after the coordinator reboots.
pub proof fn theorem_example_reboot_recovery() -> (trace: Seq<State>)
    ensures behavior(trace, example_constants()), trace.len() == 10,
        trace[6].nodes[0].attempts == Map::<Instance, Attempt>::empty(),
        record(trace.last().nodes[0], example_id()).phase is Committed,
        record(trace.last().nodes[0], example_id()).attrs == example_attrs(),
        record(trace.last().nodes[0], example_id()).accepted_ballot == 3,
        trace.last().nodes[0].executed == seq![example_id()],
{
    broadcast use group_set_lib_default;
    let c = example_constants();
    let id = example_id();
    let t = lemma_example_fast_commit();
    let t = lemma_example_execute(t);
    let s = t.last();
    let rebooted = replace_node(s, 0, Node { attempts: Map::empty(), ..s.nodes[0] }, Set::empty());
    reveal(step);
    lemma_extend_trace(t, rebooted, c, Action::Reboot { node: 0 });
    let t = t.push(rebooted);
    let n = rebooted.nodes[0];
    let r = Record { promise: 3, ..record(n, id) };
    let request = packet(Kind::Recover, 0, 0, id, 3, empty_attrs());
    let reply0 = recovery_reply(0, 0, id, 3, r);
    let started = replace_node(rebooted, 0, Node { log: n.log.insert(id, r),
        attempts: n.attempts.insert(id, attempt(3, Stage::Recovering, empty_attrs())), ..n },
        broadcast(c, request).insert(reply0));
    lemma_extend_trace(t, started, c, Action::BeginRecovery { node: 0, id, ballot: 3 });
    let t = t.push(started);
    let p = Packet { dst: 1, ..request };
    lemma_broadcast_contains(c, request, 1);
    let n1 = started.nodes[1];
    let r1 = Record { promise: 3, ..record(n1, id) };
    let reply1 = recovery_reply(1, 0, id, 3, r1);
    let replied = replace_node(started, 1, Node { log: n1.log.insert(id, r1), ..n1 }, set![reply1]);
    lemma_extend_trace(t, replied, c, Action::Recover { packet: p });
    let t = t.push(replied);
    let batch = map![0int => reply0, 1int => reply1];
    assert(batch.dom() =~= set![0int, 1int]);
    assert(batch.dom().len() == 2);
    assert(maximal_committed(batch).contains(0));
    assert(maximal_committed(batch).len() > 0);
    let recovered = publish(replied, c, 0, id, 3, example_attrs(), true);
    lemma_extend_trace(t, recovered, c,
        Action::FinishRecovery { node: 0, id, ballot: 3, batch, selected: 0 });
    t.push(recovered)
}

} // verus!
