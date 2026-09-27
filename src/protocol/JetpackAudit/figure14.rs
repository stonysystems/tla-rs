//! Jetpack, OSDI 2026, Figure 14 read literally. Two recovery rules differ from
//! the verified model in ../Jetpack/recovery.rs, which strengthens both:
//! 1. Prepare (lines 6-10) goes to every replica once f+1 BeginRecoveryOK
//!    replies arrive, and its handler neither checks nor sets recovery mode.
//! 2. FinishRecovery (lines 26-27) returns a replica to normal mode with no
//!    staleness check, so a delayed copy can undo a later freeze of that view.
//! All other steps are the verified model's own `recovery::next`. Each theorem
//! builds an execution in which a fast-committed command is missing from the
//! chosen recovery set, contradicting the paper's Lemma 2.
use vstd::prelude::*;
use super::recovery::*;

verus! {

/// Figure 14 lines 6-10: after f+1 replicas froze, any replica may reply.
pub open spec fn prepare_literal(s: State, t: State, c: Config, a: int, b: int) -> bool {
    &&& c.nodes.contains(a) && b >= 0 && b > s.promise[a]
    &&& exists|q: Set<int>| #[trigger] quorum(c, q) && q.subset_of(s.frozen)
    &&& t == State {
        promise: s.promise.insert(a, b),
        replies: s.replies.insert((a, b), Snapshot { last: s.last[a], value: s.value[a], log: s.logs[a] }),
        ..s
    }
}

/// Figure 14 lines 26-27: delivery of a delayed FinishRecovery for the view
/// under recovery, sent by the recovery that opened it (line 25).
pub open spec fn resume(s: State, t: State, c: Config, a: int) -> bool {
    &&& c.nodes.contains(a) && s.frozen.contains(a)
    &&& t == State { frozen: s.frozen.remove(a), ..s }
}

pub enum Step {
    Model { action: Action },
    PrepareLiteral { node: int, ballot: int },
    Resume { node: int },
}

pub open spec fn literal_step(s: State, t: State, c: Config, x: Step) -> bool {
    match x {
        Step::Model { action } => next(s, t, c, action),
        Step::PrepareLiteral { node, ballot } => prepare_literal(s, t, c, node, ballot),
        Step::Resume { node } => resume(s, t, c, node),
    }
}

pub open spec fn literal_behavior(states: Seq<State>, steps: Seq<Step>, c: Config) -> bool {
    &&& states.len() == steps.len() + 1 && init(states[0], c)
    &&& forall|k: int| 0 <= k < steps.len()
        ==> #[trigger] literal_step(states[k], states[k + 1], c, steps[k])
}

pub open spec fn cfg() -> Config {
    Config { nodes: set![0int, 1int, 2int], commands: set![7int],
        conflict: Set::<(int, int)>::empty(), f: 1 }
}
pub open spec fn none() -> Set<int> { Set::<int>::empty() }
pub open spec fn start() -> State {
    State {
        logs: Map::new(cfg().nodes, |a: int| Set::<int>::empty()),
        frozen: Set::<int>::empty(),
        promise: Map::new(cfg().nodes, |a: int| -1int),
        last: Map::new(cfg().nodes, |a: int| -1int),
        value: Map::new(cfg().nodes, |a: int| Set::<int>::empty()),
        replies: Map::<(int, int), Snapshot>::empty(),
        proposals: Map::<int, Set<int>>::empty(),
        votes: Set::<(int, int, Set<int>)>::empty(),
    }
}

// Successor states, written exactly as the corresponding transitions build them.
pub open spec fn ack(s: State, a: int, x: int) -> State {
    State { logs: s.logs.insert(a, s.logs[a].insert(x)), ..s }
}
pub open spec fn frz(s: State, a: int) -> State { State { frozen: s.frozen.insert(a), ..s } }
pub open spec fn thaw(s: State, a: int) -> State { State { frozen: s.frozen.remove(a), ..s } }
pub open spec fn prep(s: State, a: int, b: int) -> State {
    State {
        promise: s.promise.insert(a, b),
        replies: s.replies.insert((a, b), Snapshot { last: s.last[a], value: s.value[a], log: s.logs[a] }),
        ..s
    }
}
pub open spec fn prop(s: State, b: int, v: Set<int>) -> State {
    State { proposals: s.proposals.insert(b, v), ..s }
}
pub open spec fn acc(s: State, a: int, b: int) -> State {
    State {
        promise: s.promise.insert(a, b), last: s.last.insert(a, b),
        value: s.value.insert(a, s.proposals[b]),
        votes: s.votes.insert((a, b, s.proposals[b])), ..s
    }
}

proof fn lemma_sizes()
    ensures cfg().nodes.len() == 3, set![0int, 1int].len() == 2, set![1int, 2int].len() == 2,
        set![1int].len() == 1,
{
    assert(set![0int].len() == 1);
    assert(set![0int, 1int].len() == 2);
    assert(set![1int].len() == 1);
    assert(set![1int, 2int].len() == 2);
}

/// The unfrozen reply is no `recovery::next` step: only Prepare adds a reply,
/// and the verified `prepare` requires the replier to be frozen.
proof fn lemma_step5_not_next()
    ensures forall|a: Action| !#[trigger] next(unmerged_states()[5], unmerged_states()[6], cfg(), a),
{
    let s = unmerged_states()[5];
    let t = unmerged_states()[6];
    assert(!s.frozen.contains(2));
    assert(t.replies.dom().contains((2int, 0int)));
    assert(!s.replies.dom().contains((2int, 0int)));
    assert forall|a: Action| !#[trigger] next(s, t, cfg(), a) by {
        match a {
            Action::Prepare { node, ballot } => {
                if next(s, t, cfg(), a) {
                    assert(t.replies.dom().contains((node, ballot)));
                    assert(s.replies.dom().insert((node, ballot)) == t.replies.dom());
                    assert(node == 2 && ballot == 0);
                }
            }
            _ => {
                if next(s, t, cfg(), a) { assert(t.replies == s.replies); }
            }
        }
    }
}

/// Resuming is no `recovery::next` step: no verified action unfreezes a replica.
proof fn lemma_step9_not_next()
    ensures forall|a: Action| !#[trigger] next(stale_finish_states()[9], stale_finish_states()[10], cfg(), a),
{
    let s = stale_finish_states()[9];
    let t = stale_finish_states()[10];
    assert(s.frozen.contains(2) && !t.frozen.contains(2));
    assert forall|a: Action| !#[trigger] next(s, t, cfg(), a) by {
        match a {
            Action::Freeze { node } => {
                if next(s, t, cfg(), a) {
                    assert(t.frozen.contains(node));
                    assert(s.frozen.insert(node).contains(2));
                }
            }
            _ => {
                if next(s, t, cfg(), a) { assert(t.frozen == s.frozen); }
            }
        }
    }
}

// JETPACK-001. Replicas 0 and 1 acknowledge command 7 and freeze. Replica 2
// never receives BeginRecovery, answers Prepare while still normal, and only
// then acknowledges 7. The recovery set chosen from {1, 2} is empty.
pub open spec fn unmerged_states() -> Seq<State> {
    let s1 = ack(start(), 0, 7);
    let s2 = ack(s1, 1, 7);
    let s3 = frz(s2, 0);
    let s4 = frz(s3, 1);
    let s5 = prep(s4, 1, 0);
    let s6 = prep(s5, 2, 0);
    let s7 = prop(s6, 0, none());
    let s8 = acc(s7, 1, 0);
    let s9 = acc(s8, 2, 0);
    let s10 = ack(s9, 2, 7);
    seq![start(), s1, s2, s3, s4, s5, s6, s7, s8, s9, s10]
}
pub open spec fn unmerged_steps() -> Seq<Step> {
    seq![
        Step::Model { action: Action::Acknowledge { node: 0, command: 7 } },
        Step::Model { action: Action::Acknowledge { node: 1, command: 7 } },
        Step::Model { action: Action::Freeze { node: 0 } },
        Step::Model { action: Action::Freeze { node: 1 } },
        Step::Model { action: Action::Prepare { node: 1, ballot: 0 } },
        Step::PrepareLiteral { node: 2, ballot: 0 },
        Step::Model { action: Action::Propose { ballot: 0, quorum: set![1int, 2int], maximum: -1, value: none() } },
        Step::Model { action: Action::Accept { node: 1, ballot: 0 } },
        Step::Model { action: Action::Accept { node: 2, ballot: 0 } },
        Step::Model { action: Action::Acknowledge { node: 2, command: 7 } },
    ]
}

/// Figure 14's unmerged Prepare leaves a fast-committed command out of the
/// chosen set. Exactly one step, replica 2's reply, is not a `recovery::next` step.
pub proof fn theorem_unmerged_prepare_loses_fast_commit()
    ensures
        config_ok(cfg()),
        literal_behavior(unmerged_states(), unmerged_steps(), cfg()),
        fast_committed(unmerged_states().last(), cfg(), 7),
        chosen(unmerged_states().last(), cfg(), 0, none()),
        !none().contains(7),
        forall|k: int| 0 <= k < unmerged_steps().len() && k != 5
            ==> #[trigger] unmerged_steps()[k] is Model,
        !unmerged_states()[5].frozen.contains(2),
        forall|a: Action| !#[trigger] next(unmerged_states()[5], unmerged_states()[6], cfg(), a),
{
    let c = cfg();
    let t = unmerged_states();
    let x = unmerged_steps();
    lemma_sizes();
    let q = set![1int, 2int];
    assert(quorum(c, set![0int, 1int]) && set![0int, 1int].subset_of(t[5].frozen));
    let logs = reply_logs(t[6], 0, q);
    assert(logs[1] == set![7int] && logs[2] == Set::<int>::empty());
    assert(support(logs, q, 7) =~= set![1int]);
    assert(selected(c, logs, q) =~= none());
    assert forall|k: int| 0 <= k < x.len() implies #[trigger] literal_step(t[k], t[k + 1], c, x[k]) by {
        if k == 0 { assert(acknowledge(t[0], t[1], c, 0, 7)); }
        else if k == 1 { assert(acknowledge(t[1], t[2], c, 1, 7)); }
        else if k == 2 { assert(freeze(t[2], t[3], c, 0)); }
        else if k == 3 { assert(freeze(t[3], t[4], c, 1)); }
        else if k == 4 { assert(prepare(t[4], t[5], c, 1, 0)); }
        else if k == 5 { assert(prepare_literal(t[5], t[6], c, 2, 0)); }
        else if k == 6 { assert(propose(t[6], t[7], c, 0, q, -1, none())); }
        else if k == 7 { assert(accept(t[7], t[8], c, 1, 0)); }
        else if k == 8 { assert(accept(t[8], t[9], c, 2, 0)); }
        else { assert(acknowledge(t[9], t[10], c, 2, 7)); }
    }
    assert(support(t[10].logs, c.nodes, 7) =~= c.nodes);
    assert(fast_committed(t[10], c, 7));
    assert(quorum(c, q));
    assert(forall|a: int| #[trigger] q.contains(a) ==> voted(t[10], a, 0, none()));
    assert(chosen(t[10], c, 0, none()));
    assert(!t[5].frozen.contains(2));
    lemma_step5_not_next();
}

// JETPACK-002. Replicas 1 and 2 freeze and answer Prepare while 7 is known
// only to 0 and 1, so the empty set is chosen. A delayed FinishRecovery then
// resumes replica 2, which acknowledges 7. Every Prepare obeys the frozen rule.
pub open spec fn stale_finish_states() -> Seq<State> {
    let s1 = ack(start(), 0, 7);
    let s2 = ack(s1, 1, 7);
    let s3 = frz(s2, 1);
    let s4 = frz(s3, 2);
    let s5 = prep(s4, 1, 0);
    let s6 = prep(s5, 2, 0);
    let s7 = prop(s6, 0, none());
    let s8 = acc(s7, 1, 0);
    let s9 = acc(s8, 2, 0);
    let s10 = thaw(s9, 2);
    let s11 = ack(s10, 2, 7);
    seq![start(), s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
}
pub open spec fn stale_finish_steps() -> Seq<Step> {
    seq![
        Step::Model { action: Action::Acknowledge { node: 0, command: 7 } },
        Step::Model { action: Action::Acknowledge { node: 1, command: 7 } },
        Step::Model { action: Action::Freeze { node: 1 } },
        Step::Model { action: Action::Freeze { node: 2 } },
        Step::Model { action: Action::Prepare { node: 1, ballot: 0 } },
        Step::Model { action: Action::Prepare { node: 2, ballot: 0 } },
        Step::Model { action: Action::Propose { ballot: 0, quorum: set![1int, 2int], maximum: -1, value: none() } },
        Step::Model { action: Action::Accept { node: 1, ballot: 0 } },
        Step::Model { action: Action::Accept { node: 2, ballot: 0 } },
        Step::Resume { node: 2 },
        Step::Model { action: Action::Acknowledge { node: 2, command: 7 } },
    ]
}

/// An unguarded FinishRecovery leaves a fast-committed command out of the chosen
/// set, although every Prepare reply comes from a frozen replica. Exactly one
/// step, the resume, is not a `recovery::next` step.
pub proof fn theorem_stale_finish_loses_fast_commit()
    ensures
        config_ok(cfg()),
        literal_behavior(stale_finish_states(), stale_finish_steps(), cfg()),
        fast_committed(stale_finish_states().last(), cfg(), 7),
        chosen(stale_finish_states().last(), cfg(), 0, none()),
        !none().contains(7),
        forall|k: int| 0 <= k < stale_finish_steps().len() && k != 9
            ==> #[trigger] stale_finish_steps()[k] is Model,
        forall|a: Action| !#[trigger] next(stale_finish_states()[9], stale_finish_states()[10], cfg(), a),
{
    let c = cfg();
    let t = stale_finish_states();
    let x = stale_finish_steps();
    lemma_sizes();
    let q = set![1int, 2int];
    let logs = reply_logs(t[6], 0, q);
    assert(logs[1] == set![7int] && logs[2] == Set::<int>::empty());
    assert(support(logs, q, 7) =~= set![1int]);
    assert(selected(c, logs, q) =~= none());
    assert forall|k: int| 0 <= k < x.len() implies #[trigger] literal_step(t[k], t[k + 1], c, x[k]) by {
        if k == 0 { assert(acknowledge(t[0], t[1], c, 0, 7)); }
        else if k == 1 { assert(acknowledge(t[1], t[2], c, 1, 7)); }
        else if k == 2 { assert(freeze(t[2], t[3], c, 1)); }
        else if k == 3 { assert(freeze(t[3], t[4], c, 2)); }
        else if k == 4 { assert(prepare(t[4], t[5], c, 1, 0)); }
        else if k == 5 { assert(prepare(t[5], t[6], c, 2, 0)); }
        else if k == 6 { assert(propose(t[6], t[7], c, 0, q, -1, none())); }
        else if k == 7 { assert(accept(t[7], t[8], c, 1, 0)); }
        else if k == 8 { assert(accept(t[8], t[9], c, 2, 0)); }
        else if k == 9 { assert(resume(t[9], t[10], c, 2)); }
        else {
            assert(!t[10].frozen.contains(2));
            assert(acknowledge(t[10], t[11], c, 2, 7));
        }
    }
    assert(support(t[11].logs, c.nodes, 7) =~= c.nodes);
    assert(fast_committed(t[11], c, 7));
    assert(quorum(c, q));
    assert(forall|a: int| #[trigger] q.contains(a) ==> voted(t[11], a, 0, none()));
    assert(chosen(t[11], c, 0, none()));
    lemma_step9_not_next();
}

/// Control: in the verified model, which requires frozen Prepare repliers and
/// never unfreezes, no execution reaches either outcome.
pub proof fn corollary_model_excludes_both(states: Seq<State>, actions: Seq<Action>,
                                           i: int, j: int, b: int)
    requires behavior(states, actions, cfg()), 0 <= i < states.len(), 0 <= j < states.len(),
        fast_committed(states[i], cfg(), 7), chosen(states[j], cfg(), b, none()),
    ensures false,
{
    lemma_sizes();
    execution_safety(states, actions, cfg(), i, j, j, 7, b, none(), b, none());
}

} // verus!
