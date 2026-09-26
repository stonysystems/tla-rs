//! Public safety theorems for the EPaxos* model, including reboot steps.
use super::types::*;
use super::behavior::*;
use super::progress::*;
use super::agreement::*;
use super::visibility::*;
use super::knowledge::*;
use super::refinement::*;
use super::graph::*;
use super::execution_proof::*;
use super::validity::*;
use super::invariants::*;
use vstd::prelude::*;

verus! {

/// A replica has observed a before b if it has executed a and has either not
/// executed b yet, or executed b later. Considering both orientations gives
/// prefix compatibility of the histories projected onto each conflicting pair.
pub open spec fn observed_before(h: Seq<Instance>, a: Instance, b: Instance) -> bool {
    h.contains(a) && (!h.contains(b) || h.index_of(a) < h.index_of(b))
}

pub proof fn lemma_edge_reachable(g: Map<Instance, Attributes>, a: Instance, b: Instance)
    requires g.dom().contains(a), g.dom().contains(b), g[a].deps.contains(b)
    ensures reachable(g, a, b)
{
    reveal(reachable);
    let walk = seq![a, b];
    assert(graph_path(g, walk, a, b));
}

pub proof fn lemma_history_reach_closed(g: Map<Instance, Attributes>, h: Seq<Instance>, a: Instance, b: Instance)
    requires history_safe(g, h), h.contains(a), reachable(g, a, b)
    ensures h.contains(b)
{
    reveal(history_safe);
    h.to_set_ensures();
    lemma_reach_closed(g, h.to_set(), a, b);
}

pub proof fn lemma_history_order(g: Map<Instance, Attributes>, h: Seq<Instance>, a: Instance, b: Instance)
    requires history_safe(g, h), h.contains(a), h.contains(b), h.index_of(a) < h.index_of(b), reachable(g, a, b)
    ensures reachable(g, b, a), id_less(a, b)
{
    reveal(history_safe);
    let i = h.index_of(a);
    let j = h.index_of(b);
    assert(0 <= i < j < h.len());
    assert(h[i] == a && h[j] == b);
    assert(reachable(g, h[i], h[j]));
}

pub proof fn lemma_pair_prefix_compatibility(g: Map<Instance, Attributes>, h: Seq<Instance>, k: Seq<Instance>,
    a: Instance, b: Instance)
    requires history_safe(g, h), history_safe(g, k), a != b,
        g.dom().contains(a), g.dom().contains(b), covers(a, g[a], b, g[b]),
        observed_before(h, a, b), k.contains(b)
    ensures k.contains(a), k.index_of(a) < k.index_of(b)
{
    if g[b].deps.contains(a) {
        lemma_edge_reachable(g, b, a);
    } else {
        lemma_edge_reachable(g, a, b);
        lemma_history_reach_closed(g, h, a, b);
        lemma_history_order(g, h, a, b);
    }
    assert(reachable(g, b, a));
    lemma_history_reach_closed(g, k, b, a);
    assert(k[k.index_of(a)] == a && k[k.index_of(b)] == b);
    if k.index_of(b) < k.index_of(a) {
        lemma_history_order(g, k, b, a);
        lemma_history_reach_closed(g, h, a, b);
        lemma_history_order(g, h, a, b);
        assert(false);
    }
}

#[verifier::opaque]
pub open spec fn execution_safety(s: State, c: Constants) -> bool {
    let g = committed_graph(s);
    forall |node: int, other: int, a: Instance, b: Instance| #![trigger member(c, other), observed_before(s.nodes[node].executed, a, b)]
        member(c, node) && member(c, other) && a != b && g.dom().contains(a) && g.dom().contains(b)
        && !(g[a].payload is Nop) && !(g[b].payload is Nop) && conflicts(c, g[a].payload, g[b].payload)
        && observed_before(s.nodes[node].executed, a, b) && s.nodes[other].executed.contains(b)
        ==> s.nodes[other].executed.contains(a)
            && s.nodes[other].executed.index_of(a) < s.nodes[other].executed.index_of(b)
}

pub proof fn lemma_behavior_execution_safety(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len()
    ensures execution_safety(states[i], c)
{
    lemma_behavior_bounds(states, c, i);
    lemma_behavior_visibility(states, c, i);
    lemma_behavior_history_invariant(states, c, i);
    reveal(visibility);
    reveal(abstract_invariant);
    reveal(execution_safety);
    let s = states[i];
    let g = committed_graph(s);
    assert forall |node: int, other: int, a: Instance, b: Instance| #![trigger member(c, other), observed_before(s.nodes[node].executed, a, b)]
        member(c, node) && member(c, other) && a != b && g.dom().contains(a) && g.dom().contains(b)
        && !(g[a].payload is Nop) && !(g[b].payload is Nop) && conflicts(c, g[a].payload, g[b].payload)
        && observed_before(s.nodes[node].executed, a, b) && s.nodes[other].executed.contains(b)
        implies s.nodes[other].executed.contains(a)
            && s.nodes[other].executed.index_of(a) < s.nodes[other].executed.index_of(b) by {
        let p = lemma_graph_witness(s, a);
        let q = lemma_graph_witness(s, b);
        assert(covers(a, g[a], b, g[b]));
        assert(history_safe(abstract_view(s).graph, abstract_view(s).histories[node]));
        assert(history_safe(abstract_view(s).graph, abstract_view(s).histories[other]));
        lemma_pair_prefix_compatibility(g, s.nodes[node].executed, s.nodes[other].executed, a, b);
    }
}

pub proof fn lemma_network_history_monotonic(states: Seq<State>, c: Constants, earlier: int, later: int)
    requires behavior(states, c), 0 <= earlier <= later < states.len()
    ensures states[earlier].network.subset_of(states[later].network)
    decreases later - earlier
{
    if earlier < later {
        lemma_network_history_monotonic(states, c, earlier, later - 1);
        lemma_behavior_step_progress(states, c, later - 1);
    }
}

pub proof fn lemma_behavior_committed_stability(states: Seq<State>, c: Constants, earlier: int, later: int)
    requires behavior(states, c), 0 <= earlier <= later < states.len()
    ensures graph_extends(committed_graph(states[earlier]), committed_graph(states[later]))
{
    lemma_network_history_monotonic(states, c, earlier, later);
    lemma_behavior_agreement(states, c, later);
    lemma_graph_monotonic(states[earlier], states[later]);
}

/// Safety for every finite prefix. No fairness or bound on messages, instances,
/// ballots, or reboots is assumed. Persistence is defined by model::reboot.
pub proof fn theorem_epaxos_star_safety(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len()
    ensures
        agreement(states[i]), visibility(states[i], c), execution_safety(states[i], c),
        at_most_once(states[i], c), validity(states[i], c), abstract_invariant(abstract_view(states[i])),
{
    lemma_behavior_agreement(states, c, i);
    lemma_behavior_visibility(states, c, i);
    lemma_behavior_execution_safety(states, c, i);
    lemma_behavior_at_most_once(states, c, i);
    lemma_behavior_validity(states, c, i);
    lemma_behavior_history_invariant(states, c, i);
}

} // verus!
