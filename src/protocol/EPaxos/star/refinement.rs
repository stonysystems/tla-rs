//! Refinement to an abstract committed graph with per-replica histories.
use super::types::*;
use super::model::*;
use super::execution::*;
use super::behavior::*;
use super::invariants::*;
use super::identities::*;
use super::progress::*;
use super::evidence::*;
use super::agreement::*;
use super::graph::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub open spec fn committed_ids(s: State) -> Set<Instance> {
    s.network.filter(|p: Packet| p.kind is Commit).map(|p: Packet| p.instance)
}

pub open spec fn committed_attributes(s: State, id: Instance) -> Attributes {
    (choose |p: Packet| #[trigger] s.network.contains(p) && p.kind is Commit && p.instance == id).attrs
}

pub open spec fn committed_graph(s: State) -> Map<Instance, Attributes> {
    Map::new(committed_ids(s), |id: Instance| committed_attributes(s, id))
}

pub struct AbstractState {
    pub graph: Map<Instance, Attributes>,
    pub histories: Seq<Seq<Instance>>,
}

pub open spec fn abstract_view(s: State) -> AbstractState {
    AbstractState { graph: committed_graph(s), histories: Seq::new(s.nodes.len(), |node: int| s.nodes[node].executed) }
}

pub open spec fn abstract_init(s: AbstractState, c: Constants) -> bool {
    s.graph == Map::<Instance, Attributes>::empty()
        && s.histories == Seq::new(c.n as nat, |node: int| Seq::<Instance>::empty())
}

#[verifier::opaque]
pub open spec fn abstract_execute(s: AbstractState, s_: AbstractState, node: int, component: Seq<Instance>) -> bool {
    &&& 0 <= node < s.histories.len()
    &&& s.graph == s_.graph
    &&& ready_component(graph_node(s.graph, s.histories[node]), component)
    &&& s_.histories == s.histories.update(node, s.histories[node] + component)
}

#[verifier::opaque]
pub open spec fn abstract_next(s: AbstractState, s_: AbstractState) -> bool {
    &&& graph_extends(s.graph, s_.graph)
    &&& s.histories.len() == s_.histories.len()
    &&& s.histories == s_.histories || exists |node: int, component: Seq<Instance>|
        #[trigger] abstract_execute(s, s_, node, component)
}

#[verifier::opaque]
pub open spec fn abstract_invariant(s: AbstractState) -> bool {
    forall |node: int| 0 <= node < s.histories.len()
        ==> #[trigger] history_safe(s.graph, s.histories[node])
}

pub open spec fn abstract_trace(states: Seq<State>) -> Seq<AbstractState> {
    Seq::new(states.len(), |i: int| abstract_view(states[i]))
}

#[verifier::opaque]
pub open spec fn abstract_behavior(states: Seq<AbstractState>, c: Constants) -> bool {
    &&& states.len() > 0
    &&& abstract_init(states[0], c)
    &&& forall |i: int| 0 <= i < states.len() - 1
        ==> #[trigger] abstract_next(states[i], states[i + 1])
}

pub proof fn lemma_graph_witness(s: State, id: Instance) -> (p: Packet)
    requires committed_graph(s).dom().contains(id)
    ensures s.network.contains(p), p.kind is Commit, p.instance == id, p.attrs == committed_graph(s)[id]
{
    broadcast use group_set_lib_default;
    let filtered = s.network.filter(|p: Packet| p.kind is Commit);
    filtered.lemma_map_contains(|p: Packet| p.instance, id);
    choose |p: Packet| #[trigger] s.network.contains(p) && p.kind is Commit && p.instance == id
}

pub proof fn lemma_graph_entry(s: State, p: Packet)
    requires agreement(s), s.network.contains(p), p.kind is Commit
    ensures committed_graph(s).dom().contains(p.instance), committed_graph(s)[p.instance] == p.attrs
{
    broadcast use group_set_lib_default;
    reveal(agreement);
    let filtered = s.network.filter(|p: Packet| p.kind is Commit);
    filtered.lemma_map_contains(|p: Packet| p.instance, p.instance);
    assert(filtered.contains(p));
    assert(committed_graph(s).dom().contains(p.instance));
    let q = lemma_graph_witness(s, p.instance);
    assert(p.attrs == q.attrs);
}

pub proof fn lemma_graph_record(s: State, c: Constants, node: int, id: Instance)
    requires member(c, node), evidence(s, c), agreement(s), record(s.nodes[node], id).phase is Committed
    ensures committed_graph(s).dom().contains(id), committed_graph(s)[id] == record(s.nodes[node], id).attrs
{
    reveal(evidence);
    let r = record(s.nodes[node], id);
    assert(record_evidence(s, id, r));
    let p = choose |p: Packet| #[trigger] s.network.contains(p)
        && p.instance == id && p.ballot == r.accepted_ballot && p.attrs == r.attrs
        && if r.phase is Committed { p.kind is Commit } else { p.kind is Accept };
    lemma_graph_entry(s, p);
}

pub proof fn lemma_graph_monotonic(s: State, s_: State)
    requires agreement(s_), s.network.subset_of(s_.network)
    ensures graph_extends(committed_graph(s), committed_graph(s_))
{
    assert forall |id: Instance| #[trigger] committed_graph(s).dom().contains(id) implies {
        committed_graph(s_).dom().contains(id) && committed_graph(s_)[id] == committed_graph(s)[id]
    } by {
        let p = lemma_graph_witness(s, id);
        lemma_graph_entry(s_, p);
    }
}

pub proof fn lemma_ready_component_transfer(n: Node, m: Node, component: Seq<Instance>)
    requires ready_component(n, component), n.executed == m.executed,
        forall |id: Instance| #[trigger] component.contains(id) ==> {
            m.log.dom().contains(id) && record(m, id).phase is Committed && record(m, id).attrs == record(n, id).attrs
        }
    ensures ready_component(m, component)
{
    assert forall |i: int| 0 <= i < component.len() implies {
        let id = #[trigger] component[i];
        &&& m.log.dom().contains(id)
        &&& record(m, id).phase is Committed
        &&& !m.executed.contains(id)
        &&& record(m, id).attrs.deps.subset_of(m.executed.to_set().union(component.to_set()))
    } by {
        assert(component.contains(component[i]));
    }
    assert forall |a: Instance, b: Instance| #![trigger component.contains(a), component.contains(b)]
        component.contains(a) && component.contains(b)
        implies connected(m, component.to_set(), a, b) by {
        assert(connected(n, component.to_set(), a, b));
        let walk = choose |walk: Seq<Instance>| path(n, component.to_set(), walk, a, b);
        assert forall |i: int, j: int| 0 <= i < walk.len() - 1 && j == i + 1
            implies #[trigger] record(m, walk[i]).attrs.deps.contains(walk[j]) by {
            assert(component.to_set().contains(walk[i]));
            component.to_set_ensures();
            assert(component.contains(walk[i]));
            assert(record(n, walk[i]).attrs.deps.contains(walk[j]));
        }
        assert(path(m, component.to_set(), walk, a, b));
    }
}

pub proof fn lemma_execute_global_component(s: State, s_: State, c: Constants, node: int, component: Seq<Instance>)
    requires evidence(s, c), agreement(s), execute(s, s_, c, node, component)
    ensures ready_component(graph_node(committed_graph(s), s.nodes[node].executed), component)
{
    let n = s.nodes[node];
    let m = graph_node(committed_graph(s), n.executed);
    assert forall |id: Instance| #[trigger] component.contains(id) implies {
        m.log.dom().contains(id) && record(m, id).phase is Committed && record(m, id).attrs == record(n, id).attrs
    } by {
        lemma_graph_record(s, c, node, id);
    }
    lemma_ready_component_transfer(n, m, component);
}

pub proof fn lemma_initial_refinement(s: State, c: Constants)
    requires init(s, c)
    ensures abstract_init(abstract_view(s), c), abstract_invariant(abstract_view(s))
{
    broadcast use group_set_lib_default;
    assert(committed_ids(s) =~= Set::<Instance>::empty());
    assert(committed_graph(s) =~= Map::<Instance, Attributes>::empty());
    assert(abstract_view(s).histories =~= Seq::new(c.n as nat, |node: int| Seq::<Instance>::empty()));
    reveal(abstract_invariant);
    reveal(history_safe);
}

pub proof fn lemma_step_refinement(s: State, s_: State, c: Constants, a: Action)
    requires valid_constants(c), bounds(s, c), references_known(s, c), allocated(s, c),
        evidence(s, c), agreement(s), agreement(s_), step(s, s_, c, a)
    ensures abstract_next(abstract_view(s), abstract_view(s_))
{
    lemma_step_progress(s, s_, c, a);
    lemma_graph_monotonic(s, s_);
    reveal(step);
    reveal(abstract_next);
    if let Action::Execute { node, component } = a {
        lemma_execute_global_component(s, s_, c, node, component);
        assert(s.network.union(Set::empty()) =~= s.network);
        assert(committed_ids(s) == committed_ids(s_));
        assert(abstract_view(s).graph =~= abstract_view(s_).graph);
        assert(abstract_view(s_).histories =~= abstract_view(s).histories.update(node, s.nodes[node].executed + component));
        assert(abstract_execute(abstract_view(s), abstract_view(s_), node, component)) by { reveal(abstract_execute); }
    } else {
        assert(abstract_view(s_).histories =~= abstract_view(s).histories);
    }
}

pub proof fn lemma_abstract_step_invariant(s: AbstractState, s_: AbstractState)
    requires abstract_invariant(s), abstract_next(s, s_)
    ensures abstract_invariant(s_)
{
    reveal(abstract_next);
    reveal(abstract_invariant);
    if s.histories == s_.histories {
        assert forall |node: int| 0 <= node < s_.histories.len()
            implies #[trigger] history_safe(s_.graph, s_.histories[node]) by {
            lemma_history_extends_graph(s.graph, s_.graph, s.histories[node]);
        }
    } else {
        let (node, component) = choose |node: int, component: Seq<Instance>| #[trigger] abstract_execute(s, s_, node, component);
        reveal(abstract_execute);
        lemma_execute_history_safe(s.graph, s.histories[node], component);
    }
}

pub proof fn lemma_behavior_history_invariant(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len()
    ensures abstract_invariant(abstract_view(states[i]))
    decreases i
{
    reveal(behavior);
    if i == 0 {
        lemma_initial_refinement(states[0], c);
    } else {
        lemma_behavior_history_invariant(states, c, i - 1);
        lemma_behavior_bounds(states, c, i - 1);
        lemma_behavior_references(states, c, i - 1);
        lemma_behavior_evidence(states, c, i - 1);
        lemma_behavior_agreement(states, c, i - 1);
        lemma_behavior_agreement(states, c, i);
        lemma_behavior_step(states, c, i - 1);
        reveal(next);
        let a = choose |a: Action| #[trigger] step(states[i - 1], states[i], c, a);
        lemma_step_refinement(states[i - 1], states[i], c, a);
        lemma_abstract_step_invariant(abstract_view(states[i - 1]), abstract_view(states[i]));
    }
}

pub proof fn lemma_behavior_step_refines(states: Seq<State>, c: Constants, i: int)
    requires behavior(states, c), 0 <= i < states.len() - 1
    ensures abstract_next(abstract_view(states[i]), abstract_view(states[i + 1]))
{
    lemma_behavior_bounds(states, c, i);
    lemma_behavior_references(states, c, i);
    lemma_behavior_evidence(states, c, i);
    lemma_behavior_agreement(states, c, i);
    lemma_behavior_agreement(states, c, i + 1);
    lemma_behavior_step(states, c, i);
    reveal(behavior);
    reveal(next);
    let a = choose |a: Action| #[trigger] step(states[i], states[i + 1], c, a);
    lemma_step_refinement(states[i], states[i + 1], c, a);
}

/// The complete finite protocol trace maps to an abstract graph/history trace.
pub proof fn theorem_epaxos_star_refinement(states: Seq<State>, c: Constants)
    requires behavior(states, c)
    ensures abstract_behavior(abstract_trace(states), c)
{
    reveal(behavior);
    reveal(abstract_behavior);
    lemma_initial_refinement(states[0], c);
    assert forall |i: int| 0 <= i < abstract_trace(states).len() - 1
        implies #[trigger] abstract_next(abstract_trace(states)[i], abstract_trace(states)[i + 1]) by {
        lemma_behavior_step_refines(states, c, i);
    }
}

} // verus!
