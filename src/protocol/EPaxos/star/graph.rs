//! Abstract committed dependency graph and its execution histories.
use super::types::*;
use super::execution::*;
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {

pub open spec fn graph_path(g: Map<Instance, Attributes>, walk: Seq<Instance>,
    from: Instance, to: Instance) -> bool {
    &&& walk.len() > 0
    &&& walk[0] == from
    &&& walk[walk.len() - 1] == to
    &&& forall |i: int| 0 <= i < walk.len() ==> #[trigger] g.dom().contains(walk[i])
    &&& forall |i: int, j: int| 0 <= i < walk.len() - 1 && j == i + 1
        ==> #[trigger] g[walk[i]].deps.contains(walk[j])
}

#[verifier::opaque]
pub open spec fn reachable(g: Map<Instance, Attributes>, from: Instance, to: Instance) -> bool {
    exists |walk: Seq<Instance>| graph_path(g, walk, from, to)
}

pub open spec fn graph_extends(g: Map<Instance, Attributes>, g_: Map<Instance, Attributes>) -> bool {
    g.dom().subset_of(g_.dom()) && forall |id: Instance| #[trigger] g.dom().contains(id) ==> g_[id] == g[id]
}

pub open spec fn closed(g: Map<Instance, Attributes>, ids: Set<Instance>) -> bool {
    ids.subset_of(g.dom()) && forall |id: Instance| #[trigger] ids.contains(id) ==> g[id].deps.subset_of(ids)
}

pub open spec fn graph_node(g: Map<Instance, Attributes>, history: Seq<Instance>) -> Node {
    Node { log: Map::new(g.dom(), |id: Instance| Record { phase: Phase::Committed, attrs: g[id], ..empty_record() }),
        executed: history, ..empty_node() }
}

#[verifier::opaque]
pub open spec fn history_safe(g: Map<Instance, Attributes>, history: Seq<Instance>) -> bool {
    &&& history.no_duplicates()
    &&& closed(g, history.to_set())
    &&& forall |i: int, j: int| 0 <= i < j < history.len()
        && #[trigger] reachable(g, history[i], history[j])
        ==> reachable(g, history[j], history[i]) && id_less(history[i], history[j])
}

pub proof fn lemma_path_closed(g: Map<Instance, Attributes>, ids: Set<Instance>,
    walk: Seq<Instance>, from: Instance, to: Instance, i: int)
    requires closed(g, ids), ids.contains(from), graph_path(g, walk, from, to), 0 <= i < walk.len()
    ensures ids.contains(walk[i])
    decreases i
{
    if i > 0 {
        lemma_path_closed(g, ids, walk, from, to, i - 1);
        assert(g[walk[i - 1]].deps.contains(walk[i]));
    }
}

pub proof fn lemma_reach_closed(g: Map<Instance, Attributes>, ids: Set<Instance>, from: Instance, to: Instance)
    requires closed(g, ids), ids.contains(from), reachable(g, from, to)
    ensures ids.contains(to)
{
    reveal(reachable);
    let walk = choose |walk: Seq<Instance>| graph_path(g, walk, from, to);
    lemma_path_closed(g, ids, walk, from, to, walk.len() - 1);
}

pub proof fn lemma_reach_extends(g: Map<Instance, Attributes>, g_: Map<Instance, Attributes>, from: Instance, to: Instance)
    requires graph_extends(g, g_), reachable(g, from, to)
    ensures reachable(g_, from, to)
{
    reveal(reachable);
    let walk = choose |walk: Seq<Instance>| graph_path(g, walk, from, to);
    assert forall |i: int| 0 <= i < walk.len() implies
        #[trigger] g_.dom().contains(walk[i]) && g_[walk[i]] == g[walk[i]] by {
        assert(g.dom().contains(walk[i]));
    }
    assert forall |i: int, j: int| 0 <= i < walk.len() - 1 && j == i + 1
        implies #[trigger] g_[walk[i]].deps.contains(walk[j]) by {
        assert(g.dom().contains(walk[i]));
        assert(g_[walk[i]] == g[walk[i]]);
        assert(g[walk[i]].deps.contains(walk[j]));
    }
    assert(graph_path(g_, walk, from, to));
}

pub proof fn lemma_reach_restricts(g: Map<Instance, Attributes>, g_: Map<Instance, Attributes>,
    ids: Set<Instance>, from: Instance, to: Instance)
    requires graph_extends(g, g_), closed(g, ids), ids.contains(from), reachable(g_, from, to)
    ensures reachable(g, from, to)
{
    reveal(reachable);
    assert(closed(g_, ids));
    let walk = choose |walk: Seq<Instance>| graph_path(g_, walk, from, to);
    assert forall |i: int| 0 <= i < walk.len() implies #[trigger] ids.contains(walk[i]) by {
        lemma_path_closed(g_, ids, walk, from, to, i);
    }
    assert forall |i: int, j: int| 0 <= i < walk.len() - 1 && j == i + 1
        implies #[trigger] g[walk[i]].deps.contains(walk[j]) by {
        assert(g_[walk[i]].deps.contains(walk[j]));
        assert(ids.contains(walk[i]));
    }
    assert(graph_path(g, walk, from, to));
}

pub proof fn lemma_history_extends_graph(g: Map<Instance, Attributes>, g_: Map<Instance, Attributes>, history: Seq<Instance>)
    requires graph_extends(g, g_), history_safe(g, history)
    ensures history_safe(g_, history)
{
    reveal(history_safe);
    assert forall |i: int, j: int| 0 <= i < j < history.len()
        && #[trigger] reachable(g_, history[i], history[j])
        implies reachable(g_, history[j], history[i]) && id_less(history[i], history[j]) by {
        lemma_reach_restricts(g, g_, history.to_set(), history[i], history[j]);
        assert(reachable(g, history[j], history[i]));
        lemma_reach_extends(g, g_, history[j], history[i]);
    }
}

pub proof fn lemma_component_reachable(g: Map<Instance, Attributes>, history: Seq<Instance>,
    component: Seq<Instance>, from: Instance, to: Instance)
    requires ready_component(graph_node(g, history), component), component.contains(from), component.contains(to)
    ensures reachable(g, from, to)
{
    let n = graph_node(g, history);
    assert(connected(n, component.to_set(), from, to));
    let walk = choose |walk: Seq<Instance>| path(n, component.to_set(), walk, from, to);
    assert forall |i: int| 0 <= i < walk.len() implies #[trigger] g.dom().contains(walk[i]) by {
        assert(component.to_set().contains(walk[i]));
        component.to_set_ensures();
        assert(component.contains(walk[i]));
        let j = choose |j: int| 0 <= j < component.len() && component[j] == walk[i];
        assert(n.log.dom().contains(component[j]));
    }
    assert forall |i: int, j: int| 0 <= i < walk.len() - 1 && j == i + 1
        implies #[trigger] g[walk[i]].deps.contains(walk[j]) by {
        assert(record(n, walk[i]).attrs.deps.contains(walk[j]));
    }
    assert(graph_path(g, walk, from, to));
    reveal(reachable);
}

pub proof fn lemma_execute_history_safe(g: Map<Instance, Attributes>, history: Seq<Instance>, component: Seq<Instance>)
    requires history_safe(g, history), ready_component(graph_node(g, history), component)
    ensures history_safe(g, history + component)
{
    reveal(history_safe);
    let after = history + component;
    seq_to_set_distributes_over_add(history, component);
    assert(after.to_set() =~= history.to_set().union(component.to_set()));
    assert(closed(g, after.to_set()));
    assert forall |i: int, j: int| 0 <= i < j < after.len() implies after[i] != after[j] by {
        if j < history.len() {
            assert(history[i] != history[j]);
        } else if i >= history.len() {
            assert(component[i - history.len()] != component[j - history.len()]);
        } else {
            assert(!history.contains(component[j - history.len()]));
        }
    }
    assert forall |i: int, j: int| 0 <= i < j < after.len()
        && #[trigger] reachable(g, after[i], after[j])
        implies reachable(g, after[j], after[i]) && id_less(after[i], after[j]) by {
        if j < history.len() {
            assert(reachable(g, history[j], history[i]));
        } else if i < history.len() {
            lemma_reach_closed(g, history.to_set(), after[i], after[j]);
            assert(!history.contains(after[j]));
        } else {
            lemma_component_reachable(g, history, component, after[j], after[i]);
        }
    }
}

} // verus!
