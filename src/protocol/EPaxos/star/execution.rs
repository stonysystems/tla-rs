//! Atomic execution of one ready strongly connected component.
use super::types::*;
use super::model::*;
use vstd::prelude::*;

verus! {

pub open spec fn path(n: Node, component: Set<Instance>, walk: Seq<Instance>,
    from: Instance, to: Instance) -> bool {
    &&& walk.len() > 0
    &&& walk[0] == from
    &&& walk[walk.len() - 1] == to
    &&& forall |i: int| 0 <= i < walk.len() ==> #[trigger] component.contains(walk[i])
    &&& forall |i: int, j: int| 0 <= i < walk.len() - 1 && j == i + 1
        ==> #[trigger] record(n, walk[i]).attrs.deps.contains(walk[j])
}

pub open spec fn connected(n: Node, component: Set<Instance>, a: Instance, b: Instance) -> bool {
    exists |walk: Seq<Instance>| path(n, component, walk, a, b)
}

pub open spec fn ready_component(n: Node, batch: Seq<Instance>) -> bool {
    &&& batch.len() > 0
    &&& batch.no_duplicates()
    &&& forall |i: int, j: int| 0 <= i < j < batch.len() ==> id_less(batch[i], batch[j])
    &&& forall |i: int| 0 <= i < batch.len() ==> {
        let id = #[trigger] batch[i];
        &&& n.log.dom().contains(id)
        &&& record(n, id).phase is Committed
        &&& !n.executed.contains(id)
        &&& record(n, id).attrs.deps.subset_of(n.executed.to_set().union(batch.to_set()))
    }
    &&& forall |a: Instance, b: Instance| #![trigger batch.contains(a), batch.contains(b)]
        batch.contains(a) && batch.contains(b)
        ==> connected(n, batch.to_set(), a, b)
}

pub open spec fn execute(s: State, s_: State, c: Constants,
    node: int, batch: Seq<Instance>) -> bool {
    let n = s.nodes[node];
    &&& s.nodes.len() == c.n
    &&& member(c, node)
    &&& ready_component(n, batch)
    &&& s_ == replace_node(s, node, Node { executed: n.executed + batch, ..n }, Set::empty())
}

} // verus!
