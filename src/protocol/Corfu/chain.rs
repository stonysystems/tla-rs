//! CORFU Section 3.4: one logical position across sealed chain replacements.
//! Per-node writes and crashes are separate actions. A sealed migration copies
//! a surviving value to a fresh chain before publishing the agreed projection.
//! Layout consensus is proved separately with the shared Paxos kernel.
use vstd::prelude::*;
verus! {
pub struct State {
    pub epoch: int,
    pub chain: Seq<int>,
    pub cells: Map<int, Option<int>>,
    pub failed: Set<int>, pub sealed: Set<int>,
    pub origins: Set<int>, // payloads issued by clients, including the junk value
    pub returned: Set<int>,
}
pub open spec fn live(s: State, n: int) -> bool { s.chain.contains(n) && !s.failed.contains(n) }
pub open spec fn inv(s: State) -> bool {
    &&& s.epoch >= 0 && s.chain.len() > 0 && s.chain.no_duplicates()
    &&& s.cells.dom() == s.chain.to_set()
    &&& exists|n: int| live(s, n)
    &&& forall|i: int, j: int| #![trigger s.chain[j], s.chain[i]] 0 <= i <= j < s.chain.len() && s.cells[s.chain[j]] is Some
        ==> s.cells[s.chain[i]] == s.cells[s.chain[j]]
    &&& forall|n: int| #![trigger s.chain.contains(n)] s.chain.contains(n) && s.cells[n] is Some ==> s.origins.contains(s.cells[n]->Some_0)
    &&& forall|v: int, n: int| #![trigger s.returned.contains(v), s.chain.contains(n)] #![trigger s.returned.contains(v), s.cells[n]] s.returned.contains(v) && s.chain.contains(n) ==> s.cells[n] == Some(v)
}
pub open spec fn init(s: State, chain: Seq<int>) -> bool {
    chain.len() > 0 && chain.no_duplicates() && s == State { epoch: 0, chain,
        cells: Map::new(chain.to_set(), |n: int| None), failed: Set::empty(), sealed: Set::empty(),
        origins: Set::empty(), returned: Set::empty() }
}
pub open spec fn write(s: State, t: State, epoch: int, i: int, value: int) -> bool {
    &&& epoch == s.epoch && 0 <= i < s.chain.len()
    &&& live(s, s.chain[i]) && !s.sealed.contains(s.chain[i])
    &&& s.cells[s.chain[i]] is None
    &&& if i == 0 { s.origins.contains(value) } else { s.cells[s.chain[i - 1]] == Some(value) }
    &&& t == State { cells: s.cells.insert(s.chain[i], Some(value)), ..s }
}
pub open spec fn observe(s: State, t: State, epoch: int, value: int) -> bool {
    epoch == s.epoch && live(s, s.chain.last()) && !s.sealed.contains(s.chain.last())
        && s.cells[s.chain.last()] == Some(value)
        && t == State { returned: s.returned.insert(value), ..s }
}
pub open spec fn seal(s: State, t: State, n: int) -> bool {
    live(s, n) && t == State { sealed: s.sealed.insert(n), ..s }
}
pub open spec fn crash(s: State, t: State, n: int) -> bool {
    s.chain.contains(n) && (exists|m: int| live(s, m) && m != n)
        && t == State { failed: s.failed.insert(n), ..s }
}
// Copy the survivor's value, if one exists. If every survivor is unwritten the
// position remains empty. Full-chain copying is an atomic migration abstraction;
// it is stronger than the paper's minimal prefix-copy optimization.
pub open spec fn migrate(s: State, t: State, chain: Seq<int>, value: Option<int>) -> bool {
    &&& forall|n: int| #![trigger live(s, n)] live(s, n) ==> s.sealed.contains(n)
    &&& chain.len() > 0 && chain.no_duplicates()
    &&& match value {
        Some(v) => exists|n: int| #![trigger live(s, n)] live(s, n) && s.cells[n] == Some(v),
        None => forall|n: int| #![trigger live(s, n)] live(s, n) ==> s.cells[n] is None,
    }
    &&& t == State { epoch: s.epoch + 1, chain, cells: Map::new(chain.to_set(), |n: int| value),
        failed: Set::empty(), sealed: Set::empty(), ..s }
}
pub enum Action {
    Issue { value: int }, Write { epoch: int, index: int, value: int }, Observe { epoch: int, value: int },
    Seal { node: int }, Crash { node: int }, Migrate { chain: Seq<int>, seed: Option<int> }, Stutter,
}
pub open spec fn next(s: State, t: State, action: Action) -> bool {
    match action {
        Action::Issue { value } => t == State { origins: s.origins.insert(value), ..s },
        Action::Write { epoch, index, value } => write(s, t, epoch, index, value),
        Action::Observe { epoch, value } => observe(s, t, epoch, value),
        Action::Seal { node } => seal(s, t, node),
        Action::Crash { node } => crash(s, t, node),
        Action::Migrate { chain, seed } => migrate(s, t, chain, seed),
        Action::Stutter => t == s,
    }
}
pub proof fn init_inv(s: State, chain: Seq<int>)
    requires init(s, chain), ensures inv(s),
{
    assert(chain.contains(chain[0]));
    assert(live(s, chain[0]));
}
pub proof fn write_preserves(s: State, t: State, epoch: int, i: int, v: int)
    requires inv(s), write(s, t, epoch, i, v), ensures inv(t),
{
    let survivor = choose|n: int| live(s, n);
    assert(live(t, survivor));
    assert(s.chain.contains(s.chain[i]));
    assert(t.cells.dom() =~= s.cells.dom());
    assert forall|j: int, k: int| #![trigger t.chain[k], t.chain[j]] 0 <= j <= k < t.chain.len() && t.cells[t.chain[k]] is Some
        implies t.cells[t.chain[j]] == t.cells[t.chain[k]] by {
        if k == i {
            if j < i { assert(s.cells[s.chain[j]] == s.cells[s.chain[i - 1]]); }
        } else if j == i {
            assert(s.cells[s.chain[i]] == s.cells[s.chain[k]]); assert(false);
        } else { assert(s.cells[s.chain[j]] == s.cells[s.chain[k]]); }
    }
    assert forall|w: int, n: int| #![trigger t.returned.contains(w), t.chain.contains(n)] #![trigger t.returned.contains(w), t.cells[n]] t.returned.contains(w) && t.chain.contains(n) implies t.cells[n] == Some(w) by {
        assert(s.cells[s.chain[i]] == Some(w)); assert(false);
    }
    assert forall|n: int| #![trigger t.chain.contains(n)] t.chain.contains(n) && t.cells[n] is Some implies t.origins.contains(t.cells[n]->Some_0) by {
        if n == s.chain[i] {
            if i > 0 { assert(s.chain.contains(s.chain[i - 1])); }
        }
    }
}
pub proof fn observe_preserves(s: State, t: State, epoch: int, v: int)
    requires inv(s), observe(s, t, epoch, v), ensures inv(t),
{
    let survivor = choose|n: int| live(s, n);
    assert(live(t, survivor));
    assert(s.chain.last() == s.chain[s.chain.len() as int - 1]);
    assert forall|w: int, n: int| #![trigger t.returned.contains(w), t.chain.contains(n)] #![trigger t.returned.contains(w), t.cells[n]] t.returned.contains(w) && t.chain.contains(n) implies t.cells[n] == Some(w) by {
        if w == v {
            let i = choose|i: int| 0 <= i < s.chain.len() && s.chain[i] == n;
            assert(s.cells[s.chain[i]] == s.cells[s.chain[s.chain.len() as int - 1]]);
        }
    }
}
pub proof fn migrate_preserves(s: State, t: State, chain: Seq<int>, value: Option<int>)
    requires inv(s), migrate(s, t, chain, value), ensures inv(t),
{
    assert(chain.contains(chain[0]));
    assert(live(t, chain[0]));
    if value is Some {
        let n = choose|n: int| #![trigger live(s, n)] live(s, n) && s.cells[n] == value;
        assert(s.origins.contains(value->Some_0));
    }
    assert forall|v: int, n: int| #![trigger t.returned.contains(v), t.chain.contains(n)] #![trigger t.returned.contains(v), t.cells[n]] t.returned.contains(v) && t.chain.contains(n) implies t.cells[n] == Some(v) by {
        let survivor = choose|m: int| live(s, m);
        assert(s.cells[survivor] == Some(v));
        match value {
            Some(w) => {
                let m = choose|m: int| #![trigger live(s, m)] live(s, m) && s.cells[m] == Some(w);
                assert(s.cells[m] == Some(v));
            },
            None => { assert(s.cells[survivor] is None); assert(false); },
        }
    }
}
pub proof fn step_preserves(s: State, t: State, action: Action)
    requires inv(s), next(s, t, action),
    ensures inv(t), s.returned.subset_of(t.returned), s.origins.subset_of(t.origins), t.epoch >= s.epoch,
{
    match action {
        Action::Write { epoch, index, value } => write_preserves(s, t, epoch, index, value),
        Action::Observe { epoch, value } => observe_preserves(s, t, epoch, value),
        Action::Migrate { chain, seed } => migrate_preserves(s, t, chain, seed),
        Action::Crash { node } => {
            let m = choose|m: int| live(s, m) && m != node;
            assert(live(t, m));
        },
        _ => {
            let survivor = choose|n: int| live(s, n);
            assert(live(t, survivor));
        },
    }
}
pub open spec fn behavior(ss: Seq<State>, aa: Seq<Action>, chain: Seq<int>) -> bool {
    ss.len() == aa.len() + 1 && init(ss[0], chain)
        && forall|i: int| 0 <= i < aa.len() ==> #[trigger] next(ss[i], ss[i + 1], aa[i])
}
pub proof fn reachable_inv(ss: Seq<State>, aa: Seq<Action>, chain: Seq<int>, k: int)
    requires behavior(ss, aa, chain), 0 <= k < ss.len(), ensures inv(ss[k]),
    decreases k,
{
    if k == 0 { init_inv(ss[0], chain); }
    else {
        reachable_inv(ss, aa, chain, k - 1);
        assert(next(ss[k - 1], ss[(k - 1) + 1], aa[k - 1]));
        step_preserves(ss[k - 1], ss[k], aa[k - 1]);
    }
}
pub proof fn observations_persist(ss: Seq<State>, aa: Seq<Action>, chain: Seq<int>, i: int, j: int)
    requires behavior(ss, aa, chain), 0 <= i <= j < ss.len(),
    ensures ss[i].returned.subset_of(ss[j].returned),
    decreases j - i,
{
    if i < j {
        observations_persist(ss, aa, chain, i, j - 1);
        reachable_inv(ss, aa, chain, j - 1);
        assert(next(ss[j - 1], ss[(j - 1) + 1], aa[j - 1]));
        step_preserves(ss[j - 1], ss[j], aa[j - 1]);
    }
}
pub proof fn agreement_and_validity(ss: Seq<State>, aa: Seq<Action>, chain: Seq<int>, i: int, j: int, v: int, w: int)
    requires behavior(ss, aa, chain), 0 <= i <= j < ss.len(), ss[i].returned.contains(v), ss[j].returned.contains(w),
    ensures v == w, ss[j].origins.contains(v),
{
    observations_persist(ss, aa, chain, i, j); reachable_inv(ss, aa, chain, j);
    let n = ss[j].chain[0];
    assert(ss[j].chain.contains(n));
    assert(ss[j].cells[n] == Some(v) && ss[j].cells[n] == Some(w));
}
pub proof fn old_epoch_is_fenced(s: State, t: State, e: int, i: int, v: int)
    requires e < s.epoch,
    ensures !write(s, t, e, i, v), !observe(s, t, e, v),
{}
// The tail is the abstract single-assignment cell. Publication may occur on a
// tail write or when migration finishes a previously incomplete write.
pub open spec fn abstract_cell(s: State) -> Option<int> { s.cells[s.chain.last()] }
pub proof fn single_assignment_refinement(s: State, t: State, action: Action)
    requires inv(s), next(s,t,action),
    ensures inv(t),
        abstract_cell(s) is Some ==> abstract_cell(t)==abstract_cell(s),
        abstract_cell(t) is Some ==> t.origins.contains(abstract_cell(t)->Some_0),
{
    step_preserves(s,t,action);
    assert(s.chain.contains(s.chain.last()) && t.chain.contains(t.chain.last()));
    if abstract_cell(s) is Some {
        let v=abstract_cell(s)->Some_0;
        assert forall|n:int| s.chain.contains(n) implies s.cells[n]==Some(v) by {
            let i=choose|i:int| 0 <= i < s.chain.len() && s.chain[i]==n;
            assert(s.cells[s.chain[i]]==s.cells[s.chain[s.chain.len() as int-1]]);
        }
        match action {
            Action::Migrate { chain, seed } => {
                let survivor=choose|n:int| live(s,n);
                assert(s.cells[survivor]==Some(v));
                if seed is None { assert(s.cells[survivor] is None); }
                else {
                    let n=choose|n:int| #![trigger live(s,n)] live(s,n) && s.cells[n]==seed;
                    assert(s.cells[n]==Some(v));
                }
            },
            Action::Write { epoch,index,value } => {
                assert(s.chain.contains(s.chain[index])); assert(s.cells[s.chain[index]]==Some(v));
                assert(false);
            },
            _ => {},
        }
    }
}
pub proof fn successful_read_refines_atomic_cell(s:State,t:State,epoch:int,value:int)
    requires inv(s), observe(s,t,epoch,value),
    ensures abstract_cell(s)==Some(value), abstract_cell(t)==Some(value),
{}
} // verus!
