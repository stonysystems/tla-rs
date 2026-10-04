//! Om Figures 4-5: witness accesses and randomized consensus safety.
//! A history records issued accesses, per-witness processing times and returned
//! quorums. Random choices are nondeterministic. Quorum intersection is an
//! explicit condition: the paper does not promise unconditional agreement.
use vstd::prelude::*;

verus! {
pub type Key = (int, int, int); // array (0 proposal, 1 check), round, process
pub struct Config { pub processes: Set<int>, pub witnesses: Set<int>, pub quorums: Set<Set<int>> }
pub struct History {
    pub inputs: Map<int, int>,
    pub values: Map<Key, int>,
    pub starts: Map<Key, int>,
    pub processed: Map<(int, Key), int>,
    pub quorums: Map<Key, Set<int>>,
    pub finishes: Map<Key, int>,
}
pub open spec fn config_ok(c: Config) -> bool {
    &&& c.processes != Set::<int>::empty()
    &&& forall|q: Set<int>| #![trigger q.subset_of(c.witnesses)] c.quorums.contains(q) ==> q.subset_of(c.witnesses) && q != Set::<int>::empty()
    &&& forall|q: Set<int>, r: Set<int>| c.quorums.contains(q) && c.quorums.contains(r)
        ==> exists|w: int| q.contains(w) && r.contains(w)
}
pub open spec fn done(h: History, k: Key) -> bool { h.quorums.dom().contains(k) }
pub open spec fn issued(h: History, k: Key) -> bool { h.values.dom().contains(k) }
pub open spec fn sees(h: History, k: Key, p: int) -> bool {
    done(h, k) && exists|w: int| #![trigger h.quorums[k].contains(w)] h.quorums[k].contains(w)
        && h.processed.dom().contains((w, (k.0, k.1, p)))
        && h.processed[(w, (k.0, k.1, p))] <= h.processed[(w, k)]
}
pub open spec fn uniform(h: History, r: int, p: int) -> bool {
    forall|q: int| #![trigger sees(h, (0, r, p), q)] sees(h, (0, r, p), q) ==> h.values[(0, r, q)] == h.values[(0, r, p)]
}
pub open spec fn agrees(h: History, r: int, p: int) -> bool {
    issued(h, (1, r, p)) && h.values[(1, r, p)] == 1
}
pub open spec fn saw_agree(h: History, r: int, p: int) -> bool {
    exists|q: int| #![trigger agrees(h, r, q)] sees(h, (1, r, p), q) && agrees(h, r, q)
}
pub open spec fn saw_disagree(h: History, r: int, p: int) -> bool {
    exists|q: int| #![trigger sees(h, (1, r, p), q)] sees(h, (1, r, p), q) && h.values[(1, r, q)] == 0
}
pub open spec fn decision(h: History, r: int, p: int, v: int) -> bool {
    done(h, (1, r, p)) && !saw_disagree(h, r, p) && h.values[(0, r, p)] == v
}
pub open spec fn defined_execution(h: History, c: Config) -> bool {
    &&& h.inputs.dom() == c.processes && h.starts.dom() == h.values.dom()
    &&& h.finishes.dom() == h.quorums.dom()
    &&& forall|k: Key| #![trigger issued(h, k)] issued(h, k) ==> 0 <= k.0 <= 1 && k.1 >= 0 && c.processes.contains(k.2)
    &&& forall|w: int, k: Key| #![trigger h.processed.dom().contains((w, k))] h.processed.dom().contains((w, k)) ==>
        c.witnesses.contains(w) && issued(h, k) && h.starts[k] < h.processed[(w, k)]
    &&& forall|k: Key| #![trigger done(h, k)] #![trigger issued(h, k)] done(h, k) ==> issued(h, k) && c.quorums.contains(h.quorums[k])
        && forall|w: int| #![trigger h.quorums[k].contains(w)] h.quorums[k].contains(w) ==> h.processed.dom().contains((w, k))
            && h.processed[(w, k)] < h.finishes[k]
    // Check access follows the completed proposal access and publishes its test.
    &&& forall|r: int, p: int| #[trigger] issued(h, (1, r, p)) ==> done(h, (0, r, p))
        && h.finishes[(0, r, p)] < h.starts[(1, r, p)]
        && h.values[(1, r, p)] == (if uniform(h, r, p) { 1int } else { 0int })
    &&& forall|p: int| #[trigger] issued(h, (0, 0, p)) ==> h.values[(0, 0, p)] == h.inputs[p]
    // Figure 5: only a nondeciding process enters another iteration.
    // This models executions where the mixed-branch prop_view[q] lookup is
    // defined. Witness intersection alone does NOT establish that condition;
    // lookup.rs constructs a missing lookup using intersecting quorums.
    &&& forall|r: int, p: int| #[trigger] issued(h, (0, r, p)) && r > 0 ==>
        done(h, (1, r - 1, p)) && h.finishes[(1, r - 1, p)] < h.starts[(0, r, p)]
        && saw_disagree(h, r - 1, p)
        && if saw_agree(h, r - 1, p) {
            exists|q: int| #[trigger] sees(h, (1, r - 1, p), q) && agrees(h, r - 1, q)
                && sees(h, (0, r - 1, p), q)
                && h.values[(0, r, p)] == h.values[(0, r - 1, q)]
        } else {
            exists|q: int| #[trigger] sees(h, (0, r - 1, p), q)
                && h.values[(0, r, p)] == h.values[(0, r - 1, q)]
        }
}
pub proof fn self_visible(h: History, c: Config, k: Key)
    requires config_ok(c), defined_execution(h, c), done(h, k),
    ensures sees(h, k, k.2),
{
    let q = h.quorums[k];
    assert(q != Set::<int>::empty());
    assert(exists|w: int| q.contains(w)) by {
        if !(exists|w: int| q.contains(w)) { assert(q =~= Set::<int>::empty()); }
    }
    let w = choose|w: int| q.contains(w);
    assert(h.processed.dom().contains((w, k)));
}
pub proof fn observed_was_issued(h: History, c: Config, k: Key, p: int)
    requires defined_execution(h, c), sees(h, k, p),
    ensures issued(h, (k.0, k.1, p)),
{
    let w = choose|w: int| #![trigger h.quorums[k].contains(w)] h.quorums[k].contains(w)
        && h.processed.dom().contains((w, (k.0, k.1, p)))
        && h.processed[(w, (k.0, k.1, p))] <= h.processed[(w, k)];
}
// No atomic-snapshot assumption: two completed accesses see one another in
// at least one direction because their returned witness quorums intersect.
pub proof fn access_visibility(h: History, c: Config, a: int, r: int, p: int, q: int)
    requires config_ok(c), defined_execution(h, c), done(h, (a, r, p)), done(h, (a, r, q)),
    ensures sees(h, (a, r, p), q) || sees(h, (a, r, q), p),
{
    let x = h.quorums[(a, r, p)]; let y = h.quorums[(a, r, q)];
    let w = choose|w: int| x.contains(w) && y.contains(w);
    assert(h.processed.dom().contains((w, (a, r, p))));
    assert(h.processed.dom().contains((w, (a, r, q))));
    if h.processed[(w, (a, r, p))] <= h.processed[(w, (a, r, q))] {
        assert(sees(h, (a, r, q), p));
    } else { assert(sees(h, (a, r, p), q)); }
}
pub proof fn agreeing_proposals_equal(h: History, c: Config, r: int, p: int, q: int)
    requires config_ok(c), defined_execution(h, c), agrees(h, r, p), agrees(h, r, q),
    ensures h.values[(0, r, p)] == h.values[(0, r, q)],
{
    assert(uniform(h, r, p) && uniform(h, r, q));
    access_visibility(h, c, 0, r, p, q);
}
pub proof fn decision_agreed(h: History, c: Config, r: int, p: int, v: int)
    requires config_ok(c), defined_execution(h, c), decision(h, r, p, v),
    ensures agrees(h, r, p), issued(h, (0, r, p)), r >= 0,
{
    self_visible(h, c, (1, r, p));
    assert(issued(h, (1, r, p)));
    assert(h.values[(1, r, p)] == 0 || h.values[(1, r, p)] == 1);
    if !agrees(h, r, p) { assert(saw_disagree(h, r, p)); }
}
pub proof fn decision_forces_next(h: History, c: Config, r: int, p: int, v: int, q: int)
    requires config_ok(c), defined_execution(h, c), decision(h, r, p, v), issued(h, (0, r + 1, q)),
    ensures h.values[(0, r + 1, q)] == v,
{
    decision_agreed(h, c, r, p, v);
    assert(done(h, (1, r, q)) && saw_disagree(h, r, q));
    access_visibility(h, c, 1, r, p, q);
    if !saw_agree(h, r, q) {
        if sees(h, (1, r, q), p) { assert(saw_agree(h, r, q)); }
        assert(sees(h, (1, r, p), q));
        assert(!agrees(h, r, q)) by {
            self_visible(h, c, (1, r, q));
        }
        assert(h.values[(1, r, q)] == 0);
        assert(saw_disagree(h, r, p));
    }
    let a = choose|a: int| #[trigger] sees(h, (1, r, q), a) && agrees(h, r, a)
        && sees(h, (0, r, q), a) && h.values[(0, r + 1, q)] == h.values[(0, r, a)];
    agreeing_proposals_equal(h, c, r, p, a);
}
pub proof fn after_decision(h: History, c: Config, r: int, p: int, v: int, k: int, q: int)
    requires config_ok(c), defined_execution(h, c), decision(h, r, p, v), k > r,
        issued(h, (0, k, q)),
    ensures h.values[(0, k, q)] == v,
    decreases k - r,
{
    decision_agreed(h, c, r, p, v);
    if k == r + 1 { decision_forces_next(h, c, r, p, v, q); }
    else {
        assert(saw_disagree(h, k - 1, q));
        let a = choose|a: int| #[trigger] sees(h, (1, k - 1, q), a) && h.values[(1, k - 1, a)] == 0;
        observed_was_issued(h, c, (1, k - 1, q), a);
        assert(!uniform(h, k - 1, a));
        assert forall|b: int| #[trigger] sees(h, (0, k - 1, a), b)
            implies h.values[(0, k - 1, b)] == h.values[(0, k - 1, a)] by {
            observed_was_issued(h, c, (0, k - 1, a), b);
            after_decision(h, c, r, p, v, k - 1, b);
            after_decision(h, c, r, p, v, k - 1, a);
        }
        assert(false);
    }
}
pub proof fn agreement(h: History, c: Config, r: int, p: int, v: int, k: int, q: int, w: int)
    requires config_ok(c), defined_execution(h, c), decision(h, r, p, v), decision(h, k, q, w),
    ensures v == w,
{
    decision_agreed(h, c, r, p, v); decision_agreed(h, c, k, q, w);
    if r == k { agreeing_proposals_equal(h, c, r, p, q); }
    else if r < k { after_decision(h, c, r, p, v, k, q); }
    else { after_decision(h, c, k, q, w, r, p); }
}
pub proof fn proposal_validity(h: History, c: Config, r: int, p: int)
    requires config_ok(c), defined_execution(h, c), issued(h, (0, r, p)),
    ensures exists|q: int| #![trigger h.inputs[q]] c.processes.contains(q) && h.values[(0, r, p)] == h.inputs[q],
    decreases r,
{
    if r == 0 { assert(c.processes.contains(p)); }
    else {
        assert(r > 0);
        let q = choose|q: int| #[trigger] sees(h, (0, r - 1, p), q) && h.values[(0, r, p)] == h.values[(0, r - 1, q)];
        observed_was_issued(h, c, (0, r - 1, p), q);
        proposal_validity(h, c, r - 1, q);
    }
}
pub proof fn decision_validity(h: History, c: Config, r: int, p: int, v: int)
    requires config_ok(c), defined_execution(h, c), decision(h, r, p, v),
    ensures exists|q: int| #![trigger h.inputs[q]] c.processes.contains(q) && v == h.inputs[q],
{
    decision_agreed(h, c, r, p, v);
    proposal_validity(h, c, r, p);
}
} // verus!
