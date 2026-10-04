//! Jetpack proposer promises composed with an abstract host consensus protocol.
//! Host obligations are explicit operational rules: append proposals in receipt
//! order, execute conflicting proposals in that order, and recover prefixes.
//! Host consensus/commit durability is abstract; no fast-order theorem is a guard.
use vstd::prelude::*;
use super::recovery as r;
use super::application::independent;

verus! {

pub struct State {
    pub calls: Set<int>,
    pub base: Set<int>,
    pub pending: Set<int>,
    pub proposers: Set<int>,
    pub queues: Map<int, Seq<int>>,
    pub acks: Map<int, Set<int>>,
    // 0 normal, 1 recovering, 2 submitting the chosen recovery batch.
    pub phase: int,
    pub cut: Set<int>,
    pub core: r::State,
    pub recovery_ballot: int,
    pub batch: Set<int>,
}
pub open spec fn before(q: Seq<int>, x: int, y: int) -> bool {
    exists|i: int, j: int| 0 <= i < j < q.len() && q[i] == x && q[j] == y
}
pub open spec fn prefix(p: Seq<int>, q: Seq<int>) -> bool {
    p.len() <= q.len() && forall|i: int| 0 <= i < p.len() ==> p[i] == q[i]
}
pub open spec fn certificate(s: State, c: r::Config, x: int) -> bool {
    r::support(s.acks, c.nodes, x).len() >= r::fast_size(c)
        && s.proposers.subset_of(r::support(s.acks, c.nodes, x))
}
pub open spec fn promise_order(s: State, c: r::Config, p: int, x: int) -> bool {
    &&& s.phase == 0 ==> s.queues[p].contains(x)
    &&& forall|y: int| #![trigger s.base.contains(y)] s.queues[p].contains(y) && !s.base.contains(y) && c.conflict.contains((x, y))
        ==> before(s.queues[p], x, y)
}
pub open spec fn inv(s: State, c: r::Config) -> bool {
    &&& s.calls.subset_of(c.commands) && s.base.subset_of(s.calls)
    &&& s.pending.subset_of(s.calls) && s.pending.disjoint(s.base)
    &&& s.proposers.subset_of(c.nodes) && s.proposers != Set::<int>::empty()
    &&& s.queues.dom() == c.nodes && s.acks.dom() == c.nodes
    &&& 0 <= s.phase <= 2
    &&& forall|a: int| #![trigger c.nodes.contains(a)] c.nodes.contains(a) ==> s.queues[a].no_duplicates()
        && s.queues[a].to_set().subset_of(s.calls) && s.acks[a].subset_of(s.calls)
    &&& forall|a: int, x: int, y: int| #![trigger c.nodes.contains(a), c.conflict.contains((x, y))] c.nodes.contains(a)
        && s.acks[a].contains(x) && s.acks[a].contains(y)
        && !s.base.contains(x) && !s.base.contains(y) ==> !c.conflict.contains((x, y))
    &&& forall|p: int, x: int| #![trigger promise_order(s, c, p, x)] s.proposers.contains(p) && s.acks[p].contains(x)
        && !s.base.contains(x) ==> promise_order(s, c, p, x)
    &&& forall|x: int| #![trigger certificate(s, c, x)] s.pending.contains(x) ==> certificate(s, c, x)
    &&& forall|x: int, y: int| s.pending.contains(x) && s.pending.contains(y)
        && x != y ==> independent(c, x, y)
    &&& s.phase != 0 ==> r::inv(s.core, c) && s.cut.subset_of(s.base)
        && forall|a: int| #![trigger c.nodes.contains(a)] #![trigger s.core.logs[a]] c.nodes.contains(a) ==> s.core.logs[a] == s.acks[a].difference(s.cut)
    &&& s.phase == 2 ==> r::chosen(s.core, c, s.recovery_ballot, s.batch)
        && s.batch.subset_of(s.calls)
}
pub open spec fn seeded(c: r::Config, logs: Map<int, Set<int>>) -> r::State {
    r::State {
        logs, frozen: Set::<int>::empty(),
        promise: Map::new(c.nodes, |a: int| -1), last: Map::new(c.nodes, |a: int| -1),
        value: Map::new(c.nodes, |a: int| Set::<int>::empty()),
        replies: Map::<(int, int), r::Snapshot>::empty(),
        proposals: Map::<int, Set<int>>::empty(), votes: Set::<(int, int, Set<int>)>::empty(),
    }
}
pub open spec fn init(s: State, c: r::Config, proposers: Set<int>) -> bool {
    &&& proposers.subset_of(c.nodes) && proposers != Set::<int>::empty()
    &&& s.calls == Set::<int>::empty() && s.base == Set::<int>::empty() && s.pending == Set::<int>::empty()
    &&& s.proposers == proposers && s.phase == 0
    &&& s.queues == Map::new(c.nodes, |a: int| Seq::<int>::empty())
    &&& s.acks == Map::new(c.nodes, |a: int| Set::<int>::empty())
    &&& s.cut == Set::<int>::empty() && r::init(s.core, c)
    &&& s.recovery_ballot == -1 && s.batch == Set::<int>::empty()
}
pub open spec fn invoke(s: State, t: State, c: r::Config, x: int) -> bool {
    c.commands.contains(x) && !s.calls.contains(x) && t == State { calls: s.calls.insert(x), ..s }
}
// PR2: the host's proposal queue preserves the shim's arrival order.
pub open spec fn propose(s: State, t: State, p: int, x: int) -> bool {
    &&& s.phase == 0 && s.proposers.contains(p) && s.calls.contains(x)
    &&& !s.queues[p].contains(x)
    &&& t == State { queues: s.queues.insert(p, s.queues[p].push(x)), ..s }
}
pub open spec fn acknowledge(s: State, t: State, c: r::Config, a: int, x: int) -> bool {
    &&& c.nodes.contains(a) && s.calls.contains(x) && !s.base.contains(x)
    &&& forall|y: int| #![trigger s.base.contains(y)] s.acks[a].contains(y) && !s.base.contains(y) ==> !c.conflict.contains((x, y))
    &&& s.proposers.contains(a) ==> s.queues[a].contains(x)
        && forall|y: int| #![trigger s.base.contains(y)] s.queues[a].contains(y) && !s.base.contains(y) ==> !c.conflict.contains((x, y))
    &&& if s.phase == 0 { t.core == s.core }
        else { r::acknowledge(s.core, t.core, c, a, x) }
    &&& t == State { acks: s.acks.insert(a, s.acks[a].insert(x)), core: t.core, ..s }
}
pub open spec fn fast(s: State, t: State, c: r::Config, x: int) -> bool {
    &&& s.calls.contains(x) && !s.base.contains(x) && !s.pending.contains(x)
    &&& certificate(s, c, x)
    &&& t == State { pending: s.pending.insert(x), ..s }
}
// PR1: an earlier conflicting proposal must execute before this proposal.
pub open spec fn ready(s: State, c: r::Config, p: int, x: int) -> bool {
    s.proposers.contains(p) && s.queues[p].contains(x)
        && forall|y: int| #![trigger s.base.contains(y)] before(s.queues[p], y, x) && c.conflict.contains((y, x)) ==> s.base.contains(y)
}
pub open spec fn commit(s: State, t: State, c: r::Config, x: int, from_recovery: bool) -> bool {
    &&& s.calls.contains(x) && !s.base.contains(x) && s.phase != 1
    &&& if from_recovery { s.phase == 2 && s.batch.contains(x) }
        else { exists|p: int| ready(s, c, p, x) }
    &&& t == State { base: s.base.insert(x), pending: s.pending.remove(x), ..s }
}
// Host recovery contract: retain any per-proposer prefix, including empty.
// This is the cut after the host fences old proposal admission. Its distributed
// implementation is not verified here. Committed commands remain in base.
pub open spec fn begin_recovery(s: State, t: State, c: r::Config, queues: Map<int, Seq<int>>) -> bool {
    &&& s.phase == 0 && queues.dom() == c.nodes
    &&& forall|p: int| #![trigger c.nodes.contains(p)] c.nodes.contains(p) ==> prefix(queues[p], s.queues[p])
    &&& t == State {
        phase: 1, queues, cut: s.base,
        core: seeded(c, Map::new(c.nodes, |a: int| s.acks[a].difference(s.base))), ..s
    }
}
pub open spec fn core_step(s: State, t: State, c: r::Config, action: r::Action) -> bool {
    &&& s.phase != 0
    &&& !(action is Acknowledge)
    &&& r::next(s.core, t.core, c, action)
    &&& t == State { core: t.core, ..s }
}
pub open spec fn choose_batch(s: State, t: State, c: r::Config, b: int, v: Set<int>) -> bool {
    &&& s.phase == 1 && r::chosen(s.core, c, b, v)
    &&& t == State { phase: 2, recovery_ballot: b, batch: v, ..s }
}
// Principle 2: even an empty batch needs this marker before normal admission.
pub open spec fn finish(s: State, t: State, c: r::Config, proposers: Set<int>) -> bool {
    &&& s.phase == 2 && s.batch.subset_of(s.base)
    &&& proposers.subset_of(c.nodes) && proposers != Set::<int>::empty()
    &&& t == State {
        phase: 0, proposers,
        queues: Map::new(c.nodes, |a: int| Seq::<int>::empty()),
        acks: Map::new(c.nodes, |a: int| Set::<int>::empty()), ..s
    }
}
pub enum Action {
    Invoke { command: int }, Propose { proposer: int, command: int },
    Acknowledge { node: int, command: int }, Fast { command: int },
    Commit { command: int, from_recovery: bool },
    BeginRecovery { queues: Map<int, Seq<int>> }, Core { action: r::Action },
    ChooseBatch { ballot: int, value: Set<int> }, Finish { proposers: Set<int> }, Stutter,
}
pub open spec fn next(s: State, t: State, c: r::Config, action: Action) -> bool {
    match action {
        Action::Invoke { command } => invoke(s, t, c, command),
        Action::Propose { proposer, command } => propose(s, t, proposer, command),
        Action::Acknowledge { node, command } => acknowledge(s, t, c, node, command),
        Action::Fast { command } => fast(s, t, c, command),
        Action::Commit { command, from_recovery } => commit(s, t, c, command, from_recovery),
        Action::BeginRecovery { queues } => begin_recovery(s, t, c, queues),
        Action::Core { action } => core_step(s, t, c, action),
        Action::ChooseBatch { ballot, value } => choose_batch(s, t, c, ballot, value),
        Action::Finish { proposers } => finish(s, t, c, proposers),
        Action::Stutter => t == s,
    }
}

pub proof fn init_inv(s: State, c: r::Config, proposers: Set<int>)
    requires r::config_ok(c), init(s, c, proposers),
    ensures inv(s, c),
{}

pub proof fn two_certificates_compatible(s: State, c: r::Config, x: int, y: int)
    requires r::config_ok(c), inv(s, c), certificate(s, c, x), certificate(s, c, y),
        !s.base.contains(x), !s.base.contains(y), x != y,
    ensures independent(c, x, y),
{
    assert(exists|p: int| s.proposers.contains(p)) by {
        if !(exists|p: int| s.proposers.contains(p)) { assert(s.proposers =~= Set::<int>::empty()); }
    }
    let p = choose|p: int| s.proposers.contains(p);
    assert(s.acks[p].contains(x) && s.acks[p].contains(y));
}
pub proof fn pending_is_recoverable(s: State, c: r::Config, x: int)
    requires r::config_ok(c), inv(s, c), s.phase != 0, s.pending.contains(x),
    ensures r::fast_committed(s.core, c, x),
{
    assert(certificate(s, c, x));
    assert(s.calls.contains(x));
    assert(c.commands.contains(x));
    assert(!s.cut.contains(x));
    assert(r::support(s.core.logs, c.nodes, x) =~= r::support(s.acks, c.nodes, x));
}
pub proof fn commit_respects_fast(s: State, t: State, c: r::Config, x: int, from_recovery: bool)
    requires r::config_ok(c), inv(s, c), commit(s, t, c, x, from_recovery),
    ensures forall|y: int| #![trigger independent(c, x, y)] s.pending.contains(y) && x != y ==> independent(c, x, y),
{
    assert forall|y: int| #![trigger independent(c, x, y)] s.pending.contains(y) && x != y implies independent(c, x, y) by {
        if from_recovery {
            pending_is_recoverable(s, c, y);
            r::recovery_complete_and_safe(s.core, c, s.recovery_ballot, s.batch, y);
            assert(!c.conflict.contains((y, x)));
        } else {
            let p = choose|p: int| ready(s, c, p, x);
            assert(certificate(s, c, y));
            assert(s.acks[p].contains(y));
            assert(promise_order(s, c, p, y));
            if c.conflict.contains((x, y)) {
                assert(c.conflict.contains((y, x)));
                assert(before(s.queues[p], y, x));
                assert(s.base.contains(y));
            }
        }
    }
}

pub proof fn frame_promises(s: State, t: State, c: r::Config, p: int, x: int)
    requires promise_order(s, c, p, x), s.queues == t.queues, s.base.subset_of(t.base),
        t.phase == 0 ==> s.phase == 0,
    ensures promise_order(t, c, p, x),
{
    assert forall|y: int| #![trigger t.base.contains(y)] t.queues[p].contains(y) && !t.base.contains(y) && c.conflict.contains((x, y))
        implies before(t.queues[p], x, y) by {
        assert(!s.base.contains(y));
        assert(before(s.queues[p], x, y));
    }
}
pub proof fn growing_base_preserves(s: State, t: State, c: r::Config)
    requires inv(s, c), s.queues == t.queues, s.acks == t.acks, s.proposers == t.proposers,
        s.core == t.core, s.cut == t.cut, s.phase == t.phase,
        s.batch == t.batch, s.recovery_ballot == t.recovery_ballot,
        s.base.subset_of(t.base), t.base.subset_of(t.calls),
        s.calls.subset_of(t.calls), t.calls.subset_of(c.commands),
        t.pending.subset_of(s.pending), t.pending.disjoint(t.base),
    ensures inv(t, c),
{
    assert forall|a: int| #![trigger c.nodes.contains(a)] c.nodes.contains(a) implies t.queues[a].no_duplicates()
        && t.queues[a].to_set().subset_of(t.calls) && t.acks[a].subset_of(t.calls) by {
        assert(s.queues[a].to_set().subset_of(s.calls) && s.acks[a].subset_of(s.calls));
    }
    assert forall|p: int, x: int| #![trigger promise_order(t, c, p, x)] t.proposers.contains(p) && t.acks[p].contains(x) && !t.base.contains(x)
        implies promise_order(t, c, p, x) by {
        assert(promise_order(s, c, p, x));
        frame_promises(s, t, c, p, x);
    }
    assert forall|x: int| #![trigger certificate(t, c, x)] t.pending.contains(x) implies certificate(t, c, x) by {
        assert(certificate(s, c, x));
    }
}
pub proof fn push_preserves_before(q: Seq<int>, x: int, y: int, z: int)
    requires before(q, x, y),
    ensures before(q.push(z), x, y),
{
    let (i, j) = choose|i: int, j: int| 0 <= i < j < q.len() && q[i] == x && q[j] == y;
    assert(q.push(z)[i] == x && q.push(z)[j] == y);
}
pub proof fn prefix_preserves_before(p: Seq<int>, q: Seq<int>, x: int, y: int)
    requires prefix(p, q), q.no_duplicates(), p.contains(y), before(q, x, y),
    ensures before(p, x, y),
{
    let (i, j) = choose|i: int, j: int| 0 <= i < j < q.len() && q[i] == x && q[j] == y;
    let k = choose|k: int| 0 <= k < p.len() && p[k] == y;
    assert(q[k] == q[j]);
    assert(k == j);
    assert(p[i] == x && p[j] == y);
}
pub proof fn propose_preserves(s: State, t: State, c: r::Config, p: int, x: int)
    requires r::config_ok(c), inv(s, c), propose(s, t, p, x),
    ensures inv(t, c),
{
    assert(t.queues.dom() =~= c.nodes);
    assert forall|a: int| #![trigger c.nodes.contains(a)] c.nodes.contains(a) implies t.queues[a].no_duplicates()
        && t.queues[a].to_set().subset_of(t.calls) && t.acks[a].subset_of(t.calls) by {
        if a == p {
            s.queues[p].lemma_push_to_set_commute(x);
            assert(t.queues[p].no_duplicates());
        }
    }
    assert forall|a: int, y: int| #![trigger promise_order(t, c, a, y)] t.proposers.contains(a) && t.acks[a].contains(y) && !t.base.contains(y)
        implies promise_order(t, c, a, y) by {
        assert(promise_order(s, c, a, y));
        if a == p {
            assert(s.queues[p].contains(y));
            let witness = choose|i: int| 0 <= i < s.queues[p].len() && s.queues[p][i] == y;
            assert(t.queues[p][witness] == y);
            assert(t.queues[p].contains(y));
            assert forall|z: int| #![trigger t.base.contains(z)] t.queues[p].contains(z) && !t.base.contains(z) && c.conflict.contains((y, z))
                implies before(t.queues[p], y, z) by {
                if z == x {
                    let i = choose|i: int| 0 <= i < s.queues[p].len() && s.queues[p][i] == y;
                    assert(t.queues[p][i] == y && t.queues[p][s.queues[p].len() as int] == z);
                } else {
                    assert(s.queues[p].contains(z));
                    assert(before(s.queues[p], y, z));
                    push_preserves_before(s.queues[p], y, z, x);
                }
            }
        } else {
            assert forall|z: int| #![trigger t.base.contains(z)] t.queues[a].contains(z) && !t.base.contains(z) && c.conflict.contains((y, z))
                implies before(t.queues[a], y, z) by { assert(before(s.queues[a], y, z)); }
        }
    }
    assert forall|y: int| #![trigger certificate(t, c, y)] t.pending.contains(y) implies certificate(t, c, y) by { assert(certificate(s, c, y)); }
}
pub proof fn acknowledge_preserves(s: State, t: State, c: r::Config, a: int, x: int)
    requires r::config_ok(c), inv(s, c), acknowledge(s, t, c, a, x),
    ensures inv(t, c),
{
    assert(t.acks.dom() =~= c.nodes);
    if s.phase != 0 { r::acknowledge_preserves(s.core, t.core, c, a, x); }
    assert forall|n: int| #![trigger c.nodes.contains(n)] c.nodes.contains(n) implies t.queues[n].no_duplicates()
        && t.queues[n].to_set().subset_of(t.calls) && t.acks[n].subset_of(t.calls) by {
        assert(s.acks[n].subset_of(s.calls));
    }
    assert forall|n: int, y: int, z: int| #![trigger c.nodes.contains(n), c.conflict.contains((y, z))] c.nodes.contains(n)
        && t.acks[n].contains(y) && t.acks[n].contains(z) && !t.base.contains(y) && !t.base.contains(z)
        implies !c.conflict.contains((y, z)) by {
        if n == a && (y == x || z == x) {
            if y != x { assert(!c.conflict.contains((x, y))); }
            if z != x { assert(!c.conflict.contains((x, z))); }
        }
    }
    assert forall|p: int, y: int| #![trigger promise_order(t, c, p, y)] t.proposers.contains(p) && t.acks[p].contains(y) && !t.base.contains(y)
        implies promise_order(t, c, p, y) by {
        if p == a && y == x {
            assert forall|z: int| #![trigger t.base.contains(z)] t.queues[p].contains(z) && !t.base.contains(z) && c.conflict.contains((y, z))
                implies before(t.queues[p], y, z) by {
                assert(!c.conflict.contains((x, z)));
            }
        } else {
            assert(promise_order(s, c, p, y));
            frame_promises(s, t, c, p, y);
        }
    }
    assert forall|y: int| #![trigger certificate(t, c, y)] t.pending.contains(y) implies certificate(t, c, y) by {
        assert(certificate(s, c, y));
        assert(r::support(s.acks, c.nodes, y).subset_of(r::support(t.acks, c.nodes, y)));
        vstd::set_lib::lemma_len_subset(r::support(s.acks, c.nodes, y), r::support(t.acks, c.nodes, y));
    }
    if s.phase != 0 {
        assert(!s.cut.contains(x));
        assert forall|n: int| #![trigger c.nodes.contains(n)] #![trigger t.core.logs[n]] c.nodes.contains(n) implies t.core.logs[n] == t.acks[n].difference(t.cut) by {
            assert(t.core.logs[n] =~= t.acks[n].difference(t.cut));
        }
    }
    if s.phase == 2 {
        r::certificates_monotone(s.core, t.core, c, s.recovery_ballot, s.batch, x);
    }
}
pub proof fn fast_preserves(s: State, t: State, c: r::Config, x: int)
    requires r::config_ok(c), inv(s, c), fast(s, t, c, x),
    ensures inv(t, c), forall|y: int| #![trigger independent(c, x, y)] s.pending.contains(y) ==> independent(c, x, y),
{
    assert forall|y: int| #![trigger independent(c, x, y)] s.pending.contains(y) implies independent(c, x, y) by {
        assert(certificate(s, c, y));
        two_certificates_compatible(s, c, x, y);
    }
    assert forall|y: int| #![trigger certificate(t, c, y)] t.pending.contains(y) implies certificate(t, c, y) by {
        if y != x { assert(certificate(s, c, y)); }
    }
    assert forall|y: int, z: int| t.pending.contains(y) && t.pending.contains(z) && y != z
        implies independent(c, y, z) by {
        if y == x { assert(independent(c, x, z)); }
        else if z == x { assert(independent(c, x, y)); }
    }
    assert forall|p: int, y: int| #![trigger promise_order(t, c, p, y)] t.proposers.contains(p) && t.acks[p].contains(y) && !t.base.contains(y)
        implies promise_order(t, c, p, y) by {
        assert(promise_order(s, c, p, y)); frame_promises(s, t, c, p, y);
    }
}
pub proof fn begin_preserves(s: State, t: State, c: r::Config, queues: Map<int, Seq<int>>)
    requires r::config_ok(c), inv(s, c), begin_recovery(s, t, c, queues),
    ensures inv(t, c),
{
    assert forall|a: int| #![trigger c.nodes.contains(a)] c.nodes.contains(a) implies queues[a].no_duplicates()
        && queues[a].to_set().subset_of(t.calls) && t.acks[a].subset_of(t.calls) by {
        assert(prefix(queues[a], s.queues[a]));
        assert(queues[a].to_set().subset_of(s.queues[a].to_set())) by {
            assert forall|x: int| #![trigger queues[a].contains(x)] queues[a].contains(x) implies s.queues[a].contains(x) by {
                let i = choose|i: int| 0 <= i < queues[a].len() && queues[a][i] == x;
                assert(s.queues[a][i] == x);
            }
        }
        assert(queues[a].no_duplicates());
    }
    assert forall|p: int, x: int| #![trigger promise_order(t, c, p, x)] t.proposers.contains(p) && t.acks[p].contains(x) && !t.base.contains(x)
        implies promise_order(t, c, p, x) by {
        assert(promise_order(s, c, p, x));
        assert forall|y: int| #![trigger queues[p].contains(y)] #![trigger t.base.contains(y)] queues[p].contains(y) && !t.base.contains(y) && c.conflict.contains((x, y))
            implies before(queues[p], x, y) by {
            assert(s.queues[p].contains(y));
            assert(before(s.queues[p], x, y));
            prefix_preserves_before(queues[p], s.queues[p], x, y);
        }
    }
    assert forall|x: int| #![trigger certificate(t, c, x)] t.pending.contains(x) implies certificate(t, c, x) by { assert(certificate(s, c, x)); }
    assert forall|a: int, x: int, y: int| #![trigger c.nodes.contains(a), c.conflict.contains((x, y))] c.nodes.contains(a)
        && t.core.logs[a].contains(x) && t.core.logs[a].contains(y) implies !c.conflict.contains((x, y)) by {
        assert(s.acks[a].contains(x) && s.acks[a].contains(y) && !s.base.contains(x) && !s.base.contains(y));
    }
    assert(r::inv(t.core, c));
}
pub proof fn core_preserves(s: State, t: State, c: r::Config, action: r::Action)
    requires r::config_ok(c), inv(s, c), core_step(s, t, c, action),
    ensures inv(t, c),
{
    r::step_preserves(s.core, t.core, c, action);
    match action {
        r::Action::Acknowledge { .. } => {},
        r::Action::Freeze { .. } => {}, r::Action::Prepare { .. } => {},
        r::Action::Propose { .. } => {}, r::Action::Accept { .. } => {}, r::Action::Stutter => {},
    }
    assert(s.core.logs == t.core.logs);
    if s.phase == 2 { r::certificates_monotone(s.core, t.core, c, s.recovery_ballot, s.batch, 0); }
    assert forall|p: int, x: int| #![trigger promise_order(t, c, p, x)] t.proposers.contains(p) && t.acks[p].contains(x) && !t.base.contains(x)
        implies promise_order(t, c, p, x) by {
        assert(promise_order(s, c, p, x)); frame_promises(s, t, c, p, x);
    }
    assert forall|x: int| #![trigger certificate(t, c, x)] t.pending.contains(x) implies certificate(t, c, x) by { assert(certificate(s, c, x)); }
}
pub proof fn candidate_is_invoked(s: State, c: r::Config, v: Set<int>)
    requires r::config_ok(c), inv(s, c), s.phase != 0, r::candidate(s.core, c, v),
    ensures v.subset_of(s.calls),
{
    let q = choose|q: Set<int>| #![trigger r::quorum(c, q)] r::quorum(c, q) && q.subset_of(s.core.frozen)
        && v == r::selected(c, s.core.logs, q);
    assert forall|x: int| #![trigger v.contains(x)] v.contains(x) implies s.calls.contains(x) by {
        let support = r::support(s.core.logs, q, x);
        assert(support.len() >= r::threshold(c) > 0);
        vstd::set::lemma_set_choose_len(support);
        let a = support.choose();
        assert(q.contains(a) && s.core.logs[a].contains(x));
        assert(s.acks[a].contains(x));
    }
}
pub proof fn batch_preserves(s: State, t: State, c: r::Config, b: int, v: Set<int>)
    requires r::config_ok(c), inv(s, c), choose_batch(s, t, c, b, v),
    ensures inv(t, c),
{
    let q = choose|q: Set<int>| r::quorum(c, q) && forall|a: int| #![trigger q.contains(a)] q.contains(a) ==> r::voted(s.core, a, b, v);
    r::quorum_intersection(c, q, q);
    let a = choose|a: int| q.contains(a);
    assert(r::voted(s.core, a, b, v));
    assert(s.core.proposals.dom().contains(b) && s.core.proposals[b] == v);
    assert(r::candidate(s.core, c, v));
    candidate_is_invoked(s, c, v);
    assert forall|p: int, x: int| #![trigger promise_order(t, c, p, x)] t.proposers.contains(p) && t.acks[p].contains(x) && !t.base.contains(x)
        implies promise_order(t, c, p, x) by {
        assert(promise_order(s, c, p, x)); frame_promises(s, t, c, p, x);
    }
    assert forall|x: int| #![trigger certificate(t, c, x)] t.pending.contains(x) implies certificate(t, c, x) by { assert(certificate(s, c, x)); }
}
pub proof fn finish_preserves(s: State, t: State, c: r::Config, proposers: Set<int>)
    requires r::config_ok(c), inv(s, c), finish(s, t, c, proposers),
    ensures inv(t, c), s.pending == Set::<int>::empty(),
{
    assert forall|x: int| s.pending.contains(x) implies false by {
        pending_is_recoverable(s, c, x);
        r::recovery_complete_and_safe(s.core, c, s.recovery_ballot, s.batch, x);
        assert(s.base.contains(x));
    }
    assert(s.pending =~= Set::<int>::empty());
}
pub proof fn step_preserves(s: State, t: State, c: r::Config, action: Action)
    requires r::config_ok(c), inv(s, c), next(s, t, c, action),
    ensures inv(t, c), s.base.subset_of(t.base), s.calls.subset_of(t.calls),
{
    match action {
        Action::Invoke { command } => growing_base_preserves(s, t, c),
        Action::Propose { proposer, command } => propose_preserves(s, t, c, proposer, command),
        Action::Acknowledge { node, command } => acknowledge_preserves(s, t, c, node, command),
        Action::Fast { command } => fast_preserves(s, t, c, command),
        Action::Commit { command, from_recovery } => growing_base_preserves(s, t, c),
        Action::BeginRecovery { queues } => begin_preserves(s, t, c, queues),
        Action::Core { action } => core_preserves(s, t, c, action),
        Action::ChooseBatch { ballot, value } => batch_preserves(s, t, c, ballot, value),
        Action::Finish { proposers } => finish_preserves(s, t, c, proposers),
        Action::Stutter => {},
    }
}

} // verus!
