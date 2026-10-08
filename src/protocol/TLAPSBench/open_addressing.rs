//! OpenAddressingModel/Defs, TLAPS-Bench ffa3e31da28f960b70d8c5d44f2735e75d6edcac.
//! This is a handwritten state machine, including the eviction subroutine.
//! Table indices remain one-based; Rust sequences and stacks are zero-based.
use vstd::prelude::*;

verus! {

pub enum Cell { Empty, Value(int) }
pub open spec fn value(x: Cell) -> int { match x { Cell::Value(v) => v, Cell::Empty => 0 } }
pub enum Pc {
    Pick, Put, WaitEv, EndWEv, ChkSnc, Cntns, OnSnc, Insrt, IsMth, Cas,
    TryEv, WaitIns, EndEv, StrIns, NestedIns, Set, Flush, Rtrn, Done,
}
pub struct Frame { pub pc: Pc, pub ei: int, pub ej: int, pub lo: Cell }
pub struct LWriter {
    pub pc: Pc, pub stack: Seq<Frame>, pub ei: int, pub ej: int, pub lo: Cell,
    pub fp: int, pub index: int, pub result: bool, pub expected: Cell,
}
pub struct Constants {
    pub k: int, pub limit: int, pub fps: Set<int>, pub writers: Set<int>, pub readers: Set<int>,
}
pub struct LState {
    pub table: IMap<int, Cell>, pub external: Seq<int>, pub newexternal: Seq<int>,
    pub evict: bool, pub wait_count: int, pub history: Set<int>,
    pub threads: Map<int, LWriter>,
}
pub open spec fn valid_constants(c: Constants) -> bool {
    c.k > 0 && c.limit >= 0 && 2 * c.limit <= c.k && c.fps.len() > 1
    && forall |f: int| c.fps.contains(f) ==> f > 0
}
pub open spec fn minimum(s: Set<int>) -> int { choose |x: int| s.contains(x) && forall |y: int| s.contains(y) ==> x <= y }
pub open spec fn maximum(s: Set<int>) -> int { choose |x: int| s.contains(x) && forall |y: int| s.contains(y) ==> x >= y }
pub open spec fn wrap(i: int, k: int) -> int { if i % k == 0 { k } else { i % k } }
#[verifier::opaque]
pub open spec fn idx(c: Constants, fp: int, p: int) -> int {
    wrap(((c.k - 1) / (maximum(c.fps) - minimum(c.fps))) * (fp - minimum(c.fps) + 1) + p, c.k)
}
pub open spec fn wrapped(c: Constants, fp: int, pos: int) -> bool { idx(c, fp, 0) > wrap(pos, c.k) }
pub open spec fn matches(x: Cell, fp: int) -> bool { x == Cell::Value(fp) || x == Cell::Value(-fp) }
pub open spec fn marked(x: Cell) -> bool { x is Value && value(x) < 0 }
#[verifier::opaque]
pub open spec fn compare(c: Constants, a: Cell, i: int, b: Cell, j: int) -> int {
    if a is Value && b is Value && c.fps.contains(value(a)) && c.fps.contains(value(b)) {
        if wrapped(c, value(a), i) == wrapped(c, value(b), j) {
            if i > j && value(a) < value(b) { -1 } else { 1 }
        } else if i < j && value(a) < value(b) { -1 }
        else if i > j && value(a) > value(b) { -1 } else { 0 }
    } else { 0 }
}
pub open spec fn largest(s: Seq<int>) -> int { if s.len() == 0 { 0 } else { s.last() } }
pub open spec fn smaller(a: Seq<int>, b: Seq<int>, x: int) -> Seq<int> {
    a.filter(|v: int| largest(b) < v && v < x)
}
pub open spec fn larger(a: Seq<int>, b: Seq<int>) -> Seq<int> {
    if b.len() == 0 { a } else { a.filter(|v: int| largest(b) < v) }
}
pub open spec fn initial(c: Constants) -> LState {
    LState {
        table: IMap::new(|i: int| 1 <= i <= c.k, |i: int| Cell::Empty),
        external: Seq::empty(), newexternal: Seq::empty(), evict: false,
        wait_count: 0, history: Set::empty(),
        threads: Map::new(c.writers, |p: int| LWriter {
            pc: Pc::Pick, stack: Seq::empty(), ei: 1, ej: 1, lo: Cell::Value(0),
            fp: 0, index: 0, result: false, expected: Cell::Value(-1),
        }),
    }
}

// The selected fingerprint is a parameter only at Pick. All other choices are
// exactly the scheduler's choice of writer. Stuttering includes Terminating.
pub enum Action { Writer { p: int, pick: int }, Stutter }
#[verifier::opaque]
pub open spec fn enabled(s: LState, c: Constants, a: Action) -> bool {
    match a {
        Action::Stutter => true,
        Action::Writer { p, pick } => c.writers.contains(p) && {
            let t = s.threads[p];
            match t.pc {
                Pc::Done => false,
                Pc::Pick => c.fps.difference(s.history).is_empty()
                    || c.fps.contains(pick) && !s.history.contains(pick),
                Pc::WaitEv => !s.evict,
                Pc::WaitIns => s.wait_count == c.writers.len() - 1 + c.readers.len(),
                _ => true,
            }
        },
    }
}
#[verifier::opaque]
pub open spec fn thread_step(s: LState, c: Constants, p: int, pick: int) -> LWriter {
    let t = s.threads[p];
    match t.pc {
        Pc::Pick => if c.fps.difference(s.history).is_empty() { LWriter { pc: Pc::Done, ..t } }
            else { LWriter { fp: pick, pc: Pc::Put, ..t } },
        Pc::Put => LWriter { index: 0, result: false, expected: Cell::Value(c.limit),
            pc: if s.evict { Pc::WaitEv } else { Pc::ChkSnc }, ..t },
        Pc::WaitEv => LWriter { pc: Pc::EndWEv, ..t },
        Pc::EndWEv => LWriter { pc: Pc::Put, ..t },
        Pc::ChkSnc => LWriter { pc: if s.external.len() != 0 { Pc::Cntns } else { Pc::Insrt }, ..t },
        Pc::Cntns => if t.index < c.limit {
            let x = s.table[idx(c, t.fp, t.index)];
            if matches(x, t.fp) { LWriter { pc: Pc::Pick, ..t } }
            else if x is Empty { LWriter { expected: Cell::Value(if value(t.expected) < t.index { value(t.expected) } else { t.index }), pc: Pc::OnSnc, ..t } }
            else { LWriter { index: t.index + 1, expected: if marked(x) { Cell::Value(if value(t.expected) < t.index { value(t.expected) } else { t.index }) } else { t.expected }, ..t } }
        } else { LWriter { pc: Pc::OnSnc, ..t } },
        Pc::OnSnc => if s.external.contains(t.fp) { LWriter { pc: Pc::Pick, ..t } }
            else { LWriter { index: value(t.expected), expected: Cell::Value(-1), pc: Pc::Insrt, ..t } },
        Pc::Insrt => if t.index < c.limit {
            let x = s.table[idx(c, t.fp, t.index)];
            LWriter { expected: x, pc: if x is Empty || marked(x) && x != Cell::Value(-t.fp) { Pc::Cas } else { Pc::IsMth }, ..t }
        } else { LWriter { pc: Pc::TryEv, ..t } },
        Pc::IsMth => if matches(s.table[idx(c, t.fp, t.index)], t.fp) { LWriter { pc: Pc::Pick, ..t } }
            else { LWriter { index: t.index + 1, pc: Pc::Insrt, ..t } },
        Pc::Cas => { let ok = s.table[idx(c, t.fp, t.index)] == t.expected;
            LWriter { result: ok, pc: if ok { Pc::Pick } else { Pc::Insrt }, ..t } },
        Pc::TryEv => LWriter { pc: if !s.evict { Pc::WaitIns } else { Pc::Put }, ..t },
        Pc::WaitIns => LWriter {
            stack: seq![Frame { pc: Pc::EndEv, ei: t.ei, ej: t.ej, lo: t.lo }] + t.stack,
            ei: 1, ej: 1, lo: Cell::Value(0), pc: Pc::StrIns, ..t },
        Pc::EndEv => LWriter { pc: Pc::Put, ..t },
        Pc::StrIns => if t.ei <= c.k + c.limit { LWriter { lo: s.table[wrap(t.ei + 1, c.k)], pc: Pc::NestedIns, ..t } }
            else { LWriter { ei: 1, pc: Pc::Flush, ..t } },
        Pc::NestedIns => if compare(c, t.lo, wrap(t.ei + 1, c.k), s.table[wrap(t.ej, c.k)], wrap(t.ej, c.k)) <= -1 {
            LWriter { ej: t.ej - 1, pc: if t.ej == 0 { Pc::Set } else { Pc::NestedIns }, ..t }
        } else { LWriter { pc: Pc::Set, ..t } },
        Pc::Set => LWriter { ei: t.ei + 1, ej: t.ei + 1, pc: Pc::StrIns, ..t },
        Pc::Flush => if t.ei <= c.k + c.limit {
            LWriter { lo: s.table[wrap(t.ei, c.k)], ei: t.ei + 1, ..t }
        } else { LWriter { pc: Pc::Rtrn, ..t } },
        Pc::Rtrn => { let f = t.stack[0]; LWriter { pc: f.pc, ei: f.ei, ej: f.ej, lo: f.lo, stack: t.stack.drop_first(), ..t } },
        Pc::Done => t,
    }
}
pub open spec fn flush_append(s: LState, c: Constants, t: LWriter) -> bool {
    let x = s.table[wrap(t.ei, c.k)];
    x is Value && value(x) > largest(s.newexternal)
    && (t.ei <= c.k && !wrapped(c, value(x), t.ei)
        || t.ei > c.k && wrapped(c, value(x), t.ei))
}
#[verifier::opaque]
pub open spec fn apply(s: LState, c: Constants, a: Action) -> LState {
    match a {
        Action::Stutter => s,
        Action::Writer { p, pick } => {
            let t = s.threads[p];
            let u = LState { threads: s.threads.insert(p, thread_step(s, c, p, pick)), ..s };
            match t.pc {
                Pc::Put => LState { wait_count: if s.evict { s.wait_count + 1 } else { s.wait_count }, ..u },
                Pc::EndWEv => LState { wait_count: s.wait_count - 1, ..u },
                Pc::Cas => if s.table[idx(c, t.fp, t.index)] == t.expected {
                    LState { table: s.table.insert(idx(c, t.fp, t.index), Cell::Value(t.fp)), history: s.history.insert(t.fp), ..u }
                } else { u },
                Pc::TryEv => LState { evict: true, ..u },
                Pc::EndEv => LState { evict: false, ..u },
                Pc::NestedIns => if compare(c, t.lo, wrap(t.ei + 1, c.k), s.table[wrap(t.ej, c.k)], wrap(t.ej, c.k)) <= -1 {
                    LState { table: s.table.insert(wrap(t.ej + 1, c.k), s.table[wrap(t.ej, c.k)]), ..u }
                } else { u },
                Pc::Set => LState { table: s.table.insert(wrap(t.ej + 1, c.k), t.lo), ..u },
                Pc::Flush => if t.ei <= c.k + c.limit {
                    if flush_append(s, c, t) {
                        let x = value(s.table[wrap(t.ei, c.k)]);
                        LState { table: s.table.insert(wrap(t.ei, c.k), Cell::Value(-x)),
                            newexternal: (s.newexternal + smaller(s.external, s.newexternal, x)).push(x), ..u }
                    } else { u }
                } else { LState { external: s.newexternal + larger(s.external, s.newexternal), newexternal: Seq::empty(), ..u } },
                _ => u,
            }
        },
    }
}
#[verifier::opaque]
pub open spec fn next(s: LState, u: LState, c: Constants) -> bool {
    exists |a: Action| enabled(s, c, a) && u == apply(s, c, a)
}

// The five predicates in OpenAddressingDefs, with integer external sequences.
pub open spec fn abs(x: int) -> int { if x < 0 { -x } else { x } }
pub open spec fn contains(s: LState, c: Constants, f: int) -> bool {
    (exists |i: int| #![trigger idx(c, f, i)] 0 <= i <= c.limit && matches(s.table[idx(c, f, i)], f))
    || s.external.contains(f)
    || (f != 0 && s.evict && exists |p: int| #![trigger c.writers.contains(p)] c.writers.contains(p) && s.threads[p].lo == Cell::Value(f))
}
pub open spec fn contained_in_table(s: LState, c: Constants, f: int) -> bool {
    exists |i: int| #![trigger idx(c, abs(f), i)] 0 <= i <= c.limit && s.table[idx(c, abs(f), i)] == Cell::Value(f)
}
pub open spec fn complete_as_safety(s: LState, c: Constants) -> bool {
    forall |p: int| #![trigger c.writers.contains(p)] c.writers.contains(p) && s.threads[p].pc == Pc::Done ==> s.history == c.fps
}
pub open spec fn consistent(s: LState, c: Constants) -> bool {
    !s.evict ==> forall |f: int| #![trigger s.external.contains(f)] s.history.contains(f) ==>
        (contained_in_table(s, c, f) ==> !s.external.contains(f))
        && (contained_in_table(s, c, -f) ==> s.external.contains(f))
        && (!contained_in_table(s, c, f) ==> s.external.contains(f))
}
pub open spec fn contains_goal(s: LState, c: Constants) -> bool {
    (forall |f: int| #![trigger contains(s, c, f)] s.history.contains(f) ==> contains(s, c, f))
    && (forall |f: int| #![trigger contains(s, c, f)] c.fps.contains(f) && !s.history.contains(f) ==> !contains(s, c, f))
}
pub open spec fn duplicates(s: LState, c: Constants) -> bool {
    !s.evict ==> forall |i: int, j: int| #![trigger s.table[i], s.table[j]] 1 <= i < j <= c.k
        && s.table[i] is Value && s.table[j] is Value ==> abs(value(s.table[i])) != abs(value(s.table[j]))
}
// Pairwise strict ordering is equivalent to the benchmark's adjacent ordering.
pub open spec fn ordered(a: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i < j < a.len() ==> a[i] < a[j]
}
pub open spec fn sorted(s: LState) -> bool { ordered(s.external) && ordered(s.newexternal) }

} // verus!
