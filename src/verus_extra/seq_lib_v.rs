use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {

pub proof fn lemma_subrange_subrange<A>(s: Seq<A>, start: int, midsize: int, endsize: int)
  requires
    0 <= start <= s.len(),
    0 <= midsize <= endsize <= s.len() - start,
  ensures
    s.subrange(start, start + endsize).subrange(0, midsize) == s.subrange(start, start + midsize),
{
  assert(s.subrange(start, start + endsize).subrange(0, midsize) =~= s.subrange(start, start + midsize));
}


pub proof fn lemma_seq_add_subrange<A>(s: Seq<A>, i: int, j: int, k: int)
  requires 0 <= i <= j <= k <= s.len(),
  ensures s.subrange(i, j) + s.subrange(j, k) == s.subrange(i, k),
{
    assert_seqs_equal!{s.subrange(i, j) + s.subrange(j, k), s.subrange(i, k)}
}

pub proof fn lemma_seq_fold_left_merge_right_assoc<A, B>(s: Seq<A>, init: B, f: spec_fn(A) -> B, g: spec_fn(B, B) -> B)
  requires
    s.len() > 0,
    forall |x, y, z|
      #[trigger]
      // #[trigger g(x, y)]
      g(g(x, y), z) == g(x, g(y, z)),
  ensures
    g(s.subrange(0, s.len() - 1).fold_left(init, |b: B, a: A| g(b, f(a))), f(s[s.len() - 1]))
    ==
    s.fold_left(init, |b: B, a: A| g(b, f(a)))
  decreases s.len(),
{
  let emp = Seq::<B>::empty();
  let len: int = s.len() as int;
  let i = len - 1;
  let s1 = s.subrange(0, len - 1);
  let last = s[len - 1];
  let accf = |b: B, a: A| g(b, f(a));

  let start = s1.fold_left(init, accf);
  let all = s.fold_left(init, accf);

  if s1.len() == 0 {
    assert(s.len() == 1);
    reveal_with_fuel(Seq::fold_left, 2);
    reveal_with_fuel(Seq::fold_left, 2);
  } else {
    reveal_with_fuel(Seq::fold_left, 2);
    let head = s[0];
    let tail = s.subrange(1, len);
    let p = accf(init, s[0]);
    assert_seqs_equal!(tail.subrange(0, len - 2) == s1.subrange(1, len - 1));
    lemma_seq_fold_left_merge_right_assoc::<A, B>(tail, p, f, g);
  }
}

pub proof fn lemma_seq_fold_left_sum_right<A>(s: Seq<A>, low: int, f: spec_fn(A) -> int)
  requires
    s.len() > 0,
  ensures
    s.subrange(0, s.len() - 1).fold_left(low, |b: int, a: A| b + f(a)) + f(s[s.len() - 1])
    ==
    s.fold_left(low, |b: int, a: A| b + f(a))
{
  let g = |x: int, y: int| x + y;
  assert((|b: int, a: A| b + f(a)) =~= (|b: int, a: A| g(b, f(a))));
  lemma_seq_fold_left_merge_right_assoc::<A, int>(s, low, f, g);
}

pub proof fn lemma_seq_fold_left_append_right<A, B>(s: Seq<A>, prefix: Seq<B>, f: spec_fn(A) -> Seq<B>)
  requires s.len() > 0,
  ensures
    s.subrange(0, s.len() - 1).fold_left(prefix, |sb: Seq<B>, a: A| sb + f(a)) + f(s[s.len() - 1])
    ==
    s.fold_left(prefix, |sb: Seq<B>, a: A| sb + f(a))
{
  let g = |x: Seq<B>, y: Seq<B>| x + y;
  assert forall |x, y, z|
  #[trigger]
  // #[trigger g(x,y)]
  g(g(x, y), z) == g(x, g(y, z)) by {
    assert_seqs_equal!(g(g(x, y), z) == g(x, g(y, z)));
  };
  assert((|b: Seq<B>, a: A| b + f(a)) =~= (|b: Seq<B>, a: A| g(b, f(a))));
  lemma_seq_fold_left_merge_right_assoc::<A, Seq<B>>(s, prefix, f, g);
}

pub proof fn lemma_seq_fold_left_append_len_int<A, B>(s: Seq<A>, prefix: Seq<B>, f: spec_fn(A) -> Seq<B>)
  ensures
    s.fold_left(prefix, |sb: Seq<B>, a: A| sb + f(a)).len() as int
    ==
    s.fold_left(prefix.len() as int, |i: int, a: A| i + f(a).len() as int),
  decreases s.len(),
{
  s.lemma_fold_left_alt(prefix, |sb: Seq<B>, a: A| sb + f(a));
  s.lemma_fold_left_alt(prefix.len() as int, |i: int, a: A| i + f(a).len() as int);
  if s.len() != 0 {
    lemma_seq_fold_left_append_len_int::<A, B>(s.subrange(1, s.len() as int), prefix + f(s[0]), f);
    s.subrange(1, s.len() as int).lemma_fold_left_alt(prefix + f(s[0]), |sb: Seq<B>, a: A| sb + f(a));
    s.subrange(1, s.len() as int).lemma_fold_left_alt(prefix.len() as int + f(s[0]).len() as int, |i: int, a: A| i + f(a).len() as int);
  }
}

pub proof fn lemma_seq_fold_left_sum_len_int_positive<A, B>(s: Seq<A>, low: nat, f: spec_fn(A) -> Seq<B>)
  ensures
    s.fold_left(low as int, |acc: int, x: A| acc + f(x).len()) >= 0,
  decreases s.len(),
{
  s.lemma_fold_left_alt(low as int, |acc: int, x: A| acc + f(x).len());
  if s.len() != 0 {
    lemma_seq_fold_left_sum_len_int_positive::<A, B>(s.subrange(1, s.len() as int), low + f(s[0]).len(), f);
    s.subrange(1, s.len() as int).lemma_fold_left_alt(low + f(s[0]).len() as int, |acc: int, x: A| acc + f(x).len());
  }
}

pub proof fn lemma_seq_fold_left_append_len_int_le<A, B>(s: Seq<A>, i: int, low: int, f: spec_fn(A) -> Seq<B>)
  requires
    0 <= i <= s.len() as int,
    0 <= low,
  ensures
    s.fold_left(low, |acc: int, x: A| acc + f(x).len()) >= 0,
    s.subrange(0, i).fold_left(low, |acc: int, x: A| acc + f(x).len()) <=
    s.fold_left(low, |acc: int, x: A| acc + f(x).len()),
  decreases (2 * s.len() - i),
{
  lemma_seq_fold_left_sum_len_int_positive::<A, B>(s, low as nat, f);
  let accfl = |acc: int, x: A| acc + f(x).len();
  if s.len() == 0 {
    // done
  } else if i == s.len() {
    assert_seqs_equal!(s.subrange(0, i) == s);
    lemma_seq_fold_left_append_len_int_le::<A, B>(s.subrange(1, s.len() as int), i - 1, low + f(s[0]).len() as int, f);
  } else if i == s.len() - 1 {
    let fl = |x| f(x).len() as int;
    assert(accfl =~= (|acc: int, x: A| acc + fl(x)));
    lemma_seq_fold_left_sum_right::<A>(s, low, fl);
  } else {
    lemma_seq_fold_left_append_len_int_le::<A, B>(s.subrange(0, s.len() - 1), i, low, f);
    lemma_seq_fold_left_append_len_int_le::<A, B>(s, s.len() - 1, low, f);
    assert_seqs_equal!(s.subrange(0, s.len() - 1).subrange(0, i) == s.subrange(0, i));
  }
}

pub proof fn lemma_seq_fold_left_sum_le<A>(s: Seq<A>, init: int, high: int, f: spec_fn(A) -> int)
  requires
    forall |i:int| 0 <= i < s.len() ==> f(s[i]) <= high,
  ensures
    s.fold_left(init, |acc: int, x: A| acc + f(x)) <= init + s.len() * high,
  decreases s.len(),
{
  if s.len() != 0 {
    lemma_seq_fold_left_sum_le(s.drop_last(), init, high, f);
    assert(init + (s.len() - 1) * high + high <= init + s.len() * high) by (nonlinear_arith);
  }
}

pub proof fn lemma_if_everything_in_seq_satisfies_filter_then_filter_is_identity<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    requires forall |i: int| 0 <= i && i < s.len() ==> pred(s[i])
    ensures  s.filter(pred) == s
    decreases s.len()
{
    reveal(Seq::filter);
    if s.len() != 0 {
        let subseq = s.drop_last();
        lemma_if_everything_in_seq_satisfies_filter_then_filter_is_identity(subseq, pred);
        assert_seqs_equal!(s, subseq.push(s.last()));
    }
}

pub proof fn lemma_if_nothing_in_seq_satisfies_filter_then_filter_result_is_empty<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    requires forall |i: int| 0 <= i && i < s.len() ==> !pred(s[i])
    ensures  s.filter(pred) =~= Seq::<A>::empty()
    decreases s.len()
{
    reveal(Seq::filter);
    if s.len() != 0 {
        let subseq = s.drop_last();
        lemma_if_nothing_in_seq_satisfies_filter_then_filter_result_is_empty(subseq, pred);
        assert_seqs_equal!(s, subseq.push(s.last()));
    }
}

pub proof fn lemma_filter_skip_rejected<A>(s: Seq<A>, pred: spec_fn(A) -> bool, i: int)
    requires
        0 <= i <= s.len(),
        forall |j| 0 <= j < i ==> !pred(s[j]),
    ensures
        s.filter(pred) == s.skip(i).filter(pred)
    decreases
        s.len()
{
    reveal(Seq::filter);
    if s.len() == 0 {
        assert(s.skip(i) =~= s);
    }
    else if i < s.len() {
        assert(s.skip(i).drop_last() =~= s.drop_last().skip(i));
        lemma_filter_skip_rejected(s.drop_last(), pred, i);
    }
    else {
        assert(s.skip(i) =~= s.drop_last().skip(i - 1));
        lemma_filter_skip_rejected(s.drop_last(), pred, i - 1);
    }
}

pub proof fn lemma_fold_left_on_equiv_seqs<A, B>(s1: Seq<A>, s2: Seq<A>, eq: spec_fn(A, A) -> bool, init: B, f: spec_fn(B, A) -> B)
    requires
      s1.len() == s2.len(),
      (forall |i: int| 0 <= i < s1.len() ==> eq(s1[i], s2[i])),
      (forall |b: B, a1: A, a2: A| #[trigger] eq(a1, a2) ==> #[trigger] f(b, a1) == f(b, a2)),
    ensures
      s1.fold_left(init, f) == s2.fold_left(init, f)
    decreases s1.len(),
{
  reveal(Seq::fold_left);
  if s1.len() != 0 {
    lemma_fold_left_on_equiv_seqs(s1.drop_last(), s2.drop_last(), eq, init, f);
  }
}

pub proof fn lemma_fold_left_append_merge<A, B>(s1: Seq<A>, s2: Seq<A>, f: spec_fn(A) -> Seq<B>)
  ensures
    (s1 + s2).fold_left(Seq::empty(), |acc: Seq<B>, a: A| acc + f(a))
      ==
    s1.fold_left(Seq::empty(), |acc: Seq<B>, a: A| acc + f(a))
      +
    s2.fold_left(Seq::empty(), |acc: Seq<B>, a: A| acc + f(a))
  decreases
    s1.len() + s2.len()
{
  let e = Seq::<B>::empty();
  let af = |acc: Seq<B>, a: A| acc + f(a);
  let fl = |s: Seq<A>| s.fold_left(e, af);
  if s2.len() == 0 {
    assert(s1 + s2 =~= s1);
    assert(fl(s1) =~= fl(s1) + e);
  } else {
    lemma_fold_left_append_merge(s1, s2.drop_last(), f);
    assert((s1 + s2).drop_last() =~= s1 + s2.drop_last());
    assert((fl(s1) + fl(s2.drop_last())) + f(s2.last()) =~= fl(s1) + (fl(s2.drop_last()) + f(s2.last())));
  }
}

/// Membership in a flattened sequence-of-sequences.
///
/// vstd proves a good deal about `flatten` -- its length, its relationship to
/// `flatten_alt`, how it behaves under `push` and on singletons -- but nothing
/// about *membership*, and membership is the only thing the RSL refinement
/// proof needs (Phase 54.12.c). Its request and reply sets are currently built
/// with `Set::new_assuming_finite`, which vstd deprecates precisely because it
/// assumes rather than establishes finiteness. Expressing them instead as
/// `<seq>.flatten().to_set()` makes them finite by construction, and this lemma
/// is what lets the existing `.contains`-based proofs carry over unchanged.
///
/// Proved by induction on `s`, unfolding vstd's recursive definition
/// `flatten() == first().add(drop_first().flatten())`. The step is done at the
/// level of `to_set` rather than `contains`: vstd has no membership lemma for
/// `Seq::add`, but `lemma_to_set_distributes_over_addition` gives
/// `(a + b).to_set() == a.to_set() + b.to_set()`, and `to_set_ensures` carries
/// that back to `contains` in both directions.
pub proof fn lemma_flatten_contains<A>(s: Seq<Seq<A>>, x: A)
  ensures
    s.flatten().contains(x) <==> exists |i: int| 0 <= i < s.len() && (#[trigger] s[i]).contains(x),
  decreases s.len(),
{
  broadcast use Seq::to_set_ensures;
  broadcast use vstd::set::group_set_lemmas;

  if s.len() == 0 {
    assert(s.flatten() =~= Seq::<A>::empty());
    assert(!s.flatten().contains(x));
  } else {
    let rest = s.drop_first();
    lemma_flatten_contains(rest, x);
    let head = s.first();
    let tail = rest.flatten();
    assert(s.flatten() =~= head + tail);
    crate::verus_extra::set_lib_ext_v::lemma_to_set_distributes_over_addition(head, tail);
    assert((head + tail).to_set() == head.to_set() + tail.to_set());
    // (first + rest.flatten()).to_set() == first.to_set() + rest.flatten().to_set(),
    // and to_set_ensures carries that back to `contains` in both directions.

    if s.flatten().contains(x) {
      if s.first().contains(x) {
        assert(s[0].contains(x));
        assert(exists |i: int| 0 <= i < s.len() && #[trigger] s[i].contains(x));
      } else {
        let j = choose |j: int| #![trigger rest[j]] 0 <= j < rest.len() && rest[j].contains(x);
        assert(s[j + 1] == rest[j]);
        assert(s[j + 1].contains(x));
        assert(exists |i: int| 0 <= i < s.len() && #[trigger] s[i].contains(x));
      }
    }

    if exists |i: int| 0 <= i < s.len() && #[trigger] s[i].contains(x) {
      let i = choose |i: int| #![trigger s[i]] 0 <= i < s.len() && s[i].contains(x);
      if i == 0 {
        assert(head == s[0]);
        assert(head.contains(x));
      } else {
        assert(rest[i - 1] == s[i]);
        assert(rest[i - 1].contains(x));
        assert(exists |j: int| 0 <= j < rest.len() && #[trigger] rest[j].contains(x));
        assert(tail.contains(x));
      }
      // Spell out every hop: contains -> to_set -> union -> distributed
      // to_set -> back to contains. The solver does not chain these on its own.
      assert(head.to_set().contains(x) || tail.to_set().contains(x));
      assert((head.to_set() + tail.to_set()).contains(x));
      assert((head + tail).to_set().contains(x));
      assert((head + tail).contains(x));
      assert(s.flatten().contains(x));
    }
  }
}

pub proof fn some_differing_index_for_unequal_seqs<A>(s1: Seq<A>, s2: Seq<A>) -> (i: int)
  requires
    s1 != s2,
    s1.len() == s2.len(),
  ensures
    0 <= i < s1.len(),
    s1[i] != s2[i],
{
  if forall |i| 0 <= i < s1.len() ==> s1[i] == s2[i] {
    assert(s1 =~= s2);
  }
  choose |i:int| 0 <= i < s1.len() && s1[i] != s2[i]
}

} // verus!
