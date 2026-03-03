use vstd::prelude::*;
verus! {
    pub open spec fn Injective<X,Y>(f: spec_fn(X) -> Y) -> bool
    {
        forall |x1:X, x2:X| #![trigger f(x1), f(x2)] f(x1) == f(x2) ==> x1 == x2
    }

    pub open spec fn InjectiveOver<X, Y>(xs:Set<X>, ys:Set<Y>, f: spec_fn(X) -> Y) -> bool
        // reads f.reads
        // requires forall x :: x in xs ==> f.requires(x)
    {
        forall |x1:X, x2:X| #![trigger f(x1), f(x2)] xs.contains(x1) && xs.contains(x2) && ys.contains(f(x1)) && ys.contains(f(x2)) && f(x1) == f(x2) ==> x1 == x2
    }

    pub open spec fn MapSeqToSet<X,Y>(xs:Seq<X>, f: spec_fn(X) -> Y) -> Set<Y>
        recommends Injective(f)
    {
        Set::new(|y:Y| exists |x:X| xs.contains(x) && f(x) == y)
    }

    pub proof fn lemma_MapSeqToSet<X,Y>(xs:Seq<X>, f: spec_fn(X) -> Y)
        requires Injective(f)
        ensures forall |x:X| #[trigger] xs.contains(x) <==> MapSeqToSet(xs, f).contains(f(x))
    {

    }

    pub open spec fn intsetmax(s: Set<int>) -> int
        recommends s.len() > 0
    {
        choose |m: int|
            s.contains(m) &&
            forall |i: int| s.contains(i) ==> m >= i
    }

    #[verifier::external_body]
    pub proof fn lemma_intsetmax_ensures(s: Set<int>)
        requires s.len() > 0
        ensures ({
            let m = intsetmax(s);
            &&& s.contains(m)
            &&& forall |i: int| s.contains(i) ==> m >= i
        })
    {
    }

    #[verifier::external_body]
    pub proof fn SetNotEmpty<T>(s:Set<T>)
        requires exists |x:T| s.contains(x),
        ensures s.len()>0
    {
    }

    /// If S maps injectively into a finite set T via f, then S is finite
    /// and |S| <= |T|.
    pub proof fn lemma_injective_preimage_finite<S, T>(
        s: Set<S>, f: spec_fn(S) -> T, t: Set<T>,
    )
        requires
            t.finite(),
            forall |x: S| s.contains(x) ==> t.contains(#[trigger] f(x)),
            forall |x1: S, x2: S| #![trigger f(x1), f(x2)]
                s.contains(x1) && s.contains(x2) && f(x1) == f(x2) ==> x1 == x2,
        ensures
            s.finite(),
            s.len() <= t.len(),
        decreases t.len(),
    {
        broadcast use vstd::set::group_set_axioms;

        if t.len() == 0 {
            vstd::set_lib::lemma_set_empty_equivalency_len(t);
            assert(s =~= Set::<S>::empty()) by {
                assert forall |x: S| !s.contains(x) by {
                    if s.contains(x) {
                        assert(t.contains(f(x)));
                    }
                };
            };
        } else {
            let y = t.choose();
            let t_minus = t.remove(y);
            if exists |x: S| s.contains(x) && f(x) == y {
                let x = choose |x: S| s.contains(x) && f(x) == y;
                let s_minus = s.remove(x);
                // s_minus maps injectively into t_minus
                assert forall |x2: S| s_minus.contains(x2) implies t_minus.contains(#[trigger] f(x2)) by {
                    assert(s.contains(x2));
                    assert(t.contains(f(x2)));
                    // f(x2) != y because x2 != x (x2 in s.remove(x)) and f is injective on s
                    if f(x2) == y {
                        // Then f(x2) == f(x) == y, and s.contains(x2) && s.contains(x)
                        // By injectivity: x2 == x. But x2 in s.remove(x) means x2 != x. Contradiction.
                    }
                };
                lemma_injective_preimage_finite(s_minus, f, t_minus);
                // s_minus.finite() by IH, so s = s_minus.insert(x) is finite
            } else {
                // No element of s maps to y, so s maps into t_minus
                assert forall |x: S| s.contains(x) implies t_minus.contains(#[trigger] f(x)) by {
                    assert(t.contains(f(x)));
                    assert(f(x) != y);
                };
                lemma_injective_preimage_finite(s, f, t_minus);
            }
        }
    }

    pub proof fn lemma_MapSetCardinalityOver<X, Y>(xs: Set<X>, ys: Set<Y>, f: spec_fn(X) -> Y)
        requires
            InjectiveOver(xs, ys, f),
            forall |x: X| xs.contains(x) ==> ys.contains(f(x)),
            forall |y: Y| ys.contains(y) ==> exists |x: X| xs.contains(x) && y == f(x),
            xs.finite(),
        ensures
            xs.len() == ys.len(),
        decreases xs.len(),
    {
        broadcast use vstd::set::group_set_axioms;

        // Derive ys.finite(): ys ⊆ xs.map(f) and xs.map(f) is finite
        assert(ys.subset_of(xs.map(f))) by {
            assert forall |y: Y| ys.contains(y) implies xs.map(f).contains(y) by {
                let x = choose |x: X| xs.contains(x) && y == f(x);
            };
        };
        xs.lemma_map_finite(f);
        vstd::set_lib::lemma_len_subset(ys, xs.map(f));
        // ys is now known to be finite

        if xs.len() == 0 {
            // xs is empty
            vstd::set_lib::lemma_set_empty_equivalency_len(xs);
            // No x in xs, so no y in ys has a preimage — ys is empty
            assert(ys =~= Set::<Y>::empty()) by {
                assert forall |y: Y| !ys.contains(y) by {
                    if ys.contains(y) {
                        let x = choose |x: X| xs.contains(x) && y == f(x);
                    }
                };
            };
        } else {
            let x = xs.choose();
            let xs_prime = xs.remove(x);
            let ys_prime = ys.remove(f(x));

            // Precondition 1: InjectiveOver(xs_prime, ys_prime, f)
            // Follows from InjectiveOver(xs, ys, f) since xs_prime ⊆ xs and ys_prime ⊆ ys

            // Precondition 2: forward image
            assert forall |x2: X| xs_prime.contains(x2)
                implies ys_prime.contains(f(x2)) by
            {
                assert(xs.contains(x2));
                assert(ys.contains(f(x2)));
                // f(x2) != f(x) by injectivity (x2 != x since x2 in xs.remove(x))
                if f(x2) == f(x) {
                    // InjectiveOver: xs.contains(x2) && xs.contains(x) && ys.contains(f(x2)) && ys.contains(f(x)) && f(x2)==f(x) ==> x2==x
                    assert(ys.contains(f(x)));
                }
            };

            // Precondition 3: backward surjection
            assert forall |y: Y| ys_prime.contains(y)
                implies exists |x2: X| xs_prime.contains(x2) && y == f(x2) by
            {
                assert(ys.contains(y));
                let x2 = choose |x2: X| xs.contains(x2) && y == f(x2);
                // x2 != x because y != f(x) (y in ys.remove(f(x)))
                assert(x2 != x); // if x2 == x then y == f(x), but y in ys_prime = ys.remove(f(x))
                assert(xs_prime.contains(x2));
            };

            // xs_prime.finite() from remove
            lemma_MapSetCardinalityOver(xs_prime, ys_prime, f);
            // xs_prime.len() == ys_prime.len()
            // xs.len() == xs_prime.len() + 1 (axiom_set_remove_len)
            // ys.len() == ys_prime.len() + 1 (axiom_set_remove_len, ys.contains(f(x)))
            assert(ys.contains(f(x)));
        }
    }

    pub proof fn subset_cardinality<T>(x:Set<T>, y:Set<T>)
        requires
            x.subset_of(y),
            y.finite(),
        ensures x.len() <= y.len()
    {
        vstd::set_lib::lemma_len_subset(x, y);
    }

    pub proof fn InsertCardinality<T>(s:Set<T>, x:T)
        requires
            s.finite(),
            forall |y:T| s.contains(y) ==> y != x,
        ensures s.insert(x).len() == s.len() + 1
    {
        broadcast use vstd::set::group_set_axioms;
        // forall y in s: y != x. Instantiate with y = x: s.contains(x) ==> x != x.
        // Since x == x, we get !s.contains(x).
        assert(!s.contains(x));
        // axiom_set_insert_len (in group_set_axioms): s.insert(x).len() == s.len() + 1
    }

    pub proof fn subset_len_equal_implies_equal<T>(s1: Set<T>, s2: Set<T>)
    requires
        s1.subset_of(s2),
        s1.len() == s2.len(),
        s2.finite(),
    ensures
        s1 == s2
    {
        broadcast use vstd::set::group_set_axioms;
        if s1 != s2 {
            // s1 ⊆ s2 and s1 ≠ s2 ⟹ ∃x ∈ s2 \ s1
            assert(exists |x: T| s2.contains(x) && !s1.contains(x)) by {
                if forall |x: T| s2.contains(x) ==> s1.contains(x) {
                    assert(s1 =~= s2);
                }
            };
            let x = choose |x: T| s2.contains(x) && !s1.contains(x);
            // s1 ⊆ s2.remove(x) since all of s1 is in s2 and x ∉ s1
            assert(s1.subset_of(s2.remove(x))) by {
                assert forall |y: T| s1.contains(y) implies s2.remove(x).contains(y) by {
                    assert(s2.contains(y));  // from s1 ⊆ s2
                    assert(y != x);          // x ∉ s1 but y ∈ s1
                };
            };
            vstd::set_lib::lemma_len_subset(s1, s2.remove(x));
            // s1.len() <= s2.remove(x).len() == s2.len() - 1 < s2.len() == s1.len()
            assert(false);
        }
    }

    /// Pigeonhole principle for finite sets:
    /// If two subsets of a universe U each have size > |U|/2,
    /// then they must intersect.
    ///
    /// Formally: if A ⊆ U, B ⊆ U, |A| + |B| > |U|,
    /// then there exists w in both A and B.
    ///
    /// This is the key lemma for quorum intersection arguments
    /// in consensus protocols (Raft, Paxos).
    pub proof fn lemma_quorum_intersection<T>(a: Set<T>, b: Set<T>, u: Set<T>)
        requires
            a.subset_of(u),
            b.subset_of(u),
            a.len() + b.len() > u.len(),
            u.finite(),
        ensures
            exists |w: T| a.contains(w) && b.contains(w),
    {
        // a and b are finite (subsets of finite u)
        vstd::set_lib::lemma_len_subset(a, u);
        vstd::set_lib::lemma_len_subset(b, u);

        // a ∪ b ⊆ u
        assert((a + b).subset_of(u)) by {
            assert forall |x: T| (a + b).contains(x) implies u.contains(x) by {};
        };

        // |a ∪ b| ≤ |u| and a ∪ b is finite
        vstd::set_lib::lemma_len_subset(a + b, u);

        // Inclusion-exclusion: |a ∪ b| + |a ∩ b| = |a| + |b|
        vstd::set_lib::lemma_set_intersect_union_lens(a, b);

        // So |a ∩ b| = |a| + |b| - |a ∪ b| ≥ |a| + |b| - |u| > 0

        // a ∩ b is finite (subset of a)
        assert(a.intersect(b).subset_of(a)) by {
            assert forall |x: T| a.intersect(b).contains(x) implies a.contains(x) by {};
        };
        vstd::set_lib::lemma_len_subset(a.intersect(b), a);

        // a ∩ b is non-empty since its length > 0
        vstd::set_lib::lemma_set_empty_equivalency_len(a.intersect(b));

        // Extract witness: w ∈ a ∩ b means w ∈ a and w ∈ b
        let w = choose |w: T| a.intersect(b).contains(w);
    }

}
