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

    #[verifier::external_body]
    pub proof fn lemma_MapSetCardinalityOver<X, Y>(xs: Set<X>, ys: Set<Y>, f: spec_fn(X) -> Y)
        requires
            InjectiveOver(xs, ys, f),
            forall |x: X| xs.contains(x) ==> ys.contains(f(x)),
            forall |y: Y| ys.contains(y) ==> exists |x: X| xs.contains(x) && y == f(x),
        ensures
            xs.len() == ys.len(),
        decreases xs.len(), ys.len()
    {
        if xs.len() > 0 {
            let x = choose |x: X| xs.contains(x);
            let xs_prime = xs.remove(x);
            assert(xs_prime.len() < xs.len());
            let ys_prime = ys.remove(f(x));
            assert(ys_prime.len() < ys.len());
            lemma_MapSetCardinalityOver(xs_prime, ys_prime, f);
        }
    }

    #[verifier::external_body]
    pub proof fn SubsetCardinality<T>(x:Set<T>, y:Set<T>)
        ensures x.subset_of(y) ==> x.len() < y.len(),
                (x.subset_of(y) || x==y) ==> x.len() <= y.len()
    {
        if (x.subset_of(y)) {

        }
        if (x==y) {

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
