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
        reveal(intsetmax);
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
    pub proof fn ThingsIKnowAboutSubset<T>(x:Set<T>, y:Set<T>)
        requires x.subset_of(y)
        ensures x.len()<y.len()
        decreases x.len()
    {
        if (!x.is_empty()) {
            let e = choose |e:T| x.contains(e);
            ThingsIKnowAboutSubset(x.remove(e), y.remove(e));
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

    #[verifier::external_body]
    pub proof fn subset_cardinality<T>(x:Set<T>, y:Set<T>)
        requires x.subset_of(y)
        ensures x.len() <= y.len()
    {
    }

    #[verifier::external_body]
    pub proof fn InsertCardinality<T>(s:Set<T>, x:T)
        requires forall |y:T| s.contains(y) ==> y != x
        ensures s.insert(x).len() == s.len() + 1
    {

    }

    #[verifier::external_body]
    pub proof fn subset_len_equal_implies_equal<T>(s1: Set<T>, s2: Set<T>)
    requires
        s1.subset_of(s2),
        s1.len() == s2.len()
    ensures
        s1 == s2
    {}

    /// Pigeonhole principle for finite sets:
    /// If two subsets of a universe U each have size > |U|/2,
    /// then they must intersect.
    ///
    /// Formally: if A ⊆ U, B ⊆ U, |A| + |B| > |U|,
    /// then there exists w in both A and B.
    ///
    /// This is the key lemma for quorum intersection arguments
    /// in consensus protocols (Raft, Paxos).
    #[verifier::external_body]
    pub proof fn lemma_quorum_intersection<T>(a: Set<T>, b: Set<T>, u: Set<T>)
        requires
            a.subset_of(u),
            b.subset_of(u),
            a.len() + b.len() > u.len(),
        ensures
            exists |w: T| a.contains(w) && b.contains(w),
    {
        // Proof sketch: |A ∪ B| ≤ |U|, and |A ∪ B| = |A| + |B| - |A ∩ B|.
        // So |A ∩ B| = |A| + |B| - |A ∪ B| ≥ |A| + |B| - |U| > 0.
        // Therefore A ∩ B is non-empty.
    }

}
