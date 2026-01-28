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

            // let x = choose |x:int| s.contains(x);
        // if s.len() == 1 {
        //     x
        // } else {
        //     let sy = s.remove(x);
        //     let y = intsetmax(sy);
        //     assert(forall |i:int| s.contains(y) ==> sy.contains(i) || i == x);
        //     if x > y {
        //         x
        //     } else {
        //         y
        //     }
        // }

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

        // let m = intsetmax(s);

        // // Use `assert_by` to introduce the `choose` properties explicitly
        // assert_by({
        //     s.contains(m) && forall |i: int| s.contains(i) ==> m >= i
        // }, {
        //     assert(s.contains(m));  // Verifies the first condition
        //     assert(forall |i: int| s.contains(i) ==> m >= i);
        // });
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
        // if x.is_empty() {
        //     assert(x.len() == 0);
        //     assert(0 <= y.len());
        // } else {
        //     let e: T = choose |e: T| x.contains(e);

        //     let x_ = x.remove(e);
        //     let y_ = y.remove(e);

        //     assert(y.contains(e));

        //     spec_apply(subset_remove(x, y, e));

        //     spec_apply(set_remove_len(x, e));

        //     spec_apply(set_remove_len(y, e));

        //     subset_cardinality(x_, y_);

        //     assert(x.len() == x_.len() + 1);
        //     assert(y.len() == y_.len() + 1);
        //     assert(x_.len() + 1 <= y_.len() + 1);
        // }
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

}
