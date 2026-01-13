use builtin::*;
use builtin_macros::*;
use vstd::seq::*;
use vstd::set::*;

verus!{
    // pub proof fn ThingsIKnowAboutSubset<T>(x:Set<T>, y:Set<T>)
    //     requires x.subset_of(y)
    //     ensures x.len()<y.len()
    // {
    //     if (!x.is_empty()) {
    //         let e = choose |e:T| x.contains(e);
    //         ThingsIKnowAboutSubset(x.remove(e), y.remove(e));
    //     }
    // }

    // pub proof fn SubsetCardinality<T>(x:Set<T>, y:Set<T>)
    //     ensures x.subset_of(y) ==> x.len() < y.len(),
    //             (x.subset_of(y) || x==y) ==> x.len() <= y.len()
    // {
    //     if (x.subset_of(y)) {

    //     } 
    //     if (x==y) {

    //     }
    // }
}