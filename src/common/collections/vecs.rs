use crate::common::collections::comparable::*;
use builtin::*;
use builtin_macros::*;
use std::collections::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::view::*;

verus! {

    #[verifier(external_body)]
    pub fn update_vec_at<T>(v: &Vec<T>, idx: usize, val: T) -> (res: Vec<T>)
        where T: Clone + vstd::view::View<V = T>
        requires
            idx < v.len(),
        ensures
            res@.len() == v@.len(),
            res@ == v@.update(idx as int, val@),
            forall |i: int| 0 <= i < res@.len() ==> res@[i] == (if i == idx as int { val@ } else { v[i]@ }),
    {
        let mut res = Vec::new();
        let mut i = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                res.len() == i,
                forall |j: int| 0 <= j < i ==> res@[j] == (if j == idx as int { val@ } else { v[j]@ }),
        {
            if i == idx {
                res.push(val.clone());
            } else {
                res.push(v[i].clone());
            }
            i += 1;
        }
        res
    }



    #[verifier(external_body)]
    pub fn contains<T>(v: &Vec<T>, item:&T) -> (found: bool)
        where T: PartialEq + Clone + vstd::view::View
        // where T: Comparable + Clone,
        // requires
        //     v.len() > 0,
        ensures
            found == v@.contains(*item),
            found == v@.map(|i, t:T| t@).contains(item@),
    {
        let mut i = 0;
        assert(v@.len() == v.len() as int);
        while i < v.len()
            invariant
                0 <= i,
                i <= v.len(),
                forall |j: int| 0 <= j < i ==> v@[j] != item,
        {
            // if v[i].equals(&item) {
            if v[i] == *item {
                return true;
            }
            i += 1;
        }
        false
    }

    #[verifier(external_body)]
    pub fn contains_u64(v: &Vec<u64>, item:&u64) -> (found: bool)
        ensures
            found == v@.contains(*item),
            found == v@.map(|i, t:u64| t as int).contains(item as int),
    {
        let mut i = 0;
        assert(v@.len() == v.len() as int);
        while i < v.len()
            invariant
                0 <= i,
                i <= v.len(),
                forall |j: int| 0 <= j < i ==> v@[j] != item,
        {
            // if v[i].equals(&item) {
            if v[i] == *item {
                return true;
            }
            i += 1;
        }
        false
    }

    #[verifier(external_body)]
    pub fn truncate_vec<T>(v: &Vec<T>, start: usize, end: usize) -> (result: Vec<T>)
        where T: Clone + vstd::view::View,
        requires
            start <= end,
            end <= v.len(),
        ensures
            result.len() == end - start,
            result@ == v@.subrange(start as int, end as int),
            result@.map(|i, t:T| t@) == v@.map(|i, t:T| t@).subrange(start as int, end as int),
    {
        let mut new_vec = Vec::new();
        let mut i = start;
        assert(end <= v.len());
        assert(new_vec@ == v@.subrange(start as int, i as int));
        while i < end
            invariant
                start <= i,
                i <= end,
                end <= v.len(),
                new_vec.len() == i - start,
                new_vec@ == v@.subrange(start as int, i as int),
        {
            assert(end <= v.len());
            let ghost j = i;
            let ghost old_v = new_vec;
            assert(old_v@ == v@.subrange(start as int, j as int));
            let entry = v[i].clone();
            // assert(v[i as int].clone() == v[i as int]);
            assert(v@.len() == v.len() as int);
            assert(0 <= i && i < v.len());
            assert(v[i as int] == v@[i as int]);
            assume(entry == v[i as int]);
            assert(entry == v@[i as int]);
            new_vec.push(entry);
            assert(new_vec@.last() == v@[i as int]);
            assert(new_vec@ == old_v@ + seq![v@[i as int]]);
            i = i + 1;
            assert(new_vec@ == v@.subrange(start as int, i as int));
        }
        new_vec
    }

    #[verifier(external_body)]
    pub fn truncate_vecu64(v: &Vec<u64>, start: usize, end: usize) -> (result: Vec<u64>)
        // where T: Clone + vstd::view::View,
        requires
            start <= end,
            end <= v.len(),
        ensures
            result.len() == end - start,
            result@ == v@.subrange(start as int, end as int),
            result@.map(|i, t:u64| t as int) == v@.map(|i, t:u64| t as int).subrange(start as int, end as int),
    {
        let mut new_vec = Vec::new();
        let mut i = start;
        assert(end <= v.len());
        assert(new_vec@ == v@.subrange(start as int, i as int));
        while i < end
            invariant
                start <= i,
                i <= end,
                end <= v.len(),
                new_vec.len() == i - start,
                new_vec@ == v@.subrange(start as int, i as int),
        {
            assert(end <= v.len());
            let ghost j = i;
            let ghost old_v = new_vec;
            assert(old_v@ == v@.subrange(start as int, j as int));
            let entry = v[i].clone();
            // assert(v[i as int].clone() == v[i as int]);
            assert(v@.len() == v.len() as int);
            assert(0 <= i && i < v.len());
            assert(v[i as int] == v@[i as int]);
            assume(entry == v[i as int]);
            assert(entry == v@[i as int]);
            new_vec.push(entry);
            assert(new_vec@.last() == v@[i as int]);
            assert(new_vec@ == old_v@ + seq![v@[i as int]]);
            i = i + 1;
            assert(new_vec@ == v@.subrange(start as int, i as int));
        }
        new_vec
    }

    // #[verifier(external_body)]
    // pub fn concat_vecs<T>(v1: Vec<T>, v2: Vec<T>) -> (result: Vec<T>)
    //     where T: Clone + vstd::view::View,
    //     ensures
    //         result@ == v1@ + v2@,
    //         result@.len() == v1@.len() + v2@.len(),
    //         result@.map(|i, t:T| t@).len() == v1@.map(|i, t:T| t@).len() + v2@.map(|i, t:T| t@).len()
    // {
    //     let mut result = Vec::new();
    //     let mut i = 0;

    //     assert(result@ == v1@.subrange(0, i as int));
    //     while i < v1.len()
    //         invariant
    //             0 <= i <= v1@.len(),
    //             result@ == v1@.subrange(0, i as int),
    //     {
    //         let entry = v1[i].clone();
    //         assume(entry == v1[i as int]);
    //         result.push(entry);
    //         i = i + 1;
    //         assert(result@ == v1@.subrange(0, i as int));
    //     }

    //     i = 0;
    //     assert(result@ == v1@ + v2@.subrange(0, i as int));
    //     while i < v2.len()
    //         invariant
    //             0 <= i <= v2@.len(),
    //             result@ == v1@ + v2@.subrange(0, i as int),
    //     {
    //         let entry = v2[i].clone();
    //         assume(entry == v2[i as int]);
    //         result.push(entry);
    //         i = i + 1;
    //         assert(result@ == v1@ + v2@.subrange(0, i as int));
    //     }

    //     assert(result@ == v1@ + v2@);

    //     result
    // }

    #[verifier(external_body)]
    pub fn concat_vecs<T>(v1: &Vec<T>, v2: &Vec<T>) -> (result: Vec<T>)
        where T: Clone + vstd::view::View,
        ensures
            result@ == v1@ + v2@,
            result@.len() == v1@.len() + v2@.len(),
            result@.map(|i, t:T| t@).len() == v1@.map(|i, t:T| t@).len() + v2@.map(|i, t:T| t@).len()
    {
        let mut result = Vec::new();
        let mut i = 0;

        assert(result@ == v1@.subrange(0, i as int));
        while i < v1.len()
            invariant
                0 <= i <= v1@.len(),
                result@ == v1@.subrange(0, i as int),
        {
            let entry = v1[i].clone();
            assume(entry == v1[i as int]);
            result.push(entry);
            i = i + 1;
            assert(result@ == v1@.subrange(0, i as int));
        }

        i = 0;
        assert(result@ == v1@ + v2@.subrange(0, i as int));
        while i < v2.len()
            invariant
                0 <= i <= v2@.len(),
                result@ == v1@ + v2@.subrange(0, i as int),
        {
            let entry = v2[i].clone();
            assume(entry == v2[i as int]);
            result.push(entry);
            i = i + 1;
            assert(result@ == v1@ + v2@.subrange(0, i as int));
        }

        assert(result@ == v1@ + v2@);

        result
    }

}
