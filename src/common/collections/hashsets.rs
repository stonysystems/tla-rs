use crate::common::collections::comparable::*;
use std::collections::*;
use std::hash::Hash;
use vstd::prelude::*;
use vstd::std_specs::hash::*;
use vstd::view::*;
verus! {
    /// Extension trait providing well_formed for HashSet
    /// For HashSet, well_formed is always true since it's a standard library type
    pub trait HashSetWellFormed {
        spec fn well_formed(&self) -> bool;
    }

    impl<T> HashSetWellFormed for HashSet<T> {
        #[verifier(inline)]
        open spec fn well_formed(&self) -> bool {
            true
        }
    }
    #[verifier(external_body)]
    pub fn union_sets<T>(s1:&HashSet<T>, s2:&HashSet<T>) -> (res:HashSet<T>)
    where
        T: Clone + Eq + Hash
    ensures
        res@ == s1@.union(s2@),
    {
        let mut result = HashSet::new();
        for elem in s1 {
            result.insert(elem.clone());
        }
        for elem in s2 {
            result.insert(elem.clone());
        }
        result
    }

    #[verifier(external_body)]
    pub fn clone_hashset<T>(s:&HashSet<T>) -> (res:HashSet<T>)
    where
            T: Clone + Eq + Hash
    ensures
        res@ == s@,
    {
        let mut res = HashSet::new();
        for elem in s {
            res.insert(elem.clone());
        }
        res
    }

    #[verifier(external_body)]
    pub fn hashset_to_vec<T>(s:&HashSet<T>) -> (res:Vec<T>)
    where
            T: Clone + Eq + Hash
    {
        s.iter().cloned().collect()
    }
}
