use crate::common::collections::comparable::*;
use std::collections::*;
use std::hash::Hash;
use vstd::prelude::*;
use vstd::std_specs::hash::*;
use vstd::view::*;
verus! {
    #[verifier(external_body)]
    pub fn union_sets<T>(s1:&HashSet<T>, s2:&HashSet<T>) -> (res:HashSet<T>)
    where
        T: Clone + Eq + Hash
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
    {
        let mut res = HashSet::new();
        for elem in s {
            res.insert(elem.clone());
        }
        res
    }
}
