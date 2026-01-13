
    // fn test2(m:HashSet<u32>) -> (res:bool)
    //     ensures 
    //         res == (forall |i: u32| m@.contains(i) ==> i < 10)
    // {
    //     let mut result = true;
    //     let ghost mut seen: Set<u32> = Set::empty();
    //     let m_iter = m.iter();
    //     let ghost mut count: int = 0;
    //     assume(m_iter@.0 == 0);
    //     assert(count == m_iter@.0);
    //     // assume(m_iter@.1.len() == m@.len());

    //     for k in iter: m_iter
    //         invariant
    //             forall |x: u32| seen.contains(x) ==> m@.contains(x),
    //             seen.subset_of(m@),
    //             forall |x: u32| seen.contains(x) ==> x < 10,
    //             // count == m_iter@.0,
    //             // count <= m_iter@.1.len(),
    //             // count <= m@.len(),
    //             result ==> count == seen.len(),
    //             !result ==> !(forall |x:u32| m@.contains(x) ==> x < 10),
    //         // decreases m@.len() - count
    //     {
    //         proof{
    //             if result {
    //                 count == seen.len();
    //             }
    //         }
    //         let ghost old_seen = seen;
    //         let ghost old_count = count;
    //         proof{
    //             if result {
    //                 old_count == old_seen.len();
    //             }
    //         }
    //         proof{count = count + 1;}
    //         if *k < 10 {
    //             proof { 
    //                 if result {
    //                     assume(forall |x:u32| seen.contains(x) ==> x != *k);
    //                     InsertCardinality(seen, *k);
    //                     seen = seen.insert(*k);
    //                     assert(count == old_count + 1);
    //                     assert(seen.len() == old_seen.len() + 1);
    //                     assert(old_count + 1 == old_seen.len() + 1);
    //                     assert(seen.contains(*k));
    //                     assume(m@.contains(*k));
    //                     assert( count == seen.len());
    //                 }
    //             }
    //         }
    //         else 
    //         {
    //             assume(m@.contains(*k));
    //             result = false;
    //             assert(exists |x:u32| m@.contains(x) && x >= 10);
    //             assert(!(forall |x:u32| m@.contains(x) ==> x < 10));
    //         }
    //     }
    //     proof {
    //             assert(forall |x:u32| seen.contains(x) ==> x < 10);
    //             assert(forall |x:u32| seen.contains(x) ==> m@.contains(x));
    //             assert(seen.subset_of(m@));
    //             assume(count == m@.len());
    //             if result {
    //                 assert(seen.len() == m@.len());
    //                 assert(seen.len() == m@.len());
    //                 Self::test3(seen, m);
    //                 assert(forall |i: u32| m@.contains(i) ==> i < 10);
    //             }
    //             else {
    //                 !(forall |x:u32| m@.contains(x) ==> x < 10);
    //             }
    //         }
    //     result
    // }


    // proof fn test3(s1:Set<u32>, s2:HashSet<u32>) 
    //     requires 
    //         s1.len() == s2@.len(),
    //         s1.subset_of(s2@),
    //         forall |x:u32| s1.contains(x) ==> s2@.contains(x),
    //         forall |x:u32| s1.contains(x) ==> x < 10,
    //     ensures
    //         forall |x:u32| s2@.contains(x) ==> x < 10,
    // {
    //     // assume(forall |x:u32| s2@.contains(x) ==> s1.contains(x));
    //     assert forall |x: u32| s2@.contains(x) ==> s1.contains(x) by {
    //         assume(s2@.contains(x));
    //         if (!s1.contains(x)) {
    //             let s2_minus = s2@.remove(x);
    //             assume(s2_minus.len() == s2@.len() - 1);
    //             assert(s2_minus.len() < s2@.len());
    //             assert(s1.subset_of(s2_minus));
    //             subset_cardinality(s1, s2_minus);
    //             assert(s1.len() <= s2_minus.len());
    //             assert(s1.len() == s2@.len());
    //             assert(false);
    //         }
    //     };
    //     assert(s1 == s2@);

    //     // assert()
    // }
