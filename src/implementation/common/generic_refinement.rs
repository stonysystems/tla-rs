#![allow(unused_imports)]
use std::net;

use builtin::*;
use builtin_macros::*;
use std::collections::*;
use vstd::{modes::*, prelude::*, seq::*, *};
use vstd::view::*;

verus! {

    pub open spec fn AbstractifyU64(s:u64) -> int
    {
        s as int
    }

    pub open spec fn SeqIsAbstractable<CT>(s:Vec<CT>, AbstractableValue:spec_fn(CT) -> bool) -> bool
    {
        forall |i:int| 0 <= i < s.len() ==> AbstractableValue(s[i])
    }

    pub open spec fn SeqIsValid<CT>(s:Vec<CT>, ValidateValue:spec_fn(CT) -> bool, AbstractableValue:spec_fn(CT) -> bool) -> bool
    {
        forall |i:int| 0 <= i < s.len() ==> AbstractableValue(s[i]) && ValidateValue(s[i])
    }

    pub open spec fn AbstractifySeq<T, CT>(
        s: Vec<CT>,
        RefineValue: spec_fn(CT) -> T,
        AbstractableValue:spec_fn(CT) -> bool
    ) -> Seq<T>
        recommends SeqIsAbstractable(s, AbstractableValue)
        // decreases s.len()
    {
        s@.map(|i, ct:CT| RefineValue(ct))
    }


    pub proof fn lemma_AbstractifySeq_Ensures<T, CT>(s: Vec<CT>, RefineValue: spec_fn(CT) -> T, AbstractableValue:spec_fn(CT) -> bool)
        requires SeqIsAbstractable(s, AbstractableValue)
        ensures
        ({
            let cs = AbstractifySeq(s, RefineValue, AbstractableValue);
            &&& cs.len() == s.len()
            &&& (forall |i:int| 0 <= i < s.len() ==> cs[i] == RefineValue(s[i]))
            &&& (forall |i:T| cs.contains(i) ==> exists |x:int| 0 <= x < s.len() && i == RefineValue(s[x]))
            // &&& (forall |i:CT| #![trigger RefineValue(i)]cs.contains(RefineValue(i)) ==> exists |x:int| 0 <= x < s.len() && i == s[x])
        })
    {
    }

    #[verifier::external_body]
    pub proof fn lemma_AbstractifyVec_Concat<CT:vstd::view::View>(v1:Vec<CT>, v2:Vec<CT>, v3:Vec<CT>, p:spec_fn(CT) -> bool)
        requires
            // forall |x:CT| v1@.contains(x) ==> p(x),
            // forall |x:CT| v2@.contains(x) ==> p(x),
            forall |i:int| 0 <= i < v1@.len() ==> p(v1[i]),
            forall |i:int| 0 <= i < v2@.len() ==> p(v2[i]),
            v3@ == v1@ + v2@,
        ensures
            // forall |x:CT| v3@.contains(x) ==> p(x)
            forall |i:int| 0 <= i < v3@.len() ==> p(v3[i]),
    {

    }

    #[verifier::external_body]
    pub proof fn lemma_AbstractifyVec_Truncate<CT:vstd::view::View>(v1:Vec<CT>, v2:Vec<CT>, start:usize, end:usize, p:spec_fn(CT) -> bool)
        requires
            v2.len() == end - start,
            v2@ == v1@.subrange(start as int, end as int),
            v2@.map(|i, t:CT| t@) == v1@.map(|i, t:CT| t@).subrange(start as int, end as int),
            forall |i:int| 0 <= i < v1@.len() ==> p(v1[i]),
        ensures
            forall |i:int| 0 <= i < v2@.len() ==> p(v2[i]),
    {

    }


    pub open spec fn SetIsAbstractable<CT>(s:HashSet<CT>, AbstractableValue:spec_fn(CT) -> bool) -> bool
    {
        forall |x:CT| s@.contains(x) ==> AbstractableValue(x)
    }

    pub open spec fn SetIsValid<CT>(s:HashSet<CT>, ValidateValue:spec_fn(CT) -> bool, AbstractableValue:spec_fn(CT) -> bool) -> bool
    {
        forall |x:CT| s@.contains(x) ==> AbstractableValue(x) && ValidateValue(x)
    }

    pub open spec fn AbstractifySet<T, CT>(
        s: HashSet<CT>,
        RefineValue: spec_fn(CT) -> T,
        AbstractableValue:spec_fn(CT) -> bool
    ) -> Set<T>
        recommends SetIsAbstractable(s, AbstractableValue)
    {
        s@.map(|i:CT| RefineValue(i))
    }

    pub proof fn lemma_AbstractifySet_Ensuers<T, CT>(s: HashSet<CT>, RefineValue: spec_fn(CT) -> T, AbstractableValue:spec_fn(CT) -> bool)
        requires
            SetIsAbstractable(s, AbstractableValue),
            (forall |x:CT, y:CT| s@.contains(x) && s@.contains(y) && RefineValue(x) == RefineValue(y) ==> x == y)
        ensures
            ({
                let cs = AbstractifySet(s, RefineValue, AbstractableValue);
                &&& cs.len() == s.len()
                &&& (forall |i:CT| s@.contains(i) ==> cs.contains(RefineValue(i)))
                &&& (forall |y:T| cs.contains(y) <==> exists |x:CT| s@.contains(x) && y == RefineValue(x))
            })
    {
        let ss = s@.map(|i:CT| RefineValue(i));
        let cs = s@;
        lemma_AbstractifySet_SizeUnchange(s@, ss, RefineValue, AbstractableValue);
        assume(s.len() == s@.len());
        assert(cs.len() == ss.len());
    }

    #[verifier::external_body]
    pub proof fn lemma_AbstractifySet_SizeUnchange2<T:vstd::view::View>(s:HashSet<T>)
        ensures 
        ({
            let ss = s@.map(|i:T| i@);
            &&& s@.len() == ss.len()
            &&& s.len() == ss.len()
        })
    {

    }

    #[verifier::external_body]
    pub proof fn lemma_SetViewSizeUnchange<CT:vstd::view::View>(s:Set<CT>, ss:Set<CT::V>)
        requires
            forall |x:CT| s.contains(x) ==> ss.contains(x@),
            // forall |x:CT::V| ss.contains(x) ==> exists |y:CT| s.contains(y) &&  x == y@,
        ensures
            ss.len() == s.len()
    {

    }

    // pub proof fn lemma_SetViewSizeUnchange<CT:vstd::view::View>(s:Set<CT>, ss:Set<CT::V>)
    //     requires
    //         ss == s.map(|x:CT| x@)
    //     ensures
    //         ss.len() == s.len()
    // {

    // }

    #[verifier::external_body]
    pub proof fn lemma_AbstractifySet_SizeUnchange<T, CT>(s:Set<CT>, ss:Set<T>, RefineValue: spec_fn(CT) -> T, AbstractableValue:spec_fn(CT) -> bool)
        requires
            (forall |x:CT| s.contains(x) ==> AbstractableValue(x)),
            (forall |x:CT, y:CT| s.contains(x) && s.contains(y) && RefineValue(x) == RefineValue(y) ==> x == y),
            (forall |i:CT| s.contains(i) ==> ss.contains(RefineValue(i))),
            (forall |y:T| ss.contains(y) <==> exists |x:CT| s.contains(x) && y == RefineValue(x)),
        ensures
            s.len() == ss.len(),
        decreases s.len()
    {
        if s.len() > 0 {
            assume(exists |x:CT| s.contains(x));
            let x = choose |x:CT| s.contains(x);
            assert(s.contains(x));
            let s_ = s.remove(x);
            let ss_ = ss.remove(RefineValue(x));
            // assert(s_.len() == s.len() - 1);

            assert(s.contains(x));
            assert(!s_.contains(x));
            assert forall |y:CT| s_.contains(y) implies s.contains(y) && y != x by {
                assert(s.contains(y));
                assert(y != x);
            };
            assert forall |y:CT| s.contains(y) && y != x implies s_.contains(y) by {
                assert(s_.contains(y));
            };
            assert(s_.len() == s.len() - 1);

            assert(ss_.len() == ss.len() - 1);
            lemma_AbstractifySet_SizeUnchange(s_, ss_, RefineValue, AbstractableValue);
            assert(s.len() == ss.len());
        }
    }

    // pub proof fn lemma_AbstractifySet_Insert1<T, CT>(s1:Set<CT>, s2:Set<CT>, e:CT, Refine:spec_fn(CT) -> T)
    //     requires 

    // pub proof fn lemma_HashSetView_SizeUnchange<CT: std::cmp::Eq + std::hash::Hash>(s:HashSet<CT>, ss:Set<CT>)
    //     requires
    //         ss == s@,
    //     ensures
    //         s.len() == ss.len()
    // {
    //     assert forall |x:CT| s.contains(x) <==> ss.contains(x) by {
    //         assert(ss.contains(x) == s@.contains(x));
    //     };
    // }



    pub open spec fn MapIsAbstractable<CKT, CVT, KT, VT>(
        m:HashMap<CKT, CVT>,
        RefineKey: spec_fn(CKT) -> KT,
        AbstractableKey:spec_fn(CKT) -> bool,
        RefineValue: spec_fn(CVT) -> VT,
        AbstractableValue:spec_fn(CVT) -> bool,
        ReverseKey: spec_fn(KT) -> CKT,
    ) -> bool
    {
        &&& (forall |ck:CKT| m@.contains_key(ck) ==> AbstractableKey(ck) && AbstractableValue(m@[ck]))
        &&& (forall |ck:CKT| m@.contains_key(ck) ==> ReverseKey(RefineKey(ck)) == ck)
    }

    pub open spec fn MapIsValid<CKT, CVT, KT, VT>(
        m:HashMap<CKT, CVT>,
        RefineKey: spec_fn(CKT) -> KT,
        AbstractableKey:spec_fn(CKT) -> bool,
        ValidateKey:spec_fn(CKT) -> bool,
        RefineValue: spec_fn(CVT) -> VT,
        AbstractableValue:spec_fn(CVT) -> bool,
        ValidateValue:spec_fn(CVT) -> bool,
        ReverseKey: spec_fn(KT) -> CKT,
    ) -> bool
    {
        &&& MapIsAbstractable(m, RefineKey, AbstractableKey, RefineValue, AbstractableValue, ReverseKey)
        &&& (forall |ck:CKT| m@.contains_key(ck) ==> ValidateKey(ck) && ValidateValue(m@[ck]))
    }

    pub open spec fn AbstractifyMap<CKT, CVT, KT, VT>(
        m:HashMap<CKT, CVT>,
        RefineKey: spec_fn(CKT) -> KT,
        AbstractableKey:spec_fn(CKT) -> bool,
        ValidateKey:spec_fn(CKT) -> bool,
        RefineValue: spec_fn(CVT) -> VT,
        AbstractableValue:spec_fn(CVT) -> bool,
        ValidateValue:spec_fn(CVT) -> bool,
        ReverseKey: spec_fn(KT) -> CKT,
    ) -> Map<KT, VT>
        recommends
            MapIsAbstractable(m, RefineKey, AbstractableKey, RefineValue, AbstractableValue, ReverseKey)
    {
        Map::new(
            |k:KT| exists |ck:CKT| m@.contains_key(ck) && RefineKey(ck) == k,
            |k:KT| {
                let ck = choose |ck:CKT| m@.contains_key(ck) && RefineKey(ck) == k;
                RefineValue(m@[ck])
            }
        )
    }

    pub proof fn lemma_AbstractifyMap_Ensuers<CKT, CVT, KT, VT>(
        m:HashMap<CKT, CVT>,
        RefineKey: spec_fn(CKT) -> KT,
        AbstractableKey:spec_fn(CKT) -> bool,
        ValidateKey:spec_fn(CKT) -> bool,
        RefineValue: spec_fn(CVT) -> VT,
        AbstractableValue:spec_fn(CVT) -> bool,
        ValidateValue:spec_fn(CVT) -> bool,
        ReverseKey: spec_fn(KT) -> CKT,
    )
        requires
            MapIsAbstractable(m, RefineKey, AbstractableKey, RefineValue, AbstractableValue, ReverseKey)
        ensures
            ({
                let rm = AbstractifyMap(m, RefineKey, AbstractableKey, ValidateKey, RefineValue, AbstractableValue, ValidateValue, ReverseKey);
                &&& (forall |ck:CKT| m@.contains_key(ck) ==> rm.contains_key(RefineKey(ck)))
                &&& (forall |ck:CKT| m@.contains_key(ck) ==> rm[RefineKey(ck)] == RefineValue(m@[ck]))
                &&& (forall |k:KT| rm.contains_key(k) ==> (exists |ck:CKT| m@.contains_key(ck) && RefineKey(ck) == k))
            })
    {

    }

    #[verifier::external_body]
    pub proof fn lemma_AbstractifyMap_DomainUnchange<KT:vstd::view::View, VT:vstd::view::View>(m:HashMap<KT, VT>)
        ensures
        ({
            let sm = Map::new(
                |k:KT::V| exists |ck:KT| m@.contains_key(ck) && ck@ == k,
                |k:KT::V| {
                    let ck = choose |ck:KT| m@.contains_key(ck) && ck@ == k;
                    m@[ck]@
                }
            );
            &&& forall |k:KT| m@.contains_key(k) ==> sm.contains_key(k@) && m@[k]@ == sm[k@]
            &&& forall |k:KT| !m@.contains_key(k) ==> !sm.contains_key(k@)
        })
    {

    }

    #[verifier::external_body]
    pub proof fn lemma_AbstractifyMap_DomainUnchange2<KT:vstd::view::View, VT, CVT>(m:HashMap<KT, CVT>, RefineValue: spec_fn(CVT) -> VT)
        ensures
        ({
            let sm = Map::new(
                |k:KT::V| exists |ck:KT| m@.contains_key(ck) && ck@ == k,
                |k:KT::V| {
                    let ck = choose |ck:KT| m@.contains_key(ck) && ck@ == k;
                    RefineValue(m@[ck])
                }
            );
            &&& forall |k:KT| m@.contains_key(k) ==> sm.contains_key(k@) && RefineValue(m@[k]) == sm[k@]
            &&& forall |k:KT| !m@.contains_key(k) ==> !sm.contains_key(k@)
        })
    {

    }

    #[verifier::external_body]
    pub proof fn lemma_AbstractifyMap_DomainUnchange3<KT, CKT, VT:vstd::view::View>(m:HashMap<CKT, VT>, RefineKey: spec_fn(CKT) -> KT)
        ensures
        ({
            let sm = Map::new(
                |sk:KT| exists |ck:CKT| m@.contains_key(ck) && RefineKey(ck) == sk,
                |sk:KT| {
                    let ck = choose |ck:CKT| m@.contains_key(ck) && RefineKey(ck) == sk;
                    m@[ck]@
                }
            );
            &&& forall |ck:CKT| m@.contains_key(ck) ==> sm.contains_key(RefineKey(ck)) && m@[ck]@ == sm[RefineKey(ck)]
            &&& forall |ck:CKT| !m@.contains_key(ck) ==> !sm.contains_key(RefineKey(ck))
        })
    {

    }

    #[verifier::external_body]
    pub proof fn lemma_AbstractifyMap_Insert<KT:vstd::view::View, VT:vstd::view::View>(old_m:HashMap<KT, VT>, new_m:HashMap<KT, VT>, k:KT, v:VT)
        requires
            new_m@ == old_m@.insert(k, v)
        ensures
        ({
            let s_old_m = Map::new(
                |k:KT::V| exists |ck:KT| old_m@.contains_key(ck) && ck@ == k,
                |k:KT::V| {
                    let ck = choose |ck:KT| old_m@.contains_key(ck) && ck@ == k;
                    old_m@[ck]@
                }
            );
            let s_new_m = Map::new(
                |k:KT::V| exists |ck:KT| new_m@.contains_key(ck) && ck@ == k,
                |k:KT::V| {
                    let ck = choose |ck:KT| new_m@.contains_key(ck) && ck@ == k;
                    new_m@[ck]@
                }
            ); 
            &&& s_new_m == s_old_m.insert(k@, v@)
        })
    {

    }

    // #[verifier::external_body]
    // pub proof fn lemma_AbstractifyMap_Remove<KT:vstd::view::View, VT:vstd::view::View>(old_m:HashMap<KT, VT>, new_m:HashMap<KT, VT>, k:KT, v:VT)
    //     requires
    //         new_m@ == old_m@.insert(k, v)
    //     ensures
    //     ({
    //         let s_old_m = Map::new(
    //             |k:KT::V| exists |ck:KT| old_m@.contains_key(ck) && ck@ == k,
    //             |k:KT::V| {
    //                 let ck = choose |ck:KT| old_m@.contains_key(ck) && ck@ == k;
    //                 old_m@[ck]@
    //             }
    //         );
    //         let s_new_m = Map::new(
    //             |k:KT::V| exists |ck:KT| new_m@.contains_key(ck) && ck@ == k,
    //             |k:KT::V| {
    //                 let ck = choose |ck:KT| new_m@.contains_key(ck) && ck@ == k;
    //                 new_m@[ck]@
    //             }
    //         ); 
    //         &&& s_new_m == s_old_m.insert(k@, v@)
    //     })
    // {

    // }

    #[verifier::external_body]
    pub proof fn lemma_AbstractifyMap_Insert2<KT:vstd::view::View, VT, CVT>(old_m:HashMap<KT, CVT>, new_m:HashMap<KT, CVT>, k:KT, v:CVT, RefineValue: spec_fn(CVT) -> VT)
        requires
            new_m@ == old_m@.insert(k, v)
        ensures
        ({
            let s_old_m = Map::new(
                |k:KT::V| exists |ck:KT| old_m@.contains_key(ck) && ck@ == k,
                |k:KT::V| {
                    let ck = choose |ck:KT| old_m@.contains_key(ck) && ck@ == k;
                    RefineValue(old_m@[ck])
                }
            );
            let s_new_m = Map::new(
                |k:KT::V| exists |ck:KT| new_m@.contains_key(ck) && ck@ == k,
                |k:KT::V| {
                    let ck = choose |ck:KT| new_m@.contains_key(ck) && ck@ == k;
                    RefineValue(new_m@[ck])
                }
            ); 
            &&& s_new_m == s_old_m.insert(k@, RefineValue(v))
        })
    {

    }

    // #[verifier::external_body]
    // pub proof fn lemma_AbstractifyMap_Insert2<KT, CKT, VT:vstd::view::View>(old_m:HashMap<CKT, VT>, new_m:HashMap<CKT, VT>, k:CKT, v:VT, RefineKey: spec_fn(CKT) -> KT)
    //     requires
    //         new_m@ == old_m@.insert(k, v)
    //     ensures
    //     ({
    //         let s_old_m = Map::new(
    //             |k:KT::V| exists |ck:KT| old_m@.contains_key(ck) && ck@ == k,
    //             |k:KT::V| {
    //                 let ck = choose |ck:KT| old_m@.contains_key(ck) && ck@ == k;
    //                 RefineValue(old_m@[ck])
    //             }
    //         );
    //         let s_new_m = Map::new(
    //             |k:KT::V| exists |ck:KT| new_m@.contains_key(ck) && ck@ == k,
    //             |k:KT::V| {
    //                 let ck = choose |ck:KT| new_m@.contains_key(ck) && ck@ == k;
    //                 RefineValue(new_m@[ck])
    //             }
    //         ); 
    //         &&& s_new_m == s_old_m.insert(k@, RefineValue(v))
    //     })
    // {

    // }

    #[verifier::external_body]
    pub proof fn lemma_AbstractifyMap_Remove2<KT, CKT, VT:vstd::view::View>(old_m:HashMap<CKT, VT>, new_m:HashMap<CKT, VT>, k:CKT, RefineKey: spec_fn(CKT) -> KT)
        requires
            new_m@ == old_m@.remove(k)
        ensures
        ({
            let s_old_m = Map::new(
                |sk:KT| exists |ck:CKT| old_m@.contains_key(ck) && RefineKey(ck) == sk,
                |sk:KT| {
                    let ck = choose |ck:CKT| old_m@.contains_key(ck) && RefineKey(ck) == sk;
                    old_m@[ck]@
                }
            );
            let s_new_m = Map::new(
                |sk:KT| exists |ck:CKT| new_m@.contains_key(ck) && RefineKey(ck) == sk,
                |sk:KT| {
                    let ck = choose |ck:CKT| new_m@.contains_key(ck) && RefineKey(ck) == sk;
                    new_m@[ck]@
                }
            ); 
            &&& s_new_m == s_old_m.remove(RefineKey(k))
        })
    {

    }
}
