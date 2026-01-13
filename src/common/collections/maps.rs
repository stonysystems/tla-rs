#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::set_lib::lemma_set_properties;
use vstd::{modes::*, prelude::*, seq::*, *};

verus! {
    proof fn eq_map<A, B>(x:Map<A, B>, y:Map<A, B>) -> (ret: bool)
        requires x.dom().finite(), y.dom().finite()
        ensures ret ==> x =~= y
    {
      &&& (forall |a: A| x.contains_key(a) <==> y.contains_key(a))
      &&& (forall |a: A| #![trigger x[a], y[a]] x.contains_key(a) ==> x[a] == y[a])
    }

    pub open spec fn domain<U, V>(m: Map<U,V>) -> Set<U>
        recommends m.dom().finite()
    {
        m.dom()
    }

    pub proof fn predicate_domain<U, V>(m: Map<U,V>)
        requires m.dom().finite()
        ensures forall |i: U| domain(m).contains(i) <==> m.contains_key(i),
    {}

    pub open spec fn union<U, V>(m: Map<U,V>, m_: Map<U,V>) -> Map<U,V>
        recommends domain(m).disjoint(domain(m_)), m.dom().finite(), m_.dom().finite(),
     {
        Map::new(|i: U| domain(m).union(domain(m_)).contains(i),
                 |i: U| if m.contains_key(i) { m[i] } else {m_[i]})
    }

    pub proof fn predicate_union<U, V>(m: Map<U,V>, m_: Map<U,V>)
        requires domain(m).disjoint(domain(m_)),
                m.dom().finite(),
                m_.dom().finite(),
        ensures
            forall |i: U| union(m, m_).contains_key(i) <==> #[trigger] m.contains_key(i) || #[trigger] m_.contains_key(i),
            forall |i: U| m.contains_key(i) ==> union(m, m_)[i] == #[trigger] m[i],
            forall |i: U| m_.contains_key(i) ==> union(m, m_)[i] == #[trigger] m_[i],
    {}

    pub proof fn lemma_non_empty_map_has_elements<S,T>(m:Map<S,T>)
        requires m.len() > 0,
                 m.dom().finite(),
        ensures exists |x: S| m.contains_key(x)
        {
            predicate_domain(m);
            let dom = domain(m);
            let empty_map:Map<S,T> = Map::empty();
            assert(m.dom().disjoint(empty_map.dom()));
            assert(!(m.dom() =~= empty_map.dom()));
            assert(dom.len() > 0);
        }

    pub proof fn lemma_MapSizeIsDomainSize<S,T>(dom:Set<S>, m:Map<S,T>)
        requires dom =~= domain(m),
                    dom.finite(),
                    m.dom().finite(),
        ensures m.len() == dom.len()
        decreases m.len(), dom.len()
    {
            if m.len() == 0 {
              assert(dom.len() == 0);
            } else {
              lemma_non_empty_map_has_elements(m);
              let x: S = choose|i: S| m.contains_key(i);
              assert(m.contains_key(x));
              assert(dom.contains(x));

              let m_: Map<S, T> = m.remove(x);
              let dom_ = dom.remove(x);

              lemma_MapSizeIsDomainSize(dom_, m_);

              assert(dom_.len() == m_.len());
              assert(m == m_.insert(x, m[x]));
              assert(m.len() == m_.len() + 1);
              assert(dom.len() == dom_.len() + 1);
        }
    }

    pub proof fn lemma_maps_decrease<S,T>(before: Map<S,T>, after: Map<S,T>, item_removed:S)
      requires before.contains_key(item_removed),
               after =~= Map::new(|s: S| before.contains_key(s) && s != item_removed, |s: S| before[s]),
               before.dom().finite(),
               after.dom().finite(),
      ensures  after.len() < before.len()
    {
      assert(!(after.contains_key(item_removed)));
      assert(forall |i: S| after.contains_key(i) ==> before.contains_key(i));

      predicate_domain(before);
      predicate_domain(after);
      let domain_before = domain(before);
      let domain_after  = domain(after);

      lemma_MapSizeIsDomainSize(domain_before, before);
      lemma_MapSizeIsDomainSize(domain_after, after);
      lemma_set_properties::<S>();

      if after.len() == before.len() {
        if domain_before =~= domain_after {
          assert(!(domain_after.contains(item_removed)));
          assert(false);
        } else {
          assert(domain_after.len() == domain_before.len());
          let diff = domain_after - domain_before;
          assert(forall |i: S| after.contains_key(i) ==> before.contains_key(i));
          assert(diff.len() == 0);
          let diff2 = domain_before.difference(domain_after);
          assert(diff2.contains(item_removed));
          assert(diff2.len() >= 1);
          assert(false);
        }
      } else if after.len() > before.len() {
        //var extra :| extra in domain_after && !(extra in domain_before);
        let diff = domain_after.difference(domain_before);
        assert(domain_after.len() > domain_before.len());
        if diff.len() == 0 {
          assert(diff.len() == domain_after.len() - (domain_after*domain_before).len());
          assert((domain_after*domain_before).len() <= domain_before.len());
          assert(domain_after.len() == (domain_after*domain_before).len());
          assert(domain_after.len() <= domain_before.len());
          assert(false);
        } else {
          assert(diff.len() >= 1);
          let diff_item = choose |i: S| diff.contains(i);
          assert(domain_after.contains(diff_item));
          assert(!(domain_before.contains(diff_item)));
          assert(false);
        }
        assert(false);
      }
    }

  pub proof fn lemma_map_remove_one<S,T>(before:Map<S,T>, after:Map<S,T>, item_removed:S)
  requires
          before.dom().finite(), after.dom().finite(),
          before.contains_key(item_removed),
           after =~= Map::new(|s: S| before.contains_key(s) && s != item_removed, |s: S| before[s]),
  ensures after.len() + 1 == before.len()
{
  lemma_maps_decrease(before, after, item_removed);
  let domain_before = domain(before);
  let domain_after  = domain(after);
  lemma_MapSizeIsDomainSize(domain_before, before);
  lemma_MapSizeIsDomainSize(domain_after, after);
  lemma_set_properties::<S>();
  assert(domain_after + set![item_removed] == domain_before);
}

pub open spec fn RemoveElt<U,V>(m:Map<U,V>, elt:U) -> Map<U,V>
  recommends m.contains_key(elt), m.dom().finite()
  decreases m.len()
{
  m.remove(elt)
}

pub proof fn lemma_RemoveElt<U, V>(m: Map<U, V>, elt: U)
  requires m.contains_key(elt), m.dom().finite()
  ensures RemoveElt(m, elt).len() == m.len() - 1,
  !(RemoveElt(m, elt).contains_key(elt)),
   forall |elt_:U| #![auto] RemoveElt(m, elt).contains_key(elt_) <==> m.contains_key(elt_) && elt_ != elt,
{
  let m_ = m.remove(elt);
  lemma_map_remove_one(m, m_, elt);
}
} // verus!
