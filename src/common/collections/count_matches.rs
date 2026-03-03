use vstd::prelude::*;
use vstd::{set::*, set_lib::*};

verus! {
    pub open spec fn CountMatchesInSeq<T>(s: Seq<T>, f: spec_fn(T) -> bool) -> nat
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            CountMatchesInSeq(s.subrange(1, s.len() as int), f) + if f(s.index(0)) { 1 as nat } else { 0 as nat }
        }
    }

    pub proof fn lemma_count_matches_le_len<T>(s: Seq<T>, f: spec_fn(T) -> bool)
        ensures CountMatchesInSeq(s, f) <= s.len()
        decreases s.len()
    {
        if s.len() > 0 {
            lemma_count_matches_le_len(s.subrange(1, s.len() as int), f);
        }
    }

    pub open spec fn IsNthHighestValueInSequence(v:int, s:Seq<int>, n:int) -> bool
    {
        &&& 0 < n <= s.len()
        &&& s.contains(v)
        &&& CountMatchesInSeq(s, |x:int| x > v) < n
        &&& CountMatchesInSeq(s, |x:int| x >= v) >= n
    }

    // =========================================================================
    // Helper: maximum element of a non-empty integer sequence
    // =========================================================================

    pub open spec fn seq_max(s: Seq<int>) -> int
        recommends s.len() > 0
        decreases s.len()
    {
        if s.len() <= 1 { s[0] }
        else {
            let rest_max = seq_max(s.subrange(1, s.len() as int));
            if s[0] > rest_max { s[0] } else { rest_max }
        }
    }

    pub proof fn lemma_seq_max_properties(s: Seq<int>)
        requires s.len() > 0
        ensures
            s.contains(seq_max(s)),
            forall |i: int| 0 <= i < s.len() ==> s[i] <= seq_max(s),
        decreases s.len()
    {
        if s.len() > 1 {
            let s_tail = s.subrange(1, s.len() as int);
            lemma_seq_max_properties(s_tail);
            // s_tail.contains(seq_max(s_tail)) and forall i in s_tail: s_tail[i] <= seq_max(s_tail)
            // seq_max(s) = max(s[0], seq_max(s_tail))
            // Need: s.contains(seq_max(s)) and forall i in s: s[i] <= seq_max(s)
            assert forall |i: int| 0 <= i < s.len() implies s[i] <= seq_max(s) by {
                if i == 0 {
                    // s[0] <= max(s[0], rest_max) trivially
                } else {
                    // s[i] == s_tail[i-1] <= seq_max(s_tail) <= seq_max(s)
                    assert(s[i] == s_tail[i - 1]);
                }
            };
            // s.contains(seq_max(s)):
            if s[0] > seq_max(s_tail) {
                // seq_max(s) = s[0], s.contains(s[0]) trivially
                assert(s[0] == s.index(0));
            } else {
                // seq_max(s) = seq_max(s_tail), s_tail.contains(seq_max(s_tail))
                // so exists j in s_tail with s_tail[j] == seq_max(s_tail)
                // then s[j+1] == s_tail[j] == seq_max(s_tail) = seq_max(s)
                let j = choose |j: int| 0 <= j < s_tail.len() && s_tail[j] == seq_max(s_tail);
                assert(s[j + 1] == seq_max(s));
            }
        }
    }

    // =========================================================================
    // Helper: filter out all occurrences of a value from a sequence
    // =========================================================================

    pub open spec fn filter_value(s: Seq<int>, v: int) -> Seq<int>
        decreases s.len()
    {
        if s.len() == 0 { Seq::<int>::empty() }
        else {
            let rest = filter_value(s.subrange(1, s.len() as int), v);
            if s[0] == v { rest } else { seq![s[0]] + rest }
        }
    }

    proof fn lemma_filter_value_len(s: Seq<int>, v: int)
        ensures filter_value(s, v).len() == s.len() - CountMatchesInSeq(s, |x: int| x == v)
        decreases s.len()
    {
        if s.len() > 0 {
            lemma_filter_value_len(s.subrange(1, s.len() as int), v);
        }
    }

    proof fn lemma_filter_value_contains(s: Seq<int>, v: int)
        ensures
            forall |x: int| x != v ==> (filter_value(s, v).contains(x) <==> s.contains(x)),
            forall |x: int| filter_value(s, v).contains(x) ==> x != v,
        decreases s.len()
    {
        if s.len() > 0 {
            let s_tail = s.subrange(1, s.len() as int);
            lemma_filter_value_contains(s_tail, v);
            let fv = filter_value(s, v);
            let fv_tail = filter_value(s_tail, v);
            if s[0] == v {
                assert(fv =~= fv_tail);
                // Second postcondition: fv contains no v
                assert forall |x: int| fv.contains(x) implies x != v by {
                    assert(fv_tail.contains(x)); // fv =~= fv_tail
                    // IH second postcondition applies to fv_tail
                };
                assert forall |x: int| x != v implies (fv.contains(x) <==> s.contains(x)) by {
                    // Forward: s.contains(x) ==> fv.contains(x)
                    if s.contains(x) {
                        let j = choose |j: int| 0 <= j < s.len() && s[j] == x;
                        assert(j > 0); // since s[0] == v != x
                        assert(s_tail[j - 1] == x);
                        assert(s_tail.contains(x));
                        // IH: s_tail.contains(x) ==> fv_tail.contains(x)
                        assert(fv_tail.contains(x));
                    }
                    // Backward: fv.contains(x) ==> s.contains(x)
                    if fv.contains(x) {
                        assert(fv_tail.contains(x)); // fv =~= fv_tail
                        // IH: fv_tail.contains(x) ==> s_tail.contains(x)
                        assert(s_tail.contains(x));
                        let k = choose |k: int| 0 <= k < s_tail.len() && s_tail[k] == x;
                        assert(0 <= k + 1 && k + 1 < s.len());
                        assert(s[k + 1] == x);
                        assert(s.contains(x));
                    }
                };
            } else {
                assert(fv =~= seq![s[0]] + fv_tail);
                // Second postcondition: fv contains no v
                assert forall |x: int| fv.contains(x) implies x != v by {
                    let j = choose |j: int| 0 <= j < fv.len() && fv[j] == x;
                    if j == 0 {
                        assert(x == s[0]);
                        // s[0] != v
                    } else {
                        assert(fv_tail[j - 1] == x);
                        assert(fv_tail.contains(x));
                        // IH: fv_tail.contains(x) ==> x != v
                    }
                };
                assert forall |x: int| x != v implies (fv.contains(x) <==> s.contains(x)) by {
                    // Forward: s.contains(x) ==> fv.contains(x)
                    if s.contains(x) {
                        let j = choose |j: int| 0 <= j < s.len() && s[j] == x;
                        if j == 0 {
                            assert(fv[0] == s[0]);
                        } else {
                            assert(s_tail[j - 1] == x);
                            assert(s_tail.contains(x));
                            assert(fv_tail.contains(x));
                            let k = choose |k: int| 0 <= k < fv_tail.len() && fv_tail[k] == x;
                            assert(fv[k + 1] == x);
                        }
                    }
                    // Backward: fv.contains(x) ==> s.contains(x)
                    if fv.contains(x) {
                        let j = choose |j: int| 0 <= j < fv.len() && fv[j] == x;
                        if j == 0 {
                            assert(x == s[0]);
                            assert(s[0] == s.index(0));
                        } else {
                            assert(fv_tail[j - 1] == x);
                            assert(fv_tail.contains(x));
                            assert(s_tail.contains(x));
                            let k = choose |k: int| 0 <= k < s_tail.len() && s_tail[k] == x;
                            assert(0 <= k + 1 && k + 1 < s.len());
                            assert(s[k + 1] == x);
                        }
                    }
                };
            }
        }
    }

    // =========================================================================
    // Key counting lemma: CountMatchesInSeq decomposes through filter_value
    // =========================================================================

    /// CountMatchesInSeq(s, f) = CountMatchesInSeq(filter_value(s, v), f) + CountMatchesInSeq(s, f_and_v)
    /// where f_and_v(x) <==> f(x) && x == v.
    /// Takes f_and_v as explicit parameter to avoid nested-lambda SMT issues.
    proof fn lemma_count_filter_value(s: Seq<int>, f: spec_fn(int) -> bool, f_and_v: spec_fn(int) -> bool, v: int)
        requires
            forall |x: int| #![trigger f_and_v(x)] #![trigger f(x)] f_and_v(x) <==> (f(x) && x == v),
        ensures
            CountMatchesInSeq(s, f) ==
                CountMatchesInSeq(filter_value(s, v), f) +
                CountMatchesInSeq(s, f_and_v)
        decreases s.len()
    {
        if s.len() > 0 {
            let s_tail = s.subrange(1, s.len() as int);
            lemma_count_filter_value(s_tail, f, f_and_v, v);
            let fv = filter_value(s, v);
            let fv_tail = filter_value(s_tail, v);

            if s[0] == v {
                assert(fv =~= fv_tail);
                // Instantiate requires quantifier with x = s[0]
                assert(f_and_v(s[0]) <==> (f(s[0]) && s[0] == v));
                assert(f_and_v(s[0]) <==> f(s[0]));
            } else {
                assert(fv =~= seq![s[0]] + fv_tail);
                assert(fv.subrange(1, fv.len() as int) =~= fv_tail);
                // Instantiate requires quantifier with x = s[0]
                assert(f_and_v(s[0]) <==> (f(s[0]) && s[0] == v));
                assert(!f_and_v(s[0]));
            }
        }
    }

    // =========================================================================
    // Main theorem: nth order statistic always exists
    // =========================================================================

    /// For any integer sequence with 0 < n < len, there exists an element v in s
    /// such that count(> v) < n and count(>= v) >= n.
    /// Proof by induction on s.len() using "remove max" strategy:
    /// If count_eq(s, max) >= n, max is the witness.
    /// Otherwise, filter out max, apply IH to get v' in filtered sequence,
    /// and translate counts back to original sequence.
    pub proof fn lemma_nth_highest_value_exists(s: Seq<int>, n: int)
    requires
        0 < n,
        n <= s.len(),
    ensures
        exists |v: int| s.contains(v)
            && CountMatchesInSeq(s, |x: int| x > v) < n
            && CountMatchesInSeq(s, |x: int| x >= v) >= n,
    decreases s.len()
    {
        lemma_seq_max_properties(s);
        let m = seq_max(s);
        let count_eq_m = CountMatchesInSeq(s, |x: int| x == m);

        // count_gt(s, m) == 0 since m is max
        // Prove this via decomposition: every element <= m, so no element > m
        lemma_count_matches_le_len(s, |x: int| x > m);
        assert(CountMatchesInSeq(s, |x: int| x > m) == 0) by {
            // By contradiction: if count > 0, there's some x > m in s
            if CountMatchesInSeq(s, |x: int| x > m) > 0 {
                lemma_count_positive_implies_witness(s, |x: int| x > m);
                let x = choose |x: int| s.contains(x) && x > m;
                let j = choose |j: int| 0 <= j < s.len() && s[j] == x;
                assert(s[j] <= m); // from seq_max_properties
                assert(false);
            }
        };

        // count_gte(s, m) >= count_eq(s, m) since x == m implies x >= m
        lemma_count_implies_count(s, |x: int| x == m, |x: int| x >= m);

        if count_eq_m >= n {
            // max is the witness: count_gt = 0 < n, count_gte >= count_eq >= n
            assert(s.contains(m));
            assert(CountMatchesInSeq(s, |x: int| x > m) < n);
            assert(CountMatchesInSeq(s, |x: int| x >= m) >= n);
        } else {
            // count_eq(s, m) < n, so we filter out all m's and recurse
            let s_filtered = filter_value(s, m);
            lemma_filter_value_len(s, m);
            let n_prime = (n - count_eq_m) as int;
            assert(0 < n_prime);

            // Prove count_eq_m > 0 (m is in s) for termination
            assert(s.contains(m));
            lemma_contains_implies_count_positive(s, |x: int| x == m);
            assert(count_eq_m > 0);
            assert(s_filtered.len() < s.len());

            assert(n_prime <= s_filtered.len()) by {
                assert(s_filtered.len() == s.len() - count_eq_m);
            };

            // Apply IH to filtered sequence
            lemma_nth_highest_value_exists(s_filtered, n_prime);

            let v_prime = choose |v: int| s_filtered.contains(v)
                && CountMatchesInSeq(s_filtered, |x: int| x > v) < n_prime
                && CountMatchesInSeq(s_filtered, |x: int| x >= v) >= n_prime;

            // v' is in s, v' != m, v' < m
            lemma_filter_value_contains(s, m);
            assert(v_prime != m);
            assert(s.contains(v_prime));
            assert(v_prime < m) by {
                let j = choose |j: int| 0 <= j < s.len() && s[j] == v_prime;
                assert(s[j] <= m);
            };

            // Decompose count_gt(s, v') using explicit combined predicates
            let f_gt = |x: int| x > v_prime;
            let f_gt_and_m = |x: int| (x > v_prime) && x == m;
            let f_eq_m = |x: int| x == m;

            // count_gt(s, v') = count_gt(filtered, v') + count(s, f_gt_and_m)
            lemma_count_filter_value(s, f_gt, f_gt_and_m, m);
            // f_gt_and_m <==> f_eq_m (since m > v')
            lemma_count_equiv(s, f_gt_and_m, f_eq_m);
            assert(CountMatchesInSeq(s, f_gt) ==
                CountMatchesInSeq(s_filtered, f_gt) + count_eq_m);
            assert(CountMatchesInSeq(s, f_gt) < n);

            // Decompose count_gte(s, v') similarly
            let f_gte = |x: int| x >= v_prime;
            let f_gte_and_m = |x: int| (x >= v_prime) && x == m;

            lemma_count_filter_value(s, f_gte, f_gte_and_m, m);
            lemma_count_equiv(s, f_gte_and_m, f_eq_m);
            assert(CountMatchesInSeq(s, f_gte) ==
                CountMatchesInSeq(s_filtered, f_gte) + count_eq_m);
            assert(CountMatchesInSeq(s, f_gte) >= n);
        }
    }

    // =========================================================================
    // Small helper lemmas used by the main proof
    // =========================================================================

    /// If count > 0, there exists a witness element satisfying f
    proof fn lemma_count_positive_implies_witness(s: Seq<int>, f: spec_fn(int) -> bool)
        requires CountMatchesInSeq(s, f) > 0
        ensures exists |x: int| s.contains(x) && f(x)
        decreases s.len()
    {
        if f(s[0]) {
            assert(s[0] == s.index(0));
            assert(s.contains(s[0]));
        } else {
            let s_tail = s.subrange(1, s.len() as int);
            lemma_count_positive_implies_witness(s_tail, f);
            let x = choose |x: int| s_tail.contains(x) && f(x);
            let j = choose |j: int| 0 <= j < s_tail.len() && s_tail[j] == x;
            assert(0 <= j + 1 && j + 1 < s.len());
            assert(s[j + 1] == x);
            assert(s.contains(x));
        }
    }

    /// If s contains an element satisfying f, the count is positive
    proof fn lemma_contains_implies_count_positive(s: Seq<int>, f: spec_fn(int) -> bool)
        requires exists |x: int| s.contains(x) && f(x)
        ensures CountMatchesInSeq(s, f) > 0
        decreases s.len()
    {
        let x = choose |x: int| s.contains(x) && f(x);
        let j = choose |j: int| 0 <= j < s.len() && s[j] == x;
        if j == 0 {
            // s[0] == x and f(x), so f(s[0]) is true
        } else {
            let s_tail = s.subrange(1, s.len() as int);
            assert(s_tail[j - 1] == x);
            assert(s_tail.contains(x));
            lemma_contains_implies_count_positive(s_tail, f);
        }
    }

    /// If f(x) ==> g(x) for all x, then CountMatchesInSeq(s, f) <= CountMatchesInSeq(s, g)
    proof fn lemma_count_implies_count(s: Seq<int>, f: spec_fn(int) -> bool, g: spec_fn(int) -> bool)
        requires forall |x: int| #![trigger f(x), g(x)] f(x) ==> g(x)
        ensures CountMatchesInSeq(s, f) <= CountMatchesInSeq(s, g)
        decreases s.len()
    {
        if s.len() > 0 {
            lemma_count_implies_count(s.subrange(1, s.len() as int), f, g);
        }
    }

    /// If f and g are equivalent, they produce the same count
    proof fn lemma_count_equiv(s: Seq<int>, f: spec_fn(int) -> bool, g: spec_fn(int) -> bool)
        requires forall |x: int| #![trigger f(x), g(x)] f(x) <==> g(x)
        ensures CountMatchesInSeq(s, f) == CountMatchesInSeq(s, g)
        decreases s.len()
    {
        if s.len() > 0 {
            lemma_count_equiv(s.subrange(1, s.len() as int), f, g);
        }
    }

}
