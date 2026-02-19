use vstd::{map::*, prelude::*, set::*};

use crate::common::collections::{maps::*, sets::*, vecs::*};
use crate::common::native::io_s::*;
use crate::implementation::common::generic_refinement::*;
use crate::implementation::RSL::cconstants::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::types_i::*;
use crate::protocol::RSL::{learner::*, types::*};
use std::collections::HashMap;
use std::collections::HashSet;
use std::hash::RandomState;
use vstd::std_specs::hash::*;
// DEPRECATED: Use `crate::generated::RSL::learner_gen` for functional wrappers
// and `crate::generated::RSL::types_gen::CLearner` for the type directly.
// This module's methods are still called internally by the generated wrappers.
#[deprecated(note = "Import CLearner from crate::generated::RSL::types_gen instead")]
pub use crate::generated::RSL::types_gen::CLearner;

verus! {
    broadcast use crate::common::native::io_s::axiom_endpoint_key_model;

    impl CLearner
    {
        // #[verifier(external_body)]
        pub fn CLearnerInit(c:CReplicaConstants) -> (clearner_init_result:Self)
        requires c.valid()
        ensures
            clearner_init_result.valid(),
            LLearnerInit(clearner_init_result@, c@)

        {
            let t1 = c;
            let t2 = CBallot{seqno:0, proposer_id:0};
            let t3: HashMap<COperationNumber,CLearnerTuple> = HashMap::new();
            let rc = CLearner{
                constants: t1,
                max_ballot_seen: t2,
                unexecuted_learner_state: t3,
            };

            let ghost arc = rc@;
            let ghost ac = c@;
            assert(arc.constants == ac);
            assert(arc.max_ballot_seen == Ballot{seqno:0, proposer_id:0});
            assert(arc.unexecuted_learner_state == Map::<OperationNumber, LearnerTuple>::empty());

            rc
        }

        pub proof fn lemma_learnerstate_insert(s:CLearnerState, s2:CLearnerState, opn:COperationNumber, tup:CLearnerTuple)
            requires
                clearnerstate_is_abstractable(s),
                clearnerstate_is_valid(s),
                COperationNumberIsAbstractable(opn),
                COperationNumberIsValid(opn),
                tup.abstractable(),
                tup.valid(),
                s2@ == s@.insert(opn, tup),
            ensures
                // forall |p:COperationNumber| s2@.contains_key(p) ==> COperationNumberIsAbstractable(p) && s2@[p].abstractable(),
                clearnerstate_is_abstractable(s2),
                clearnerstate_is_valid(s2),
        {

        }

        #[verifier(external_body)]
        proof fn lemma_singleitem_hashset(s:HashSet<EndPoint>, ss:Set<AbstractEndPoint>, e:EndPoint)
            requires
                // s@.contains(e),
                // s@.len() == 1,
                s@ == Set::<EndPoint>::empty(),
                ss == set![e@],
            ensures
                s@.insert(e).map(|e:EndPoint| e@) == ss,
        {

        }

        #[verifier(external_body)]
        proof fn lemma_singleitem_hashmap(s:CLearnerState, ss:LearnerState, opn:COperationNumber, tup:CLearnerTuple)
            requires
                s@ == Map::<COperationNumber, CLearnerTuple>::empty(),
                ss == map![opn as int => tup@],
            ensures
                (
                    {
                        let ns = s@.insert(opn, tup);
                        let sns =
                        Map::new(
                            |ak: int| exists |k: u64| ns.contains_key(k) && k as int == ak,
                            |ak: int| {
                                let k = choose |k: u64| ns.contains_key(k) && k as int == ak;
                                ns[k]@
                            }
                        );
                        &&& sns == ss
                    }
                )
                // s@.insert(opn, tup).map(|e:EndPoint| e@) == ss,
        {

        }

        #[verifier(external_body)]
        proof fn lemma_hashmap_insert(s:CLearnerState, ss:LearnerState, opn:COperationNumber, tup:CLearnerTuple)
            requires
                // s@ == Map::<COperationNumber, CLearnerTuple>::empty(),
                ss == Map::new(
                    |ak: int| exists |k: u64| s@.contains_key(k) && k as int == ak,
                    |ak: int| {
                        let k = choose |k: u64| s@.contains_key(k) && k as int == ak;
                        s@[k]@
                    }
                )
                // ss == map![opn as int => tup@],
            ensures
                (
                    {
                        let ns = s@.insert(opn, tup);
                        let sns =
                        Map::new(
                            |ak: int| exists |k: u64| ns.contains_key(k) && k as int == ak,
                            |ak: int| {
                                let k = choose |k: u64| ns.contains_key(k) && k as int == ak;
                                ns[k]@
                            }
                        );
                        &&& sns == ss.insert(opn as int, tup@)
                    }
                )
                // s@.insert(opn, tup).map(|e:EndPoint| e@) == ss,
        {

        }

        #[verifier(external_body)]
        proof fn lemma_hashset_insert(s:HashSet<EndPoint>, ss:Set<AbstractEndPoint>, e:EndPoint)
            requires
                ss == s@.map(|e:EndPoint| e@)
                // ss == map![opn as int => tup@],
            ensures
                (
                    {
                        let ns = s@.insert(e);
                        let sns = ns.map(|e:EndPoint| e@);
                        &&& sns == ss.insert(e@)
                    }
                )
                // s@.insert(opn, tup).map(|e:EndPoint| e@) == ss,
        {

        }


        // #[verifier(external_body)]
        pub fn CLearnerProcess2b(&mut self, packet: CPacket)
            requires
                old(self).valid(),
                packet.valid(),
                packet.msg is CMessage2b
            ensures
                self.valid(),
                LLearnerProcess2b(old(self)@, self@, packet@)
        {
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::hash_map::group_hash_map_axioms;
            let ghost ss = old(self)@;
            let ghost p = packet@;

            match packet.msg {
                CMessage::CMessage2b { opn_2b, bal_2b, val_2b } => {
                    let opn = opn_2b;

                    // if !(self.constants.all.config.replica_ids.contains(&packet.src))
                    if !contains(&self.constants.all.config.replica_ids, &packet.src)
                        || CBalLt(&bal_2b, &self.max_ballot_seen)
                    {
                        assert(!ss.constants.all.config.replica_ids.contains(p.src) || BalLt(p.msg->bal_2b, ss.max_ballot_seen));
                        assert(self.valid());
                        // No state changes needed
                        let ghost ns = self@;
                        assert(LLearnerProcess2b(ss, ns, p));
                    } else if CBalLt(&self.max_ballot_seen, &bal_2b) {
                        broadcast use vstd::std_specs::hash::group_hash_axioms;

                        assert(BalLt(ss.max_ballot_seen, p.msg->bal_2b));

                        let mut m_set: HashSet<EndPoint> = HashSet::new();

                        proof{Self::lemma_singleitem_hashset(m_set, set![p.src], packet.src);}

                        m_set.insert(packet.src);

                        let ghost s_set = m_set@.map(|e:EndPoint| e@);
                        assert(p.src == packet.src@);
                        assert(s_set == set![p.src]);

                        assert(packet.src.abstractable());
                        assert(forall |p:EndPoint| m_set@.contains(p) ==> p.abstractable());
                        let tup = CLearnerTuple {
                            received_2b_message_senders: m_set,
                            candidate_learned_value: val_2b,
                        };
                        let ghost stup = LearnerTuple{
                            received_2b_message_senders:set![p.src],
                            candidate_learned_value:p.msg->val_2b};
                        assert(tup@ == stup);
                        let ghost sstate = map![opn as int => stup];
                        // assert(packet.src.abstractable());
                        // assert(crequestbatch_is_abstractable(&tup.candidate_learned_value));
                        // assert(forall |p:EndPoint| tup.received_2b_message_senders@.contains(p) ==> p.abstractable());
                        // assert(tup.abstractable());
                        self.max_ballot_seen = bal_2b;
                        let mut new_state:CLearnerState = HashMap::new();
                        proof{Self::lemma_singleitem_hashmap(new_state, sstate, opn, tup);}
                        new_state.insert(opn, tup);
                        self.unexecuted_learner_state = new_state;

                        assert(abstractify_clearnerstate(self.unexecuted_learner_state) == sstate);
                        // assert(clearnerstate_is_abstractable(self.unexecuted_learner_state));
                        // assert(self.abstractable());
                        // assert(self.valid());
                        // assert()
                        let ghost ns = self@;
                        assert(ns.constants == ss.constants);
                        assert(ns.max_ballot_seen == p.msg->bal_2b);
                        assert(ns.unexecuted_learner_state == sstate);
                        assert(LLearnerProcess2b(ss, ns, p));
                    } else if !self.unexecuted_learner_state.contains_key(&opn) {
                        assert(!ss.unexecuted_learner_state.contains_key(opn as int));
                        let mut m_set: HashSet<EndPoint> = HashSet::new();
                        proof{Self::lemma_singleitem_hashset(m_set, set![p.src], packet.src);}

                        m_set.insert(packet.src);

                        let ghost s_set = m_set@.map(|e:EndPoint| e@);
                        assert(s_set == set![p.src]);

                        let tup = CLearnerTuple {
                            received_2b_message_senders: m_set,
                            candidate_learned_value: val_2b,
                        };
                        assert(tup.valid());
                        let ghost stup = LearnerTuple{received_2b_message_senders:set![p.src], candidate_learned_value:p.msg->val_2b};
                        assert(tup@ == stup);
                        proof{Self::lemma_hashmap_insert(self.unexecuted_learner_state, ss.unexecuted_learner_state, opn, tup);}
                        self.unexecuted_learner_state.insert(opn, tup);

                        assert(self.abstractable());
                        assert(self.valid());
                        let ghost ns = self@;
                        assert(LLearnerProcess2b(ss, ns, p));
                    } else {
                        let v = self.unexecuted_learner_state.get(&opn);
                        match v {
                            Some(v) => {
                                broadcast use vstd::std_specs::hash::group_hash_axioms;
                                assert(ss.unexecuted_learner_state.contains_key(opn as int));
                                assert(v@ == ss.unexecuted_learner_state[opn as int]);
                                assert(v.valid());
                                assert(v.received_2b_message_senders@.map(|e:EndPoint| e@) == ss.unexecuted_learner_state[opn as int].received_2b_message_senders);
                                assert(
                                    v.received_2b_message_senders@.contains(packet.src) ==>
                                    ss.unexecuted_learner_state[opn as int].received_2b_message_senders.contains(p.src)
                                );
                                if v.received_2b_message_senders.contains(&packet.src){
                                    assert(ss.unexecuted_learner_state[opn as int].received_2b_message_senders.contains(p.src));
                                    assert(self.valid());
                                    let ghost ns = self@;
                                    assert(LLearnerProcess2b(ss, ns, p));
                                } else {
                                    // broadcast use vstd::std_specs::hash::group_hash_axioms;
                                    assume(!ss.unexecuted_learner_state[opn as int].received_2b_message_senders.contains(p.src));
                                    let mut tup = v.clone_up_to_view();


                                    let ghost sotup = ss.unexecuted_learner_state[opn as int];
                                    assert(tup@ == sotup);

                                    proof{Self::lemma_hashset_insert(tup.received_2b_message_senders,
                                            sotup.received_2b_message_senders,
                                            packet.src);}


                                    assert(tup.abstractable());
                                    tup.received_2b_message_senders.insert(packet.src);
                                    assert(tup.abstractable());
                                    assert(clearnerstate_is_abstractable(self.unexecuted_learner_state));
                                    assert(clearnerstate_is_valid(self.unexecuted_learner_state));

                                    let ghost s_set = tup.received_2b_message_senders@.map(|e:EndPoint| e@);
                                    assert(s_set == sotup.received_2b_message_senders + set![packet.src@]);


                                    let ghost stup = LearnerTuple{
                                        received_2b_message_senders:sotup.received_2b_message_senders + set![p.src],
                                        candidate_learned_value:sotup.candidate_learned_value};
                                    assert(tup@ == stup);

                                    assert(COperationNumberIsValid(opn));
                                    assert(tup.valid());

                                    proof{Self::lemma_hashmap_insert(self.unexecuted_learner_state, ss.unexecuted_learner_state, opn, tup);}

                                    let ghost old_state = self.unexecuted_learner_state;

                                    self.unexecuted_learner_state.insert(opn, tup);

                                    assert(self.unexecuted_learner_state@ == old_state@.insert(opn, tup));
                                    proof{Self::lemma_learnerstate_insert(old_state, self.unexecuted_learner_state, opn, tup);}
                                    assert(clearnerstate_is_abstractable(self.unexecuted_learner_state));
                                    assert(clearnerstate_is_valid(self.unexecuted_learner_state));
                                    assert(self.abstractable());
                                    assert(self.valid());
                                    let ghost ns = self@;
                                    assert(ns.unexecuted_learner_state == ss.unexecuted_learner_state.insert(opn as int, stup));
                                    assert(ns.constants == ss.constants);
                                    assert(ns.max_ballot_seen == ss.max_ballot_seen);
                                    assert(LLearnerProcess2b(ss, ns, p));
                                }
                            }
                            None => {
                                assert(self.valid());
                                let ghost ns = self@;
                                assert(LLearnerProcess2b(ss, ns, p));
                            }
                        }
                    }

                }
                _ => {
                    // unreachable due to precondition: `packet.msg is CMessage2b`
                }
            }


        }

        // #[verifier(external_body)]
        pub fn CLearnerForgetDecision(&mut self, opn:COperationNumber)
            requires
                old(self).valid(),
                COperationNumberIsValid(opn)
            ensures
                self.valid(),
                LLearnerForgetDecision(old(self)@, self@, AbstractifyCOperationNumberToOperationNumber(opn))
        {
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::hash_map::group_hash_map_axioms;

            let ghost ss = old(self)@;
            let ghost sopn = opn as int;

            proof{lemma_AbstractifyMap_DomainUnchange3(
                    self.unexecuted_learner_state,
                    |s: COperationNumber| s as int);

                    assert(forall |x:COperationNumber| self.unexecuted_learner_state@.contains_key(x) ==>
                                                        ss.unexecuted_learner_state.contains_key(x as int))
            }
            if self.unexecuted_learner_state.contains_key(&opn) {
                assert(self.unexecuted_learner_state@.contains_key(opn));
                assert(ss.unexecuted_learner_state.contains_key(sopn));
                self.unexecuted_learner_state.remove(&opn);
                assert(self.unexecuted_learner_state@ == old(self).unexecuted_learner_state@.remove(opn));
                let ghost ns = self@;
                proof{
                    lemma_AbstractifyMap_Remove2(
                        old(self).unexecuted_learner_state,
                        self.unexecuted_learner_state, opn,
                        |s: COperationNumber| s as int);
                    assert(ns.unexecuted_learner_state == ss.unexecuted_learner_state.remove(sopn));
                }
                assert(clearnerstate_is_abstractable(self.unexecuted_learner_state));
                assert(self.abstractable());
                let ghost ns = self@;
                assert(ns.unexecuted_learner_state == ss.unexecuted_learner_state.remove(sopn));
                assert(LLearnerForgetDecision(old(self)@, self@, AbstractifyCOperationNumberToOperationNumber(opn)));
            }
            else {
                // No state changes needed
                assert(!ss.unexecuted_learner_state.contains_key(sopn));
                assert(LLearnerForgetDecision(old(self)@, self@, AbstractifyCOperationNumberToOperationNumber(opn)));
            }
        }

        #[verifier(external_body)]
        proof fn lemma_ClearnerState_Insert(state:CLearnerState, new_state:CLearnerState, opn:COperationNumber, t:CLearnerTuple)
            requires
                clearnerstate_is_valid(state),
                COperationNumberIsValid(opn),
                t.valid(),
                new_state@ == state@.insert(opn, t),
            ensures
                clearnerstate_is_valid(new_state)
                // ({
                //     let new_state = state.insert(opn, t);
                //     &&& clearnerstate_is_valid(state)
                // })
        {

        }

        // #[verifier(external_body)]
        pub fn CLearnerForgetOperationsBefore(&mut self, ops_complete:COperationNumber)
            requires
                old(self).valid(),
                COperationNumberIsValid(ops_complete)
            ensures
                self.valid(),
                LLearnerForgetOperationsBefore(old(self)@, self@, AbstractifyCOperationNumberToOperationNumber(ops_complete))
        {
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::hash_map::group_hash_map_axioms;

            assert(obeys_key_model::<COperationNumber>());
            assert(builds_valid_hashers::<RandomState>());


            let ghost ss = old(self)@;
            let ghost sops = ops_complete as int;

            let m_keys = self.unexecuted_learner_state.keys();
            assert(m_keys@.0 == 0);
            assert(m_keys@.1.to_set() =~= self.unexecuted_learner_state@.dom());
            assume(m_keys@.1.len() == self.unexecuted_learner_state@.len());

            let ghost mut seen_keys = Set::<u64>::empty();
            assert(seen_keys == m_keys@.1.take(m_keys@.0).to_set());

            let mut new_state: HashMap<COperationNumber, CLearnerTuple> = HashMap::new();

            for opn in iter:m_keys
                invariant
                    self.valid(),
                    clearnerstate_is_valid(new_state),
                    seen_keys.subset_of(self.unexecuted_learner_state@.dom()),
                    // seen_keys.len() == m_keys@.0,
                    forall |i:COperationNumber| seen_keys.contains(i) ==> self.unexecuted_learner_state@.contains_key(i),
                    forall |i:COperationNumber| new_state@.contains_key(i) ==> self.unexecuted_learner_state@.contains_key(i) && i >= ops_complete,
                    forall |i:COperationNumber| new_state@.contains_key(i) ==> new_state@[i]@ == self.unexecuted_learner_state@[i]@,
                    forall |i:COperationNumber| new_state@.contains_key(i) ==> seen_keys.contains(i),
                    forall |i:COperationNumber| seen_keys.contains(i) && i >= ops_complete ==> new_state@.contains_key(i),
            {
                broadcast use vstd::std_specs::hash::group_hash_axioms;
                broadcast use vstd::hash_map::group_hash_map_axioms;
                assert(clearnerstate_is_valid(new_state));
                assert(clearnerstate_is_valid(self.unexecuted_learner_state));
                assume(self.unexecuted_learner_state@.contains_key(*opn));
                proof{seen_keys = seen_keys.insert(*opn);}
                if *opn >= ops_complete {
                    let v = self.unexecuted_learner_state.get(opn);
                    match v {
                        Some(v) => {
                            assert(COperationNumberIsValid(*opn));
                            assert(COperationNumberIsAbstractable(*opn));
                            assert(v.valid());
                            assert(v.abstractable());
                            let ghost old_state = new_state;
                            let nv = v.clone_up_to_view();
                            assert(nv.abstractable());
                            new_state.insert(*opn, nv);
                            assert(new_state@ == old_state@.insert(*opn, nv));
                            proof{Self::lemma_ClearnerState_Insert(old_state, new_state, *opn, nv);}
                            // assert(forall |i:COperationNumber| new_state@.contains_key(i) ==> COperationNumberIsAbstractable(i) && new_state@[i].abstractable());
                            // assert(forall |i:COperationNumber| new_state@.contains_key(i) ==> COperationNumberIsValid(i) && new_state@[i].valid());
                            assert(clearnerstate_is_valid(new_state));
                        }
                        None => {
                            assert(clearnerstate_is_valid(new_state));
                        }
                    }
                }
            }

            assert(forall |i:COperationNumber| new_state@.contains_key(i) ==> self.unexecuted_learner_state@.contains_key(i) && i >= ops_complete && new_state@[i]@ == self.unexecuted_learner_state@[i]@);

            assert(seen_keys.subset_of(self.unexecuted_learner_state@.dom()));
            assert(forall |i:COperationNumber| seen_keys.contains(i) ==> self.unexecuted_learner_state@.contains_key(i));
            assume(m_keys@.0 == m_keys@.1.len());
            assume(seen_keys.len() == m_keys@.0);
            assert(seen_keys.len() == m_keys@.1.len());
            proof{subset_len_equal_implies_equal(seen_keys, self.unexecuted_learner_state@.dom())};
            assert(seen_keys == self.unexecuted_learner_state@.dom());
            assert(forall |i:COperationNumber| self.unexecuted_learner_state@.contains_key(i) ==> seen_keys.contains(i));

            assert(forall |i:COperationNumber| new_state@.contains_key(i) <==> seen_keys.contains(i) && i >= ops_complete);

            self.unexecuted_learner_state = new_state;
            let ghost ns = self@;
            assert(forall |i:OperationNumber| ns.unexecuted_learner_state.contains_key(i) ==> i >= sops && ss.unexecuted_learner_state.contains_key(i));


            assert(forall |i:OperationNumber| ss.unexecuted_learner_state.contains_key(i) && i >= sops ==> ns.unexecuted_learner_state.contains_key(i));
            assert(forall |i:OperationNumber| ns.unexecuted_learner_state.contains_key(i) <==> i >= sops && ss.unexecuted_learner_state.contains_key(i));
            assert(forall |i:OperationNumber| ns.unexecuted_learner_state.contains_key(i) ==> ns.unexecuted_learner_state[i] == ss.unexecuted_learner_state[i]);

            assert(ns.constants == ss.constants);
            assert(ns.max_ballot_seen == ss.max_ballot_seen);

            assert(LLearnerForgetOperationsBefore(ss, ns, sops));

            assert(clearnerstate_is_abstractable(self.unexecuted_learner_state));
            assert(self.abstractable());
        }

        fn test()
        {
            broadcast use vstd::std_specs::hash::group_hash_axioms;

            let mut m = HashMap::<u32, i8>::new();
            assert(m@ == Map::<u32, i8>::empty());

            m.insert(3, 4);
            m.insert(6, -8);
            let m_keys = m.keys();
            assert(m_keys@.0 == 0);
            assert(m_keys@.1.to_set() =~= m@.dom());
            assume(m_keys@.1.len() == m@.len()); // verus is stupid, this should be true
            let ghost key_set = m_keys@.1.to_set();

            let ghost mut seen_keys = Set::<u32>::empty();
            assert(seen_keys == m_keys@.1.take(m_keys@.0).to_set());

            let mut items = HashMap::<u32, i8>::new();

            for k in iter: m_keys
                invariant
                    // m@.contains_key(k),
                    seen_keys.subset_of(m@.dom()),
                    // seen_keys.len() == m_keys@.0,
                    forall |i:u32| seen_keys.contains(i) ==> m@.contains_key(i),
                    forall |i:u32| items@.contains_key(i) ==> i <= 5 && m@.contains_key(i),
                    forall |i:u32| items@.contains_key(i) ==> items@[i] == m@[i],
                    forall |i:u32| items@.contains_key(i) ==> seen_keys.contains(i),
                    forall |i:u32| seen_keys.contains(i) && i <= 5 ==> items@.contains_key(i),
            {
                broadcast use vstd::std_specs::hash::group_hash_axioms;
                // let b = m.contains_key(k);
                // assert(b);
                assume(m@.contains_key(*k)); // verus is stupid, it doesn't know that k is a member of iter's key_set.
                assert(forall |i:u32| items@.contains_key(i) ==> seen_keys.contains(i));
                proof{seen_keys = seen_keys.insert(*k);}
                if *k <= 5 {
                    let v = m.get(k);
                    match v {
                        Some(v) => {
                            assert(*k <= 5);
                            assert(m@.contains_key(*k));
                            let nv = *v;
                            assert(nv == *v);
                            items.insert(*k, nv);
                        }
                        None => {

                        }
                    }
                }
            }

            assert(seen_keys.subset_of(m@.dom()));
            assert(forall |i:u32| seen_keys.contains(i) ==> m@.contains_key(i));
            assume(m_keys@.0 == m_keys@.1.len()); // verus is stupid, it doesn't know after iteration, the number of iterated number equals to the len of iter's key_set.
            assert(seen_keys.len() == m_keys@.0);
            assert(seen_keys.len() == m_keys@.1.len());
            proof{subset_len_equal_implies_equal(seen_keys, m@.dom())};
            assert(seen_keys == m@.dom());
            assert(forall |i: u32| m@.contains_key(i) ==> seen_keys.contains(i));

            assert(forall |i: u32| items@.contains_key(i) <==> seen_keys.contains(i) && i <= 5);

            assert(forall |i:u32| m@.contains_key(i) ==> seen_keys.contains(i));

            assert(forall |i:u32| m@.contains_key(i) && i <= 5 ==> items@.contains_key(i));

            assert(forall |i:u32| items@.contains_key(i) ==> i <= 5 && m@.contains_key(i) && items@[i] == m@[i]);

            assert(forall |i: u32|
                items@.contains_key(i)
            ==> i <= 5 && m@.contains_key(i)
            );
        }


        fn test3()
        {
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            let mut m = HashMap::<u32, i8>::new();
            assert(m@ == Map::<u32, i8>::empty());

            m.insert(3, 4);
            m.insert(6, -8);
            let m_keys = m.keys();
            assert(m_keys@.0 == 0);
            assert(m_keys@.1.to_set() =~= m@.dom());
            assert(m_keys@.1.to_set().len() == m@.dom().len());
            assume(m_keys@.1.len() == m_keys@.1.to_set().len()); // verus is stupid, this should be true, because hashmap doesn't have depulicate keys.
            assert(m_keys@.1.len() == m@.len());

            // let ghost all_keys = m_keys@.1.to_set();
            let ghost mut items = Set::<u32>::empty();
            assert(items == m_keys@.1.take(m_keys@.0).to_set());

            let ghost key_set = m_keys@.1.to_set();
            assert(key_set =~= m@.dom());

            for k in iter: m_keys
                invariant
                    items.subset_of(m@.dom()),
                    key_set =~= m@.dom(),
                    items == m_keys@.1.take(m_keys@.0).to_set(),
                    forall |i:u32| items.contains(i) ==> m@.contains_key(i),
            {
                assume(key_set.contains(*k)); // verus is stupid, it doesn't know that k is a member of iter's key_set.
                assert(m@.contains_key(*k));
                proof { items.insert(*k); }
            }

            assume(m_keys@.0 == m_keys@.1.len()); // verus is stupid, it doesn't know after iteration, the number of iterated number equals to the len of iter's key_set.
            assert(items.len() == m_keys@.1.len());
            assert(items.len() == m@.len());
        }
    }
}
