// Manual code for CLearnerForgetDecision, CLearnerProcess2b, and CLearnerForgetOperationsBefore.
// These functions have protocol-specific proofs too complex for auto-generation.
// They are injected into learner_gen.rs by the transpiler via manual_code config.

pub exec fn CLearnerForgetDecision(s: &CLearner, opn: &u64) -> (result: CLearner)
requires
    s.valid(),
ensures
    result.valid(),
    LLearnerForgetDecision(s@, result@, *opn as int),
{
    if s.unexecuted_learner_state.contains_key(opn) {
        let mut m = clone_clearnerstate(&s.unexecuted_learner_state);
        m.remove(opn);
        let result = CLearner {
            constants: s.constants.clone_up_to_view(),
            max_ballot_seen: s.max_ballot_seen,
            unexecuted_learner_state: m,
        };
        proof {
            lemma_abstractify_clearnerstate_remove(
                s.unexecuted_learner_state, result.unexecuted_learner_state, *opn);
        }
        result
    } else {
        s.clone_up_to_view()
    }
}

pub exec fn CLearnerProcess2b(s: &CLearner, packet: &CPacket) -> (result: CLearner)
requires
    s.valid(),
    packet.valid(),
    packet.msg is CMessage2b,
ensures
    result.valid(),
    LLearnerProcess2b(s@, result@, packet@),
{
    let (m_opn_2b, m_bal_2b, m_val_2b) = match &packet.msg {
        CMessage::CMessage2b{bal_2b, opn_2b, val_2b} => (*opn_2b, *bal_2b, clone_request_batch_up_to_view(val_2b)),
        _ => unreachable_value()
    };
    let opn = m_opn_2b;

    if !contains(&s.constants.all.config.replica_ids, &packet.src) || CBalLt(&m_bal_2b, &s.max_ballot_seen) {
        // Branch 1: source not in config or ballot too old — return s unchanged
        let result = s.clone_up_to_view();
        proof {
            assert(result@ == s@);
            assert(result.valid());
            assert(LLearnerProcess2b(s@, result@, packet@));
        }
        result
    } else if CBalLt(&s.max_ballot_seen, &m_bal_2b) {
        // Branch 2: new higher ballot — reset state to singleton
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use crate::common::native::io_s::axiom_endpoint_key_model;
        let src_clone = packet.src.clone_up_to_view();
        let mut hs: HashSet<EndPoint> = HashSet::new();
        hs.insert(src_clone);
        let tup_ = CLearnerTuple {
            received_2b_message_senders: hs,
            candidate_learned_value: m_val_2b,
        };
        let mut new_state: HashMap<COperationNumber, CLearnerTuple> = HashMap::new();
        { new_state.insert(opn, tup_); }
        let result = CLearner {
            constants: s.constants.clone_up_to_view(),
            max_ballot_seen: m_bal_2b,
            unexecuted_learner_state: new_state,
        };
        proof {
            assert(src_clone@ == packet.src@);
            assert(packet.src.abstractable());
            lemma_abstractify_singleton_clearnerstate(
                result.unexecuted_learner_state, opn, tup_);
            assert(result@.constants == s@.constants);
            assert(result@.max_ballot_seen == packet@.msg->bal_2b);
            let spec_tup = LearnerTuple{
                received_2b_message_senders: Set::<AbstractEndPoint>::empty().insert(packet@.src),
                candidate_learned_value: packet@.msg->val_2b,
            };
            broadcast use vstd::set::Set::lemma_set_map_insert_commute;
            let ghost f = |i: EndPoint| i@;
            let ghost mapped_empty = Set::<EndPoint>::empty().map(f);
            assert forall |y: AbstractEndPoint| !(#[trigger] mapped_empty.contains(y)) by { }
            assert(mapped_empty =~= Set::<AbstractEndPoint>::empty());
            assert(Set::<EndPoint>::empty().insert(src_clone).map(|i: EndPoint| i@)
                =~= Set::<AbstractEndPoint>::empty().insert(src_clone@));
            assert(src_clone@ == packet@.src);
            assert(tup_@.received_2b_message_senders =~= spec_tup.received_2b_message_senders);
            assert(tup_@.candidate_learned_value =~= spec_tup.candidate_learned_value);
            assert(tup_@ == spec_tup);
            assert(result@.unexecuted_learner_state =~= Map::<OperationNumber, LearnerTuple>::empty().insert(opn as int, spec_tup));
            assert(LLearnerProcess2b(s@, result@, packet@));
        }
        result
    } else {
        if !s.unexecuted_learner_state.contains_key(&opn) {
            // Branch 3: equal ballot, opn not in state — insert new entry
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use crate::common::native::io_s::axiom_endpoint_key_model;
            let src_clone = packet.src.clone_up_to_view();
            let mut hs: HashSet<EndPoint> = HashSet::new();
            hs.insert(src_clone);
            let tup_ = CLearnerTuple {
                received_2b_message_senders: hs,
                candidate_learned_value: m_val_2b,
            };
            let mut new_state = clone_clearnerstate(&s.unexecuted_learner_state);
            { new_state.insert(opn, tup_); }
            let result = CLearner {
                constants: s.constants.clone_up_to_view(),
                max_ballot_seen: m_bal_2b,
                unexecuted_learner_state: new_state,
            };
            proof {
                assert(src_clone@ == packet.src@);
                assert(packet.src.abstractable());
                lemma_abstractify_clearnerstate_insert(
                    s.unexecuted_learner_state, result.unexecuted_learner_state, opn, tup_);
                assert(!BalLt(m_bal_2b@, s.max_ballot_seen@));
                assert(!BalLt(s.max_ballot_seen@, m_bal_2b@));
                assert(s@.constants.all.config.replica_ids.contains(packet@.src));
                assert(!(!s@.constants.all.config.replica_ids.contains(packet@.src) || BalLt(packet@.msg->bal_2b, s@.max_ballot_seen)));
                assert(!BalLt(s@.max_ballot_seen, packet@.msg->bal_2b));
                assert(!s.unexecuted_learner_state@.contains_key(opn));
                assert(result@.constants == s@.constants);
                assert(result@.max_ballot_seen == m_bal_2b@);
                assert(result@.max_ballot_seen == packet@.msg->bal_2b);
                let spec_tup = LearnerTuple{
                    received_2b_message_senders: Set::<AbstractEndPoint>::empty().insert(packet@.src),
                    candidate_learned_value: packet@.msg->val_2b,
                };
                broadcast use vstd::set::Set::lemma_set_map_insert_commute;
                let ghost f = |i: EndPoint| i@;
                let ghost mapped_empty = Set::<EndPoint>::empty().map(f);
                assert forall |y: AbstractEndPoint| !(#[trigger] mapped_empty.contains(y)) by { }
                assert(mapped_empty =~= Set::<AbstractEndPoint>::empty());
                assert(Set::<EndPoint>::empty().insert(src_clone).map(|i: EndPoint| i@)
                    =~= Set::<AbstractEndPoint>::empty().insert(src_clone@));
                assert(src_clone@ == packet@.src);
                assert(tup_@.received_2b_message_senders =~= spec_tup.received_2b_message_senders);
                assert(tup_@.candidate_learned_value =~= spec_tup.candidate_learned_value);
                assert(tup_@ == spec_tup);
                assert(result@.unexecuted_learner_state =~= s@.unexecuted_learner_state.insert(opn as int, spec_tup));
                assert(LLearnerProcess2b(s@, result@, packet@));
            }
            result
        } else {
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use crate::common::native::io_s::axiom_endpoint_key_model;
            let tup_ref = s.unexecuted_learner_state.get(&opn).unwrap();
            let sender_present = tup_ref.received_2b_message_senders.contains(&packet.src);
            if sender_present {
                // Branch 4: already received from this sender — return s unchanged
                let result = s.clone_up_to_view();
                proof {
                    assert(result@ == s@);
                    assert(s@.constants.all.config.replica_ids.contains(packet@.src));
                    assert(!BalLt(m_bal_2b@, s.max_ballot_seen@));
                    assert(!(!s@.constants.all.config.replica_ids.contains(packet@.src) || BalLt(packet@.msg->bal_2b, s@.max_ballot_seen)));
                    assert(!BalLt(s.max_ballot_seen@, m_bal_2b@));
                    assert(!BalLt(s@.max_ballot_seen, packet@.msg->bal_2b));
                    assert(s.unexecuted_learner_state@.contains_key(opn));
                    let abs_map = abstractify_clearnerstate(s.unexecuted_learner_state);
                    assert(abs_map.contains_key(opn as int));
                    assert(s@.unexecuted_learner_state.contains_key(opn as int));
                    assert(packet.src.abstractable());
                    assert(tup_ref.received_2b_message_senders@.contains(packet.src));
                    assert(tup_ref.received_2b_message_senders@.map(|i: EndPoint| i@).contains(packet.src@));
                    assert(abs_map[opn as int].received_2b_message_senders.contains(packet@.src));
                    assert(s@.unexecuted_learner_state[opn as int].received_2b_message_senders.contains(packet@.src));
                    assert(LLearnerProcess2b(s@, result@, packet@));
                }
                result
            } else {
                // Branch 5: add sender to existing entry
                broadcast use vstd::std_specs::hash::group_hash_axioms;
                broadcast use crate::common::native::io_s::axiom_endpoint_key_model;
                let src_clone = packet.src.clone_up_to_view();
                let mut new_senders = clone_hashset(&tup_ref.received_2b_message_senders);
                new_senders.insert(src_clone);
                let tup_ = CLearnerTuple {
                    received_2b_message_senders: new_senders,
                    candidate_learned_value: clone_request_batch_up_to_view(&tup_ref.candidate_learned_value),
                };
                let mut new_state = clone_clearnerstate(&s.unexecuted_learner_state);
                { new_state.insert(opn, tup_); }
                let result = CLearner {
                    constants: s.constants.clone_up_to_view(),
                    max_ballot_seen: s.max_ballot_seen,
                    unexecuted_learner_state: new_state,
                };
                proof {
                    assert(src_clone@ == packet.src@);
                    assert(packet.src.abstractable());
                    lemma_abstractify_clearnerstate_insert(
                        s.unexecuted_learner_state, result.unexecuted_learner_state, opn, tup_);
                    assert(s@.constants.all.config.replica_ids.contains(packet@.src));
                    assert(!BalLt(m_bal_2b@, s.max_ballot_seen@));
                    assert(!(!s@.constants.all.config.replica_ids.contains(packet@.src) || BalLt(packet@.msg->bal_2b, s@.max_ballot_seen)));
                    assert(!BalLt(s.max_ballot_seen@, m_bal_2b@));
                    assert(!BalLt(s@.max_ballot_seen, packet@.msg->bal_2b));
                    assert(s.unexecuted_learner_state@.contains_key(opn));
                    assert(s@.unexecuted_learner_state.contains_key(opn as int));
                    broadcast use crate::common::native::io_s::axiom_endpoint_view;
                    assert(!tup_ref.received_2b_message_senders@.contains(packet.src));
                    assert forall |x: EndPoint| tup_ref.received_2b_message_senders@.contains(x) implies x@ != packet.src@ by {
                        if x@ == packet.src@ {
                            assert(x == packet.src);
                        }
                    }
                    assert(!tup_ref.received_2b_message_senders@.map(|i: EndPoint| i@).contains(packet.src@));
                    assert(!s@.unexecuted_learner_state[opn as int].received_2b_message_senders.contains(packet@.src));
                    assert(result@.constants == s@.constants);
                    assert(result@.max_ballot_seen == s@.max_ballot_seen);
                    broadcast use vstd::set::Set::lemma_set_map_insert_commute;
                    let spec_old_tup = s@.unexecuted_learner_state[opn as int];
                    assert(tup_@.received_2b_message_senders =~= spec_old_tup.received_2b_message_senders.insert(packet@.src));
                    assert(tup_@.candidate_learned_value =~= spec_old_tup.candidate_learned_value);
                    let spec_new_tup = LearnerTuple{
                        received_2b_message_senders: spec_old_tup.received_2b_message_senders + Set::<AbstractEndPoint>::empty().insert(packet@.src),
                        candidate_learned_value: spec_old_tup.candidate_learned_value,
                    };
                    assert(spec_new_tup.received_2b_message_senders =~= spec_old_tup.received_2b_message_senders.insert(packet@.src));
                    assert(tup_@ == spec_new_tup);
                    assert(result@.unexecuted_learner_state =~= s@.unexecuted_learner_state.insert(opn as int, spec_new_tup));
                    assert(LLearnerProcess2b(s@, result@, packet@));
                }
                result
            }
        }
    }
}

pub exec fn CLearnerForgetOperationsBefore(s: &CLearner, ops_complete: &u64) -> (result: CLearner)
requires
    s.valid(),
ensures
    result.valid(),
    LLearnerForgetOperationsBefore(s@, result@, *ops_complete as int),
{
    let filtered = filter_clearnerstate(&s.unexecuted_learner_state, *ops_complete);
    let result = CLearner {
        constants: s.constants.clone_up_to_view(),
        max_ballot_seen: s.max_ballot_seen,
        unexecuted_learner_state: filtered,
    };
    proof {
        let s_map = s.unexecuted_learner_state;
        let f_map = result.unexecuted_learner_state;
        let s_abs = abstractify_clearnerstate(s_map);
        let r_abs = abstractify_clearnerstate(f_map);

        // Forward: r_abs has k ==> ak >= ops_complete && s_abs has k
        assert forall |ak: OperationNumber|
            r_abs.contains_key(ak) implies ak >= *ops_complete as int && s_abs.contains_key(ak)
        by {
            assert(exists |k: u64| f_map@.contains_key(k) && k as int == ak);
            let ck = choose |k: u64| f_map@.contains_key(k) && k as int == ak;
            let ghost _trig = f_map@[ck];
            assert(s_map@.contains_key(ck));
            assert(ck >= *ops_complete);
            assert(s_map@.contains_key(ck) && ck as int == ak);
        }

        // Backward: ak >= ops_complete && s_abs has k ==> r_abs has k
        assert forall |ak: OperationNumber|
            ak >= *ops_complete as int && s_abs.contains_key(ak) implies r_abs.contains_key(ak)
        by {
            assert(exists |k: u64| s_map@.contains_key(k) && k as int == ak);
            let ck = choose |k: u64| s_map@.contains_key(k) && k as int == ak;
            assert(s_map@.contains_key(ck));
            assert(ck as int >= *ops_complete as int);
            assert(f_map@.contains_key(ck));
            assert(f_map@.contains_key(ck) && ck as int == ak);
        }

        // Conjunct 2: values match
        assert forall |ak: OperationNumber|
            r_abs.contains_key(ak) implies r_abs[ak] == s_abs[ak]
        by {
            assert(exists |k: u64| f_map@.contains_key(k) && k as int == ak);
            let ck_r = choose |k: u64| f_map@.contains_key(k) && k as int == ak;
            assert(s_map@.contains_key(ck_r));
            let ck_s = choose |k: u64| s_map@.contains_key(k) && k as int == ak;
            assert(ck_r == ck_s);
            assert(f_map@[ck_r]@ == s_map@[ck_r]@);
        }
    }
    result
}
