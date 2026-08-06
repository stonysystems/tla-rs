use crate::common::collections::sets::lemma_quorum_intersection;
use crate::protocol::Raft::membership::*;
use crate::protocol::Raft::raft::{
    LAdvanceCommitIndex,
    LAdvanceCommitIndexWithMembership,
    LAppendConfigurationEntry,
    LBecomeLeader,
    LBecomeLeaderWithMembership,
    LClientRequest,
    LHandleVoteResponseMsg,
    LHandleVoteResponseMsgWithMembership,
    LReceiveVoteAndBecomeLeader,
    LNext,
    LTryAdvanceCommitIndex,
    LTryAdvanceCommitIndexWithMembership,
    LFollowerAppendEntries,
    replicator_count,
    step_down_if_needed,
};
use crate::protocol::Raft::refinement_proof::state_machine::{
    MaxCommitIndex,
    RaftDistributedState,
};
use crate::protocol::Raft::types::{
    LConstants,
    LLogEntry,
    LLogValue,
    LMembershipConfig,
    LMembershipPhase,
    LRaftMessage,
    LState,
};
use vstd::prelude::*;

verus! {

    /// The view of an executable stable phase is the corresponding
    /// mathematical stable phase.
    pub proof fn lemma_stable_membership_phase_view(
        config: LMembershipConfig,
    )
        ensures
            membership_phase_view(
                LMembershipPhase::Stable {
                    config,
                },
            ) == (MembershipPhase::Stable {
                config: membership_config_view(config),
            }),
    {
    }

    /// The view of an executable joint phase contains the set views
    /// of both executable configurations.
    pub proof fn lemma_joint_membership_phase_view(
        old_config: LMembershipConfig,
        new_config: LMembershipConfig,
    )
        ensures
            membership_phase_view(
                LMembershipPhase::Joint {
                    old_config,
                    new_config,
                },
            ) == (MembershipPhase::Joint {
                old_config: membership_config_view(old_config),
                new_config: membership_config_view(new_config),
            }),
    {
    }

    /// A majority of the executable configuration's set view is
    /// exactly a valid quorum for its corresponding stable phase.
    pub proof fn lemma_executable_majority_is_stable_phase_quorum(
        config: LMembershipConfig,
        quorum: Set<int>,
    )
        requires
            is_majority_of(
                quorum,
                membership_config_view(config),
            ),
        ensures
            is_quorum_for_phase(
                quorum,
                stable_phase_from_config(config),
            ),
    {
    }

    /// Specification-level representation of entries that may affect
    /// membership. This remains separate from the concrete Raft log
    /// while the committed-log design is developed and verified.
    pub enum MembershipLogEntry {
        /// An ordinary replicated command that does not change membership.
        Data {
            value: int,
        },

        /// A complete membership phase recorded in the replicated log.
        Configuration {
            phase: MembershipPhase,
        },
    }

    /// Convert an executable log value into the corresponding entry
    /// used by the membership-history proof.
    pub open spec fn membership_log_entry_view(
        value: LLogValue,
    ) -> MembershipLogEntry {
        match value {
            LLogValue::Data {
                value,
            } => {
                MembershipLogEntry::Data {
                    value,
                }
            },
            LLogValue::Configuration {
                phase,
            } => {
                MembershipLogEntry::Configuration {
                    phase: membership_phase_view(phase),
                }
            },
        }
    }

    /// Project a prefix of the actual tagged Raft log into the
    /// one-entry-per-index membership-history representation.
    ///
    /// Unlike the application-log projection, this does not filter
    /// configuration entries. Keeping every physical index makes it
    /// possible to reuse the legal-history lemmas below.
    pub open spec fn membership_history_from_raft_log(
        log: Seq<LLogEntry>,
        prefix_len: int,
    ) -> Seq<MembershipLogEntry>
        decreases prefix_len
    {
        if prefix_len <= 0 || prefix_len > log.len() {
            Seq::<MembershipLogEntry>::empty()
        } else {
            membership_history_from_raft_log(
                log,
                prefix_len - 1,
            ).push(
                membership_log_entry_view(
                    log[prefix_len - 1].payload,
                ),
            )
        }
    }

    /// A valid projected prefix contains exactly one membership-history
    /// entry for every physical Raft-log entry in that prefix.
    pub proof fn lemma_membership_history_from_raft_log_len(
        log: Seq<LLogEntry>,
        prefix_len: int,
    )
        requires
            0 <= prefix_len <= log.len(),
        ensures
            membership_history_from_raft_log(
                log,
                prefix_len,
            ).len() == prefix_len,
        decreases prefix_len,
    {
        if prefix_len > 0 {
            lemma_membership_history_from_raft_log_len(
                log,
                prefix_len - 1,
            );
        }
    }

    /// Extending the physical log beyond a valid prefix does not change
    /// that prefix's membership-history projection.
    pub proof fn lemma_membership_history_ignores_uncommitted_raft_append(
        log: Seq<LLogEntry>,
        entry: LLogEntry,
        prefix_len: int,
    )
        requires
            0 <= prefix_len <= log.len(),
        ensures
            membership_history_from_raft_log(
                log.push(entry),
                prefix_len,
            ) == membership_history_from_raft_log(
                log,
                prefix_len,
            ),
        decreases prefix_len,
    {
        if prefix_len > 0 {
            assert(log.push(entry)[prefix_len - 1]
                == log[prefix_len - 1]);
            lemma_membership_history_ignores_uncommitted_raft_append(
                log,
                entry,
                prefix_len - 1,
            );
        }
    }

    /// Projecting a valid prefix preserves the payload at every
    /// physical Raft-log index.
    pub proof fn lemma_membership_history_from_raft_log_index(
        log: Seq<LLogEntry>,
        prefix_len: int,
        index: int,
    )
        requires
            0 <= prefix_len <= log.len(),
            0 <= index < prefix_len,
        ensures
            membership_history_from_raft_log(
                log,
                prefix_len,
            )[index] == membership_log_entry_view(
                log[index].payload,
            ),
        decreases prefix_len,
    {
        lemma_membership_history_from_raft_log_len(
            log,
            prefix_len,
        );

        if index < prefix_len - 1 {
            lemma_membership_history_from_raft_log_index(
                log,
                prefix_len - 1,
                index,
            );
        } else {
            assert(index == prefix_len - 1);
            lemma_membership_history_from_raft_log_len(
                log,
                prefix_len - 1,
            );
        }
    }

    /// The proof-history projection and the actual tagged Raft log
    /// derive exactly the same active membership phase.
    pub proof fn lemma_projected_membership_history_has_same_active_phase(
        log: Seq<LLogEntry>,
        committed_len: int,
        initial_phase: MembershipPhase,
    )
        requires
            0 <= committed_len <= log.len(),
        ensures
            active_membership_phase(
                membership_history_from_raft_log(
                    log,
                    committed_len,
                ),
                committed_len,
                initial_phase,
            ) == active_membership_phase_from_raft_log(
                log,
                committed_len,
                initial_phase,
            ),
        decreases committed_len,
    {
        if committed_len > 0 {
            let previous_history =
                membership_history_from_raft_log(
                    log,
                    committed_len - 1,
                );

            let final_entry = membership_log_entry_view(
                log[committed_len - 1].payload,
            );

            assert(
                membership_history_from_raft_log(
                    log,
                    committed_len,
                ) == previous_history.push(final_entry)
            );

            lemma_membership_history_from_raft_log_len(
                log,
                committed_len - 1,
            );

            match log[committed_len - 1].payload {
                LLogValue::Data { value: _ } => {
                    lemma_uncommitted_entry_does_not_affect_active_phase(
                        previous_history,
                        final_entry,
                        committed_len - 1,
                        initial_phase,
                    );

                    lemma_projected_membership_history_has_same_active_phase(
                        log,
                        committed_len - 1,
                        initial_phase,
                    );
                },
                LLogValue::Configuration { phase } => {
                    assert(final_entry
                        == (MembershipLogEntry::Configuration {
                            phase: membership_phase_view(phase),
                        }));

                    assert(
                        active_membership_phase(
                            previous_history.push(final_entry),
                            committed_len,
                            initial_phase,
                        ) == membership_phase_view(phase)
                    );
                },
            }
        }
    }

    /// Ordinary executable data remains ordinary data in the proof log.
    pub proof fn lemma_data_log_value_view(
        value: int,
    )
        ensures
            membership_log_entry_view(
                LLogValue::Data {
                    value,
                },
            ) == (MembershipLogEntry::Data {
                value,
            }),
    {
    }

    /// An executable configuration value becomes a configuration
    /// entry containing the mathematical view of its phase.
    pub proof fn lemma_configuration_log_value_view(
        phase: LMembershipPhase,
    )
        ensures
            membership_log_entry_view(
                LLogValue::Configuration {
                    phase,
                },
            ) == (MembershipLogEntry::Configuration {
                phase: membership_phase_view(phase),
            }),
    {
    }

    /// An ordinary log entry's tagged payload agrees with its
    /// existing application-level integer value.
    pub open spec fn data_payload_matches_value(
        entry: LLogEntry,
    ) -> bool {
        entry.payload == (LLogValue::Data {
            value: entry.value,
        })
    }

    /// The client-request action appends an ordinary data entry whose
    /// tagged payload agrees with its application value.
    pub proof fn lemma_client_request_appends_matching_data_payload(
        s: LState,
        s_: LState,
        c: LConstants,
        value: int,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            LClientRequest(
                s,
                s_,
                c,
                value,
                sent_packets,
            ),
        ensures
            s_.log.len() == s.log.len() + 1,
            data_payload_matches_value(
                s_.log[s.log.len() as int],
            ),
    {
        let entry = LLogEntry {
            term: s.current_term,
            value,
            payload: LLogValue::Data {
                value,
            },
        };

        assert(s_.log == s.log.push(entry));
        assert(s_.log[s.log.len() as int] == entry);
        assert(data_payload_matches_value(entry));
    }

    /// When a follower accepts an entry, it appends an ordinary data
    /// entry whose tagged payload agrees with its application value.
    pub proof fn lemma_follower_append_appends_matching_data_payload(
        s: LState,
        s_: LState,
        c: LConstants,
        ae_term: int,
        ae_leader: int,
        ae_prev_index: int,
        ae_prev_term: int,
        ae_value: int,
        ae_has_entry: bool,
        ae_leader_commit: int,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
             LFollowerAppendEntries(
                s,
                s_,
                c,
                ae_term,
                ae_leader,
                ae_prev_index,
                ae_prev_term,
                ae_value,
                LLogValue::Data {
                    value: ae_value,
                },
                ae_has_entry,
                ae_leader_commit,
                sent_packets,
            ),
            ae_has_entry,
        ensures
            s_.log.len() == s.log.len() + 1,
            data_payload_matches_value(
                s_.log[s.log.len() as int],
            ),
    {
        let entry = LLogEntry {
            term: ae_term,
            value: ae_value,
            payload: LLogValue::Data {
                value: ae_value,
            },
        };

        assert(s_.log == s.log.push(entry));
        assert(s_.log[s.log.len() as int] == entry);
        assert(data_payload_matches_value(entry));
    }

    /// With no committed actual log entries, the initial membership
    /// phase remains active.
    pub proof fn lemma_empty_raft_log_prefix_uses_initial_phase(
        log: Seq<LLogEntry>,
        initial_phase: MembershipPhase,
    )
        ensures
            active_membership_phase_from_raft_log(
                log,
                0,
                initial_phase,
            ) == initial_phase,
    {
    }

    /// A committed configuration payload in the actual Raft log
    /// becomes the active mathematical membership phase.
    pub proof fn lemma_committed_raft_configuration_becomes_active(
        log: Seq<LLogEntry>,
        initial_phase: MembershipPhase,
        term: int,
        legacy_value: int,
        phase: LMembershipPhase,
    )
        ensures
            active_membership_phase_from_raft_log(
                log.push(
                    LLogEntry {
                        term,
                        value: legacy_value,
                        payload: LLogValue::Configuration {
                            phase,
                        },
                    },
                ),
                (log.len() + 1) as int,
                initial_phase,
            ) == membership_phase_view(phase),
    {
    }

    /// An entry outside the committed prefix cannot affect the active
    /// membership phase derived from the actual Raft log.
    pub proof fn lemma_uncommitted_raft_entry_does_not_affect_active_phase(
        log: Seq<LLogEntry>,
        uncommitted_entry: LLogEntry,
        committed_len: int,
        initial_phase: MembershipPhase,
    )
        requires
            0 <= committed_len,
            committed_len <= log.len(),
        ensures
            active_membership_phase_from_raft_log(
                log.push(uncommitted_entry),
                committed_len,
                initial_phase,
            ) == active_membership_phase_from_raft_log(
                log,
                committed_len,
                initial_phase,
            ),
        decreases committed_len
    {
        if committed_len <= 0 {
        } else {
            assert(0 <= committed_len - 1);
            assert(committed_len - 1 < log.len());

            assert(
                log.push(uncommitted_entry)[committed_len - 1]
                    == log[committed_len - 1]
            );

            match log[committed_len - 1].payload {
                LLogValue::Data {
                    value: _,
                } => {
                    lemma_uncommitted_raft_entry_does_not_affect_active_phase(
                        log,
                        uncommitted_entry,
                        committed_len - 1,
                        initial_phase,
                    );
                },
                LLogValue::Configuration {
                    phase: _,
                } => {
                },
            }
        }
    }

    /// Two actual Raft logs with identical committed entries derive
    /// the same active membership phase.
    pub proof fn lemma_equal_committed_raft_prefixes_have_same_active_phase(
        left_log: Seq<LLogEntry>,
        right_log: Seq<LLogEntry>,
        committed_len: int,
        initial_phase: MembershipPhase,
    )
        requires
            0 <= committed_len <= left_log.len(),
            committed_len <= right_log.len(),
            forall |index: int|
                0 <= index < committed_len
                ==> left_log[index] == right_log[index],
        ensures
            active_membership_phase_from_raft_log(
                left_log,
                committed_len,
                initial_phase,
            ) == active_membership_phase_from_raft_log(
                right_log,
                committed_len,
                initial_phase,
            ),
        decreases
            committed_len,
    {
        if committed_len > 0 {
            assert(
                left_log[committed_len - 1]
                == right_log[committed_len - 1]
            );

            match left_log[committed_len - 1].payload {
                LLogValue::Data { value: _ } => {
                    assert forall |index: int|
                        0 <= index < committed_len - 1
                        implies left_log[index] == right_log[index]
                    by {
                    };
                    lemma_equal_committed_raft_prefixes_have_same_active_phase(
                        left_log,
                        right_log,
                        committed_len - 1,
                        initial_phase,
                    );
                },
                LLogValue::Configuration { phase: _ } => {
                },
            }
        }
    }

    /// The derived membership phase only reads Configuration entries, so two
    /// logs that place the same Configuration entries at the same positions
    /// derive the same phase — even if their Data entries differ entirely.
    ///
    /// This is strictly weaker in its hypotheses than
    /// `lemma_equal_committed_raft_prefixes_have_same_active_phase`, which
    /// demands full prefix equality. It is what a minimal-missing-boundary
    /// argument can actually supply, since such an argument recovers agreement
    /// on membership boundaries but says nothing about application data.
    pub proof fn lemma_logs_with_same_configurations_have_same_active_phase(
        left_log: Seq<LLogEntry>,
        right_log: Seq<LLogEntry>,
        committed_len: int,
        initial_phase: MembershipPhase,
    )
        requires
            0 <= committed_len <= left_log.len(),
            committed_len <= right_log.len(),
            forall |index: int|
                0 <= index < committed_len
                ==> ((left_log[index].payload is Configuration)
                    == (right_log[index].payload is Configuration)),
            forall |index: int|
                0 <= index < committed_len
                && left_log[index].payload is Configuration
                ==> left_log[index] == right_log[index],
        ensures
            active_membership_phase_from_raft_log(
                left_log,
                committed_len,
                initial_phase,
            ) == active_membership_phase_from_raft_log(
                right_log,
                committed_len,
                initial_phase,
            ),
        decreases
            committed_len,
    {
        if committed_len > 0 {
            if left_log[committed_len - 1].payload is Configuration {
                // Both logs carry the identical Configuration entry here, so
                // both derivations stop at the same phase.
                assert(left_log[committed_len - 1]
                    == right_log[committed_len - 1]);
            } else {
                // Both carry Data here, so both derivations recurse.
                assert(!(right_log[committed_len - 1].payload
                    is Configuration));
                lemma_logs_with_same_configurations_have_same_active_phase(
                    left_log,
                    right_log,
                    committed_len - 1,
                    initial_phase,
                );
            }
        }
    }

    /// Server states with the same committed log prefix and initial
    /// configuration therefore make decisions under the same phase.
    pub proof fn lemma_states_with_equal_committed_prefix_have_same_active_phase(
        left_state: LState,
        left_constants: LConstants,
        right_state: LState,
        right_constants: LConstants,
    )
        requires
            left_state.commit_index == right_state.commit_index,
            0 <= left_state.commit_index,
            left_state.commit_index <= left_state.log.len(),
            right_state.commit_index <= right_state.log.len(),
            left_constants.servers == right_constants.servers,
            forall |index: int|
                0 <= index < left_state.commit_index
                ==> left_state.log[index] == right_state.log[index],
        ensures
            active_membership_phase_for_state(
                left_state,
                left_constants,
            ) == active_membership_phase_for_state(
                right_state,
                right_constants,
            ),
    {
        lemma_equal_committed_raft_prefixes_have_same_active_phase(
            left_state.log,
            right_state.log,
            left_state.commit_index,
            MembershipPhase::Stable {
                config: left_constants.servers,
            },
        );
        assert(
            (MembershipPhase::Stable {
                config: left_constants.servers,
            }) == (MembershipPhase::Stable {
                config: right_constants.servers,
            })
        );
    }

    /// Committing an ordinary data payload in the actual Raft log
    /// does not change the active membership phase.
    pub proof fn lemma_committed_raft_data_preserves_active_phase(
        log: Seq<LLogEntry>,
        initial_phase: MembershipPhase,
        term: int,
        value: int,
    )
        ensures
            active_membership_phase_from_raft_log(
                log.push(
                    LLogEntry {
                        term,
                        value,
                        payload: LLogValue::Data {
                            value,
                        },
                    },
                ),
                (log.len() + 1) as int,
                initial_phase,
            ) == active_membership_phase_from_raft_log(
                log,
                log.len() as int,
                initial_phase,
            ),
    {
        let data_entry = LLogEntry {
            term,
            value,
            payload: LLogValue::Data {
                value,
            },
        };

        assert(
            active_membership_phase_from_raft_log(
                log.push(data_entry),
                (log.len() + 1) as int,
                initial_phase,
            ) == active_membership_phase_from_raft_log(
                log.push(data_entry),
                log.len() as int,
                initial_phase,
            )
        );

        lemma_uncommitted_raft_entry_does_not_affect_active_phase(
            log,
            data_entry,
            log.len() as int,
            initial_phase,
        );
    }

    /// Extract only ordinary application commands from a prefix of
    /// Raft's actual log.
    ///
    /// Configuration entries affect membership but are not exposed as
    /// client commands.
    pub open spec fn application_values_from_raft_log(
        log: Seq<LLogEntry>,
        committed_len: int,
    ) -> Seq<int>
        decreases committed_len
    {
        if committed_len <= 0 || committed_len > log.len() {
            Seq::<int>::empty()
        } else {
            let previous = application_values_from_raft_log(
                log,
                committed_len - 1,
            );

            match log[committed_len - 1].payload {
                LLogValue::Data {
                    value,
                } => {
                    previous.push(value)
                },
                LLogValue::Configuration {
                    phase: _,
                } => {
                    previous
                },
            }
        }
    }

    /// Extract the application-visible committed log from the distributed
    /// Raft state without changing the existing physical committed-log view.
    ///
    /// The physical committed prefix still includes every Raft entry, while
    /// this parallel view filters Configuration entries from that prefix.
    pub open spec fn GetApplicationCommittedLog(
        ds: RaftDistributedState,
    ) -> Seq<int> {
        let max_commit = MaxCommitIndex(ds);
        if max_commit <= 0 {
            Seq::<int>::empty()
        } else {
            let server_id = choose |id: int| 0 <= id < ds.num_servers
                && ds.server_states[id].commit_index >= max_commit
                && ds.server_states[id].log.len() >= max_commit;
            application_values_from_raft_log(
                ds.server_states[server_id].log,
                max_commit,
            )
        }
    }

    /// The parallel distributed view is exactly the tagged-payload filter
    /// applied to the selected maximum committed Raft prefix.
    pub proof fn lemma_get_application_committed_log_selected_prefix(
        ds: RaftDistributedState,
    )
        ensures
            MaxCommitIndex(ds) <= 0 ==> GetApplicationCommittedLog(ds)
                == Seq::<int>::empty(),
            MaxCommitIndex(ds) > 0 ==> {
                let max_commit = MaxCommitIndex(ds);
                let server_id = choose |id: int| 0 <= id < ds.num_servers
                    && ds.server_states[id].commit_index >= max_commit
                    && ds.server_states[id].log.len() >= max_commit;
                GetApplicationCommittedLog(ds)
                    == application_values_from_raft_log(
                        ds.server_states[server_id].log,
                        max_commit,
                    )
            },
    {
    }

    /// Appending an entry outside the examined prefix cannot change
    /// the extracted application-command sequence.
    pub proof fn lemma_uncommitted_raft_entry_does_not_affect_application_values(
        log: Seq<LLogEntry>,
        uncommitted_entry: LLogEntry,
        committed_len: int,
    )
        requires
            0 <= committed_len,
            committed_len <= log.len(),
        ensures
            application_values_from_raft_log(
                log.push(uncommitted_entry),
                committed_len,
            ) == application_values_from_raft_log(
                log,
                committed_len,
            ),
        decreases committed_len
    {
        if committed_len <= 0 {
        } else {
            assert(0 <= committed_len - 1);
            assert(committed_len - 1 < log.len());

            assert(
                log.push(uncommitted_entry)[committed_len - 1]
                    == log[committed_len - 1]
            );

            lemma_uncommitted_raft_entry_does_not_affect_application_values(
                log,
                uncommitted_entry,
                committed_len - 1,
            );
        }
    }

    /// Appending a legal but uncommitted configuration entry preserves
    /// the currently active membership and application-visible output.
    pub proof fn lemma_append_configuration_preserves_committed_views(
        s: LState,
        s_: LState,
        c: LConstants,
        phase: LMembershipPhase,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            LAppendConfigurationEntry(
                s,
                s_,
                c,
                phase,
                sent_packets,
            ),
        ensures
            s_.log.len() == s.log.len() + 1,
            is_legal_phase_progression(
                active_membership_phase_from_raft_log(
                    s.log,
                    s.commit_index,
                    MembershipPhase::Stable {
                        config: c.servers,
                    },
                ),
                membership_phase_view(phase),
            ),
            active_membership_phase_from_raft_log(
                s_.log,
                s_.commit_index,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ) == active_membership_phase_from_raft_log(
                s.log,
                s.commit_index,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ),
            application_values_from_raft_log(
                s_.log,
                s_.commit_index,
            ) == application_values_from_raft_log(
                s.log,
                s.commit_index,
            ),
            s_.election_membership_phase
                == s.election_membership_phase,
            forall |index: int|
                s_.commit_index <= index < s_.log.len()
                && s_.log[index].payload is Configuration
                ==> index == s.log.len(),
            !uncommitted_suffix_has_no_configuration(
                s_.log,
                s_.commit_index,
            ),
    {
        let entry = LLogEntry {
            term: s.current_term,
            value: 0int,
            payload: LLogValue::Configuration {
                phase,
            },
        };

        assert(s_.log == s.log.push(entry));

        lemma_uncommitted_raft_entry_does_not_affect_active_phase(
            s.log,
            entry,
            s.commit_index,
            MembershipPhase::Stable {
                config: c.servers,
            },
        );

        lemma_uncommitted_raft_entry_does_not_affect_application_values(
            s.log,
            entry,
            s.commit_index,
        );

        assert forall |index: int|
            s_.commit_index <= index < s_.log.len()
            && s_.log[index].payload is Configuration
            implies index == s.log.len()
        by {
            if index < s.log.len() {
                assert(s_.log[index] == s.log[index]);
                assert(!(s.log[index].payload is Configuration));
                assert(false);
            } else {
                assert(index == s.log.len());
            }
        };

        assert(s_.log[s.log.len() as int] == entry);
        assert(s_.log[s.log.len() as int].payload
            is Configuration);
        assert(!uncommitted_suffix_has_no_configuration(
            s_.log,
            s_.commit_index,
        ));
    }

    /// Appending a legal configuration without committing it preserves
    /// well-formedness of the already committed actual-log history.
    pub proof fn lemma_append_configuration_preserves_actual_history(
        s: LState,
        s_: LState,
        c: LConstants,
        phase: LMembershipPhase,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            LAppendConfigurationEntry(
                s,
                s_,
                c,
                phase,
                sent_packets,
            ),
            committed_raft_membership_history_is_well_formed(
                s.log,
                s.commit_index,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ),
        ensures
            committed_raft_membership_history_is_well_formed(
                s_.log,
                s_.commit_index,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ),
    {
        let entry = s_.log[s.log.len() as int];
        lemma_membership_history_ignores_uncommitted_raft_append(
            s.log,
            entry,
            s.commit_index,
        );
    }

    /// Committing an ordinary data entry appends exactly its payload
    /// value to the application-visible command sequence.
    pub proof fn lemma_committed_raft_data_extends_application_values(
        log: Seq<LLogEntry>,
        term: int,
        value: int,
    )
        ensures
            application_values_from_raft_log(
                log.push(
                    LLogEntry {
                        term,
                        value,
                        payload: LLogValue::Data {
                            value,
                        },
                    },
                ),
                (log.len() + 1) as int,
            ) == application_values_from_raft_log(
                log,
                log.len() as int,
            ).push(value),
    {
        let data_entry = LLogEntry {
            term,
            value,
            payload: LLogValue::Data {
                value,
            },
        };

        lemma_uncommitted_raft_entry_does_not_affect_application_values(
            log,
            data_entry,
            log.len() as int,
        );
    }

    /// Committing a configuration entry changes membership but does
    /// not add a command to the application-visible sequence.
    pub proof fn lemma_committed_raft_configuration_preserves_application_values(
        log: Seq<LLogEntry>,
        term: int,
        legacy_value: int,
        phase: LMembershipPhase,
    )
        ensures
            application_values_from_raft_log(
                log.push(
                    LLogEntry {
                        term,
                        value: legacy_value,
                        payload: LLogValue::Configuration {
                            phase,
                        },
                    },
                ),
                (log.len() + 1) as int,
            ) == application_values_from_raft_log(
                log,
                log.len() as int,
            ),
    {
        let configuration_entry = LLogEntry {
            term,
            value: legacy_value,
            payload: LLogValue::Configuration {
                phase,
            },
        };

        lemma_uncommitted_raft_entry_does_not_affect_application_values(
            log,
            configuration_entry,
            log.len() as int,
        );
    }

    /// Derive the active membership phase from the committed log prefix.
    ///
    /// Only entries with indices below committed_len are considered.
    /// The latest committed Configuration entry determines the active phase.
    /// If no such entry exists, the initial phase remains active.
    pub open spec fn active_membership_phase(
        log: Seq<MembershipLogEntry>,
        committed_len: int,
        initial_phase: MembershipPhase,
    ) -> MembershipPhase
        decreases committed_len
    {
        if committed_len <= 0 || committed_len > log.len() {
            initial_phase
        } else {
            match log[committed_len - 1] {
                MembershipLogEntry::Data { value: _ } => {
                    active_membership_phase(
                        log,
                        committed_len - 1,
                        initial_phase,
                    )
                },
                MembershipLogEntry::Configuration { phase } => {
                    phase
                },
            }
        }
    }

    /// With no committed entries, the initial membership remains active.
    pub proof fn lemma_no_committed_entries_use_initial_phase(
        log: Seq<MembershipLogEntry>,
        initial_phase: MembershipPhase,
    )
        ensures
            active_membership_phase(
                log,
                0,
                initial_phase,
            ) == initial_phase,
    {
    }

    /// If a configuration entry is appended and immediately committed,
    /// the phase contained in that entry becomes active.
    pub proof fn lemma_committed_configuration_becomes_active(
        log: Seq<MembershipLogEntry>,
        initial_phase: MembershipPhase,
        phase: MembershipPhase,
    )
        ensures
            active_membership_phase(
                log.push(
                    MembershipLogEntry::Configuration {
                        phase,
                    },
                ),
                    (log.len() + 1) as int,
                initial_phase,
            ) == phase,
    {
    }

    /// Appending an entry beyond the committed prefix cannot affect
    /// the active membership phase.
    pub proof fn lemma_uncommitted_entry_does_not_affect_active_phase(
        log: Seq<MembershipLogEntry>,
        uncommitted_entry: MembershipLogEntry,
        committed_len: int,
        initial_phase: MembershipPhase,
    )
        requires
            0 <= committed_len,
            committed_len <= log.len(),
        ensures
            active_membership_phase(
                log.push(uncommitted_entry),
                committed_len,
                initial_phase,
            ) == active_membership_phase(
                log,
                committed_len,
                initial_phase,
            ),
        decreases committed_len
    {
        if committed_len <= 0 {
        } else {
            assert(0 <= committed_len - 1);
            assert(committed_len - 1 < log.len());

            assert(
                log.push(uncommitted_entry)[committed_len - 1]
                    == log[committed_len - 1]
            );

            match log[committed_len - 1] {
                MembershipLogEntry::Data { value: _ } => {
                    lemma_uncommitted_entry_does_not_affect_active_phase(
                        log,
                        uncommitted_entry,
                        committed_len - 1,
                        initial_phase,
                    );
                },
                MembershipLogEntry::Configuration { phase: _ } => {
                },
            }
        }
    }

    /// Committing an ordinary data entry does not change membership.
    pub proof fn lemma_committed_data_preserves_active_phase(
        log: Seq<MembershipLogEntry>,
        initial_phase: MembershipPhase,
        value: int,
    )
        ensures
            active_membership_phase(
                log.push(
                    MembershipLogEntry::Data {
                        value,
                    },
                ),
                (log.len() + 1) as int,
                initial_phase,
            ) == active_membership_phase(
                log,
                log.len() as int,
                initial_phase,
            ),
    {
        let data_entry = MembershipLogEntry::Data {
            value,
        };

        assert(
            active_membership_phase(
                log.push(data_entry),
                (log.len() + 1) as int,
                initial_phase,
            ) == active_membership_phase(
                log.push(data_entry),
                log.len() as int,
                initial_phase,
            )
        );

        lemma_uncommitted_entry_does_not_affect_active_phase(
            log,
            data_entry,
            log.len() as int,
            initial_phase,
        );
    }

    /// While the committed membership remains the original stable
    /// configuration, the existing fixed-majority election guard is
    /// sufficient for the new active-phase election guard.
    pub proof fn lemma_fixed_election_guard_implies_active_stable_quorum(
        s: LState,
        c: LConstants,
    )
        requires
            c.servers.len() > 0,
            c.quorum_size == c.servers.len() / 2 + 1,
            s.votes_granted.subset_of(c.servers),
            s.votes_granted.len() >= c.quorum_size,
            election_membership_phase_for_state(s, c)
                == (MembershipPhase::Stable {
                    config: c.servers,
                }),
        ensures
            has_active_election_quorum(s, c),
    {
        assert(s.votes_granted.len()
            >= c.servers.len() / 2 + 1);
        assert(is_majority_of(
            s.votes_granted,
            c.servers,
        ));
        assert(is_quorum_for_phase(
            s.votes_granted,
            MembershipPhase::Stable {
                config: c.servers,
            },
        ));
    }

    /// The existing fixed-quorum leader transition is a valid
    /// active-membership leader transition while membership is stable.
    pub proof fn lemma_fixed_become_leader_implies_membership_become_leader(
        s: LState,
        s_: LState,
        c: LConstants,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            LBecomeLeader(s, s_, c, sent_packets),
            c.servers.len() > 0,
            c.quorum_size == c.servers.len() / 2 + 1,
            s.votes_granted.subset_of(c.servers),
            election_membership_phase_for_state(s, c)
                == (MembershipPhase::Stable {
                    config: c.servers,
                }),
        ensures
            LBecomeLeaderWithMembership(
                s,
                s_,
                c,
                sent_packets,
            ),
    {
        lemma_fixed_election_guard_implies_active_stable_quorum(
            s,
            c,
        );
    }

    /// While membership is still the original stable configuration,
    /// the fixed vote-response handler is also a valid dynamic-membership
    /// vote-response handler.
    pub proof fn lemma_fixed_vote_response_implies_membership_vote_response(
        s: LState,
        s_: LState,
        c: LConstants,
        term: int,
        granted: bool,
        voter: int,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            LHandleVoteResponseMsg(
                s,
                s_,
                c,
                term,
                granted,
                voter,
                sent_packets,
            ),
            c.servers.len() > 0,
            c.quorum_size == c.servers.len() / 2 + 1,
            step_down_if_needed(s, term).votes_granted
                .subset_of(c.servers),
            election_membership_phase_for_state(
                step_down_if_needed(s, term),
                c,
            ) == (MembershipPhase::Stable {
                config: c.servers,
            }),
        ensures
            LHandleVoteResponseMsgWithMembership(
                s,
                s_,
                c,
                term,
                granted,
                voter,
                sent_packets,
            ),
    {
        let s_mid = step_down_if_needed(s, term);

        if s_mid.role is Candidate
            && term >= s_mid.current_term
            && granted
            && c.servers.contains(voter)
        {
            let votes = s_mid.votes_granted.insert(voter);

            assert(votes.subset_of(c.servers)) by {
                assert forall |server: int|
                    votes.contains(server)
                    implies c.servers.contains(server)
                by {
                };
            };

            if votes.len() >= c.quorum_size {
                assert(votes.len()
                    >= c.servers.len() / 2 + 1);
                assert(is_majority_of(votes, c.servers));
                assert(has_active_election_quorum_after_vote(
                    s_mid,
                    c,
                    voter,
                ));
            } else {
                assert(!has_active_election_quorum_after_vote(
                    s_mid,
                    c,
                    voter,
                )) by {
                    if has_active_election_quorum_after_vote(
                        s_mid,
                        c,
                        voter,
                    ) {
                        assert(is_majority_of(votes, c.servers));
                        assert(votes.len()
                            >= c.servers.len() / 2 + 1);
                        assert(votes.len() >= c.quorum_size);
                        assert(false);
                    }
                };
            }
        }
    }

    /// The Candidate-to-Leader action records the membership phase used
    /// for the election, and its vote set is a quorum for that phase.
    pub proof fn lemma_receive_vote_and_become_leader_records_quorum(
        s: LState,
        s_: LState,
        c: LConstants,
        term: int,
        granted: bool,
        voter: int,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            LReceiveVoteAndBecomeLeader(
                s,
                s_,
                c,
                term,
                granted,
                voter,
                sent_packets,
            ),
            has_active_election_quorum_after_vote(s, c, voter),
        ensures
            has_recorded_election_quorum(s_),
    {
        assert(s_.role is Leader);
        assert(s_.votes_granted
            == s.votes_granted.insert(voter));
        assert(s_.election_membership_phase
            == Some(election_membership_phase_for_state(s, c)));
        assert(is_quorum_for_phase(
            s_.votes_granted,
            election_membership_phase_for_state(s, c),
        ));
    }

    /// The full vote-response handler preserves a valid saved election
    /// certificate, or creates one when the candidate becomes leader.
    pub proof fn lemma_vote_response_preserves_recorded_election_quorum(
        s: LState,
        s_: LState,
        c: LConstants,
        term: int,
        granted: bool,
        voter: int,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            LHandleVoteResponseMsg(
                s, s_, c, term, granted, voter, sent_packets,
            ),
            has_recorded_election_quorum(s),
        ensures
            has_recorded_election_quorum(s_),
    {
        let s_mid = step_down_if_needed(s, term);
        if s_mid.role is Candidate
            && term >= s_mid.current_term
            && granted
            && c.servers.contains(voter)
            && has_active_election_quorum_after_vote(s_mid, c, voter)
        {
            lemma_receive_vote_and_become_leader_records_quorum(
                s_mid, s_, c, term, granted, voter, sent_packets,
            );
        }
    }

    /// Every local Raft step preserves a leader's saved election
    /// certificate. The only step that creates a new leader is the
    /// vote-response path proved above.
    pub proof fn lemma_lnext_preserves_recorded_election_quorum(
        s: LState,
        s_: LState,
        c: LConstants,
    )
        requires
            LNext(s, s_, c),
            has_recorded_election_quorum(s),
        ensures
            has_recorded_election_quorum(s_),
    {
    }

    /// A leader's saved election phase has actual-log provenance when
    /// it is derived from a prefix that was committed by election time.
    pub open spec fn has_recorded_election_log_provenance(
        s: LState,
        c: LConstants,
    ) -> bool {
        if s.role is Leader {
            exists |election_log_len: int| {
                &&& 0 <= election_log_len <= s.log.len()
                &&& s.election_membership_phase == Some(
                    active_membership_phase_from_raft_log(
                        s.log,
                        election_log_len,
                        MembershipPhase::Stable {
                            config: c.servers,
                        },
                    ),
                )
            }
        } else {
            true
        }
    }

    /// A newly elected leader's recorded phase *is* the latest-log phase of the
    /// state it enters. Both promotion actions leave the log untouched and save
    /// the phase derived from it, so the two coincide at the moment of
    /// election.
    ///
    /// This matters because the coincidence is not preserved afterwards: once a
    /// leader appends a Configuration entry its stored phase and its latest-log
    /// phase diverge permanently. Results about newly elected leaders can
    /// therefore rely on this equality, while results about arbitrary leaders
    /// cannot.
    pub proof fn lemma_receive_vote_and_become_leader_records_latest_log_phase(
        s: LState,
        s_: LState,
        c: LConstants,
        vote_term: int,
        vote_granted: bool,
        voter: int,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            LReceiveVoteAndBecomeLeader(
                s, s_, c, vote_term, vote_granted, voter, sent_packets),
        ensures
            s_.election_membership_phase
                == Some(election_membership_phase_for_state(s_, c)),
    {
        assert(s_.log == s.log);
    }

    /// Same fact for the plain Candidate-to-Leader promotion.
    pub proof fn lemma_become_leader_records_latest_log_phase(
        s: LState,
        s_: LState,
        c: LConstants,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            LBecomeLeader(s, s_, c, sent_packets),
        ensures
            s_.election_membership_phase
                == Some(election_membership_phase_for_state(s_, c)),
    {
        assert(s_.log == s.log);
    }

    /// The Candidate-to-Leader action saves the phase derived from the
    /// candidate's current committed actual-log prefix.
    pub proof fn lemma_receive_vote_and_become_leader_records_log_provenance(
        s: LState,
        s_: LState,
        c: LConstants,
        term: int,
        granted: bool,
        voter: int,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            LReceiveVoteAndBecomeLeader(
                s,
                s_,
                c,
                term,
                granted,
                voter,
                sent_packets,
            ),
            0 <= s.commit_index <= s.log.len(),
        ensures
            has_recorded_election_log_provenance(s_, c),
    {
        let election_log_len = s.log.len() as int;
        assert(s_.log == s.log);
        assert(0 <= election_log_len <= s_.log.len());
        assert(s_.election_membership_phase == Some(
            active_membership_phase_from_raft_log(
                s_.log,
                election_log_len,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ),
        ));
    }

    proof fn lemma_lnext_existing_leader_preserves_log_provenance(
        s: LState,
        s_: LState,
        c: LConstants,
    )
        requires
            LNext(s, s_, c),
            s.role is Leader,
            s_.role is Leader,
            has_recorded_election_log_provenance(s, c),
            0 <= s.commit_index <= s.log.len(),
        ensures
            has_recorded_election_log_provenance(s_, c),
    {
        let election_log_len = choose |election_log_len: int| {
            &&& 0 <= election_log_len <= s.log.len()
            &&& s.election_membership_phase == Some(
                active_membership_phase_from_raft_log(
                    s.log,
                    election_log_len,
                    MembershipPhase::Stable {
                        config: c.servers,
                    },
                ),
            )
        };

        assert(election_log_len <= s_.log.len());

        assert forall |index: int|
            0 <= index < election_log_len
            implies s.log[index] == s_.log[index]
        by {
        };

        lemma_equal_committed_raft_prefixes_have_same_active_phase(
            s.log,
            s_.log,
            election_log_len,
            MembershipPhase::Stable {
                config: c.servers,
            },
        );

        assert(s_.election_membership_phase
            == s.election_membership_phase);

        assert(s_.election_membership_phase == Some(
            active_membership_phase_from_raft_log(
                s_.log,
                election_log_len,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ),
        ));
    }

    proof fn lemma_lnext_new_leader_records_log_provenance(
        s: LState,
        s_: LState,
        c: LConstants,
    )
        requires
            LNext(s, s_, c),
            !(s.role is Leader),
            s_.role is Leader,
            0 <= s.commit_index <= s.log.len(),
        ensures
            has_recorded_election_log_provenance(s_, c),
    {
    }

    /// Every local Raft step preserves a leader's actual-log election
    /// provenance. A newly elected leader uses its current commit index;
    /// an existing leader keeps the old prefix as its log grows.
    pub proof fn lemma_lnext_preserves_recorded_election_log_provenance(
        s: LState,
        s_: LState,
        c: LConstants,
    )
        requires
            LNext(s, s_, c),
            has_recorded_election_log_provenance(s, c),
            0 <= s.commit_index <= s.log.len(),
        ensures
            has_recorded_election_log_provenance(s_, c),
    {
        if s_.role is Leader {
            if s.role is Leader {
                lemma_lnext_existing_leader_preserves_log_provenance(
                    s, s_, c,
                );
            } else {
                lemma_lnext_new_leader_records_log_provenance(
                    s, s_, c,
                );
            }
        }
    }

    /// Any two majorities of the same configuration overlap.
    pub proof fn lemma_majorities_intersect(
        quorum1: Set<int>,
        quorum2: Set<int>,
        config: Set<int>,
    )
        requires
            is_majority_of(quorum1, config),
            is_majority_of(quorum2, config),
        ensures
            exists |server: int|
                quorum1.contains(server) && quorum2.contains(server),
    {
        let majority_size = config.len() / 2 + 1;

        assert(quorum1.len() >= majority_size);
        assert(quorum2.len() >= majority_size);
        assert(majority_size + majority_size > config.len());
        assert(quorum1.len() + quorum2.len() > config.len());

        lemma_quorum_intersection(quorum1, quorum2, config);
    }

    /// An old-configuration majority overlaps every joint quorum.
    pub proof fn lemma_old_majority_intersects_joint(
        old_quorum: Set<int>,
        joint_quorum: Set<int>,
        old_config: Set<int>,
        new_config: Set<int>,
    )
        requires
            is_majority_of(old_quorum, old_config),
            is_joint_quorum(joint_quorum, old_config, new_config),
        ensures
            exists |server: int|
                old_quorum.contains(server)
                && joint_quorum.contains(server),
    {
        let joint_old = joint_quorum.intersect(old_config);

        lemma_majorities_intersect(
            old_quorum,
            joint_old,
            old_config,
        );

        let server = choose |server: int|
            old_quorum.contains(server)
            && joint_old.contains(server);

        assert(old_quorum.contains(server));
        assert(joint_old.contains(server));
        assert(joint_quorum.contains(server));
    }

    /// A new-configuration majority overlaps every joint quorum.
    pub proof fn lemma_new_majority_intersects_joint(
        new_quorum: Set<int>,
        joint_quorum: Set<int>,
        old_config: Set<int>,
        new_config: Set<int>,
    )
        requires
            is_majority_of(new_quorum, new_config),
            is_joint_quorum(joint_quorum, old_config, new_config),
        ensures
            exists |server: int|
                new_quorum.contains(server)
                && joint_quorum.contains(server),
    {
        let joint_new = joint_quorum.intersect(new_config);

        lemma_majorities_intersect(
            new_quorum,
            joint_new,
            new_config,
        );

        let server = choose |server: int|
            new_quorum.contains(server)
            && joint_new.contains(server);

        assert(new_quorum.contains(server));
        assert(joint_new.contains(server));
        assert(joint_quorum.contains(server));
    }

    /// Any two joint-consensus quorums overlap.
    pub proof fn lemma_joint_quorums_intersect(
        joint_quorum1: Set<int>,
        joint_quorum2: Set<int>,
        old_config: Set<int>,
        new_config: Set<int>,
    )
        requires
            is_joint_quorum(
                joint_quorum1,
                old_config,
                new_config,
            ),
            is_joint_quorum(
                joint_quorum2,
                old_config,
                new_config,
            ),
        ensures
            exists |server: int|
                joint_quorum1.contains(server)
                && joint_quorum2.contains(server),
    {
        let joint1_old = joint_quorum1.intersect(old_config);
        let joint2_old = joint_quorum2.intersect(old_config);

        lemma_majorities_intersect(
            joint1_old,
            joint2_old,
            old_config,
        );

        let server = choose |server: int|
            joint1_old.contains(server)
            && joint2_old.contains(server);

        assert(joint_quorum1.contains(server));
        assert(joint_quorum2.contains(server));
    }

    /// Any two quorums valid for the same membership phase overlap.
    pub proof fn lemma_phase_quorums_intersect(
        quorum1: Set<int>,
        quorum2: Set<int>,
        phase: MembershipPhase,
    )
        requires
            is_quorum_for_phase(quorum1, phase),
            is_quorum_for_phase(quorum2, phase),
        ensures
            exists |server: int|
                quorum1.contains(server)
                && quorum2.contains(server),
    {
        match phase {
            MembershipPhase::Stable { config } => {
                lemma_majorities_intersect(
                    quorum1,
                    quorum2,
                    config,
                );
            },
            MembershipPhase::Joint {
                old_config,
                new_config,
            } => {
                lemma_joint_quorums_intersect(
                    quorum1,
                    quorum2,
                    old_config,
                    new_config,
                );
            },
        }
    }

    /// A quorum from the old stable phase overlaps a quorum from
    /// the following joint-consensus phase.
    pub proof fn lemma_stable_to_joint_quorums_intersect(
        stable_quorum: Set<int>,
        joint_quorum: Set<int>,
        old_config: Set<int>,
        new_config: Set<int>,
    )
        requires
            is_quorum_for_phase(
                stable_quorum,
                MembershipPhase::Stable {
                    config: old_config,
                },
            ),
            is_quorum_for_phase(
                joint_quorum,
                MembershipPhase::Joint {
                    old_config,
                    new_config,
                },
            ),
        ensures
            exists |server: int|
                stable_quorum.contains(server)
                && joint_quorum.contains(server),
    {
        lemma_old_majority_intersects_joint(
            stable_quorum,
            joint_quorum,
            old_config,
            new_config,
        );
    }

    /// A quorum from the joint-consensus phase overlaps a quorum
    /// from the following new stable phase.
    pub proof fn lemma_joint_to_stable_quorums_intersect(
        joint_quorum: Set<int>,
        stable_quorum: Set<int>,
        old_config: Set<int>,
        new_config: Set<int>,
    )
        requires
            is_quorum_for_phase(
                joint_quorum,
                MembershipPhase::Joint {
                    old_config,
                    new_config,
                },
            ),
            is_quorum_for_phase(
                stable_quorum,
                MembershipPhase::Stable {
                    config: new_config,
                },
            ),
        ensures
            exists |server: int|
                joint_quorum.contains(server)
                && stable_quorum.contains(server),
    {
        lemma_new_majority_intersects_joint(
            stable_quorum,
            joint_quorum,
            old_config,
            new_config,
        );

        let server = choose |server: int|
            stable_quorum.contains(server)
            && joint_quorum.contains(server);

        assert(joint_quorum.contains(server));
        assert(stable_quorum.contains(server));
    }

    /// Every membership phase legally progresses to itself.
    /// This covers ordinary data entries, which do not change membership.
    pub proof fn lemma_phase_progression_reflexive(
        phase: MembershipPhase,
    )
        ensures
            is_legal_phase_progression(
                phase,
                phase,
            ),
    {
        match phase {
            MembershipPhase::Stable { config: _ } => {
            },
            MembershipPhase::Joint {
                old_config: _,
                new_config: _,
            } => {
            },
        }
    }

    /// Determine whether the next committed log entry is legal.
    ///
    /// Data entries are always legal because they preserve membership.
    /// Configuration entries must follow the joint-consensus phase order.
    pub open spec fn is_legal_next_membership_log_entry(
        log: Seq<MembershipLogEntry>,
        committed_len: int,
        initial_phase: MembershipPhase,
        entry: MembershipLogEntry,
    ) -> bool {
        &&& 0 <= committed_len
        &&& committed_len <= log.len()
        &&& match entry {
            MembershipLogEntry::Data { value: _ } => {
                true
            },
            MembershipLogEntry::Configuration { phase } => {
                is_legal_phase_progression(
                    active_membership_phase(
                        log,
                        committed_len,
                        initial_phase,
                    ),
                    phase,
                )
            },
        }
    }

    /// Every entry in the committed prefix follows the legal
    /// joint-consensus membership-phase progression.
    pub open spec fn committed_membership_log_is_well_formed(
        log: Seq<MembershipLogEntry>,
        committed_len: int,
        initial_phase: MembershipPhase,
    ) -> bool
        decreases committed_len
    {
        if committed_len < 0 || committed_len > log.len() {
            false
        } else if committed_len == 0 {
            true
        } else {
            &&& committed_membership_log_is_well_formed(
                log,
                committed_len - 1,
                initial_phase,
            )
            &&& is_legal_next_membership_log_entry(
                log,
                committed_len - 1,
                initial_phase,
                log[committed_len - 1],
            )
        }
    }

    /// An empty committed prefix is a well-formed membership history.
    pub proof fn lemma_empty_committed_membership_log_is_well_formed(
        log: Seq<MembershipLogEntry>,
        initial_phase: MembershipPhase,
    )
        ensures
            committed_membership_log_is_well_formed(
                log,
                0,
                initial_phase,
            ),
    {
    }

    /// A nonempty well-formed committed prefix consists of a
    /// well-formed shorter prefix followed by one legal entry.
    pub proof fn lemma_well_formed_committed_log_decomposes(
        log: Seq<MembershipLogEntry>,
        committed_len: int,
        initial_phase: MembershipPhase,
    )
        requires
            committed_membership_log_is_well_formed(
                log,
                committed_len,
                initial_phase,
            ),
            committed_len > 0,
        ensures
            committed_membership_log_is_well_formed(
                log,
                committed_len - 1,
                initial_phase,
            ),
            is_legal_next_membership_log_entry(
                log,
                committed_len - 1,
                initial_phase,
                log[committed_len - 1],
            ),
    {
    }

    /// In every nonempty well-formed committed history, the final
    /// committed entry produces a legal membership-phase progression.
    pub proof fn lemma_well_formed_committed_log_last_step_is_legal(
        log: Seq<MembershipLogEntry>,
        committed_len: int,
        initial_phase: MembershipPhase,
    )
        requires
            committed_membership_log_is_well_formed(
                log,
                committed_len,
                initial_phase,
            ),
            committed_len > 0,
        ensures
            is_legal_phase_progression(
                active_membership_phase(
                    log,
                    committed_len - 1,
                    initial_phase,
                ),
                active_membership_phase(
                    log,
                    committed_len,
                    initial_phase,
                ),
            ),
    {
        lemma_well_formed_committed_log_decomposes(
            log,
            committed_len,
            initial_phase,
        );

        let previous_phase = active_membership_phase(
            log,
            committed_len - 1,
            initial_phase,
        );

        match log[committed_len - 1] {
            MembershipLogEntry::Data { value: _ } => {
                lemma_phase_progression_reflexive(
                    previous_phase,
                );
            },
            MembershipLogEntry::Configuration { phase } => {
                assert(is_legal_phase_progression(
                    previous_phase,
                    phase,
                ));
            },
        }
    }

    /// Every shorter committed prefix of a well-formed membership
    /// history is itself well formed.
    pub proof fn lemma_well_formed_committed_log_prefix(
        log: Seq<MembershipLogEntry>,
        longer_len: int,
        prefix_len: int,
        initial_phase: MembershipPhase,
    )
        requires
            committed_membership_log_is_well_formed(
                log,
                longer_len,
                initial_phase,
            ),
            0 <= prefix_len <= longer_len,
        ensures
            committed_membership_log_is_well_formed(
                log,
                prefix_len,
                initial_phase,
            ),
        decreases
            longer_len - prefix_len,
    {
        if prefix_len < longer_len {
            assert(longer_len > 0);
            lemma_well_formed_committed_log_decomposes(
                log,
                longer_len,
                initial_phase,
            );
            lemma_well_formed_committed_log_prefix(
                log,
                longer_len - 1,
                prefix_len,
                initial_phase,
            );
        }
    }

    /// Every committed step in an interval of a well-formed history
    /// follows the legal joint-consensus phase order.
    pub proof fn lemma_well_formed_committed_log_interval_is_legal(
        log: Seq<MembershipLogEntry>,
        earlier_len: int,
        later_len: int,
        initial_phase: MembershipPhase,
    )
        requires
            committed_membership_log_is_well_formed(
                log,
                later_len,
                initial_phase,
            ),
            0 <= earlier_len <= later_len,
        ensures
            forall |committed_len: int|
                earlier_len < committed_len <= later_len
                ==> is_legal_phase_progression(
                    active_membership_phase(
                        log,
                        committed_len - 1,
                        initial_phase,
                    ),
                    #[trigger] active_membership_phase(
                        log,
                        committed_len,
                        initial_phase,
                    ),
                ),
    {
        assert forall |committed_len: int|
            earlier_len < committed_len <= later_len
            implies is_legal_phase_progression(
                active_membership_phase(
                    log,
                    committed_len - 1,
                    initial_phase,
                ),
                #[trigger] active_membership_phase(
                    log,
                    committed_len,
                    initial_phase,
                ),
            )
        by {
            lemma_well_formed_committed_log_prefix(
                log,
                later_len,
                committed_len,
                initial_phase,
            );
            lemma_well_formed_committed_log_last_step_is_legal(
                log,
                committed_len,
                initial_phase,
            );
        };
    }

    /// The committed prefix of the actual tagged Raft log is a legal
    /// joint-consensus history when its one-to-one membership projection
    /// is well formed.
    pub open spec fn committed_raft_membership_history_is_well_formed(
        log: Seq<LLogEntry>,
        committed_len: int,
        initial_phase: MembershipPhase,
    ) -> bool {
        &&& 0 <= committed_len <= log.len()
        &&& committed_membership_log_is_well_formed(
            membership_history_from_raft_log(
                log,
                committed_len,
            ),
            committed_len,
            initial_phase,
        )
    }

    /// The next physical Raft-log entry is legal for membership.
    /// Data entries preserve the phase; Configuration entries must
    /// follow the Stable-to-Joint-to-Stable progression.
    pub open spec fn is_legal_next_raft_membership_log_entry(
        log: Seq<LLogEntry>,
        committed_len: int,
        initial_phase: MembershipPhase,
    ) -> bool {
        &&& 0 <= committed_len < log.len()
        &&& match log[committed_len].payload {
            LLogValue::Data { value: _ } => true,
            LLogValue::Configuration { phase } => {
                is_legal_phase_progression(
                    active_membership_phase_from_raft_log(
                        log,
                        committed_len,
                        initial_phase,
                    ),
                    membership_phase_view(phase),
                )
            },
        }
    }

    /// Committing one legal next entry extends a well-formed committed
    /// history of the actual tagged Raft log.
    pub proof fn lemma_legal_next_raft_entry_extends_actual_history(
        log: Seq<LLogEntry>,
        committed_len: int,
        initial_phase: MembershipPhase,
    )
        requires
            committed_raft_membership_history_is_well_formed(
                log,
                committed_len,
                initial_phase,
            ),
            is_legal_next_raft_membership_log_entry(
                log,
                committed_len,
                initial_phase,
            ),
        ensures
            committed_raft_membership_history_is_well_formed(
                log,
                committed_len + 1,
                initial_phase,
            ),
    {
        let history = membership_history_from_raft_log(
            log,
            committed_len,
        );

        let entry = membership_log_entry_view(
            log[committed_len].payload,
        );

        let extended_history = membership_history_from_raft_log(
            log,
            committed_len + 1,
        );

        lemma_membership_history_from_raft_log_len(
            log,
            committed_len,
        );

        assert(extended_history == history.push(entry));

        lemma_projected_membership_history_has_same_active_phase(
            log,
            committed_len,
            initial_phase,
        );

        match log[committed_len].payload {
            LLogValue::Data { value } => {
                assert(entry == (MembershipLogEntry::Data {
                    value,
                }));
                assert(is_legal_next_membership_log_entry(
                    history,
                    committed_len,
                    initial_phase,
                    entry,
                ));
            },
            LLogValue::Configuration { phase } => {
                assert(entry == (MembershipLogEntry::Configuration {
                    phase: membership_phase_view(phase),
                }));
                assert(is_legal_phase_progression(
                    active_membership_phase(
                        history,
                        committed_len,
                        initial_phase,
                    ),
                    membership_phase_view(phase),
                ));
                assert(is_legal_next_membership_log_entry(
                    history,
                    committed_len,
                    initial_phase,
                    entry,
                ));
            },
        }

        lemma_legal_entry_extends_well_formed_committed_log(
            history,
            initial_phase,
            entry,
        );
    }

    /// Committing an interval of individually legal actual-log entries
    /// preserves the full legal joint-consensus membership history.
    pub proof fn lemma_legal_actual_commit_interval_extends_history(
        log: Seq<LLogEntry>,
        earlier_len: int,
        later_len: int,
        initial_phase: MembershipPhase,
    )
        requires
            committed_raft_membership_history_is_well_formed(
                log,
                earlier_len,
                initial_phase,
            ),
            earlier_len <= later_len <= log.len(),
            forall |committed_len: int|
                earlier_len <= committed_len < later_len
                ==> is_legal_next_raft_membership_log_entry(
                    log,
                    committed_len,
                    initial_phase,
                ),
        ensures
            committed_raft_membership_history_is_well_formed(
                log,
                later_len,
                initial_phase,
            ),
        decreases later_len - earlier_len,
    {
        if earlier_len < later_len {
            lemma_legal_next_raft_entry_extends_actual_history(
                log,
                earlier_len,
                initial_phase,
            );

            lemma_legal_actual_commit_interval_extends_history(
                log,
                earlier_len + 1,
                later_len,
                initial_phase,
            );
        }
    }

    /// A suffix containing only Data entries cannot change the active
    /// membership phase between its two prefix lengths.
    pub proof fn lemma_configuration_free_interval_preserves_active_phase(
        log: Seq<LLogEntry>,
        earlier_len: int,
        later_len: int,
        initial_phase: MembershipPhase,
    )
        requires
            0 <= earlier_len <= later_len <= log.len(),
            forall |index: int|
                earlier_len <= index < later_len
                ==> !(log[index].payload is Configuration),
        ensures
            active_membership_phase_from_raft_log(
                log,
                later_len,
                initial_phase,
            ) == active_membership_phase_from_raft_log(
                log,
                earlier_len,
                initial_phase,
            ),
        decreases later_len - earlier_len,
    {
        if earlier_len < later_len {
            assert(!(log[later_len - 1].payload
                is Configuration));

            match log[later_len - 1].payload {
                LLogValue::Data { value: _ } => {
                    lemma_configuration_free_interval_preserves_active_phase(
                        log,
                        earlier_len,
                        later_len - 1,
                        initial_phase,
                    );
                },
                LLogValue::Configuration { phase: _ } => {
                    assert(false);
                },
            }
        }
    }

    /// If at most one Configuration entry is locally uncommitted, deriving
    /// election membership from the full log can move at most one legal
    /// joint-consensus step beyond the committed membership phase.
    pub proof fn lemma_latest_log_election_phase_is_at_most_one_step_ahead(
        s: LState,
        c: LConstants,
    )
        requires
            raft_membership_log_is_well_formed(
                s.log,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ),
            uncommitted_suffix_has_at_most_one_configuration(
                s.log,
                s.commit_index,
            ),
        ensures
            is_legal_phase_progression(
                active_membership_phase_for_state(s, c),
                election_membership_phase_for_state(s, c),
            ),
    {
        let initial_phase = MembershipPhase::Stable {
            config: c.servers,
        };

        if forall |index: int|
            s.commit_index <= index < s.log.len()
            ==> !(s.log[index].payload is Configuration)
        {
            lemma_configuration_free_interval_preserves_active_phase(
                s.log,
                s.commit_index,
                s.log.len() as int,
                initial_phase,
            );
            lemma_phase_progression_reflexive(
                active_membership_phase_for_state(s, c),
            );
        } else {
            let boundary = choose |index: int|
                s.commit_index <= index < s.log.len()
                && s.log[index].payload is Configuration;

            assert forall |index: int|
                s.commit_index <= index < boundary
                implies !(s.log[index].payload is Configuration)
            by {
                if s.log[index].payload is Configuration {
                    assert(index == boundary) by {
                        assert(uncommitted_suffix_has_at_most_one_configuration(
                            s.log,
                            s.commit_index,
                        ));
                    };
                    assert(false);
                }
            };

            assert forall |index: int|
                boundary + 1 <= index < s.log.len()
                implies !(s.log[index].payload is Configuration)
            by {
                if s.log[index].payload is Configuration {
                    assert(index == boundary) by {
                        assert(uncommitted_suffix_has_at_most_one_configuration(
                            s.log,
                            s.commit_index,
                        ));
                    };
                    assert(false);
                }
            };

            lemma_configuration_free_interval_preserves_active_phase(
                s.log,
                s.commit_index,
                boundary,
                initial_phase,
            );
            lemma_adjacent_committed_raft_prefixes_progress_legally(
                s.log,
                boundary + 1,
                initial_phase,
            );
            lemma_configuration_free_interval_preserves_active_phase(
                s.log,
                boundary + 1,
                s.log.len() as int,
                initial_phase,
            );

            assert(active_membership_phase_for_state(s, c)
                == active_membership_phase_from_raft_log(
                    s.log,
                    boundary,
                    initial_phase,
                ));
            assert(election_membership_phase_for_state(s, c)
                == active_membership_phase_from_raft_log(
                    s.log,
                    boundary + 1,
                    initial_phase,
                ));
        }
    }

    /// Interval generalisation of the one-step-ahead result: if a stretch of
    /// the log carries at most one Configuration entry, the phase derived at
    /// the far end is at most one legal joint-consensus step beyond the phase
    /// derived at the near end.
    ///
    /// `lemma_latest_log_election_phase_is_at_most_one_step_ahead` is the
    /// special case `earlier_len = commit_index`, `later_len = log.len()`. The
    /// general form is needed to relate a leader's *election snapshot* phase —
    /// which is what its saved membership phase, and hence its vote quorum, is
    /// measured against — to phases derived at other prefixes.
    pub proof fn lemma_bounded_boundary_interval_progresses_legally(
        log: Seq<LLogEntry>,
        earlier_len: int,
        later_len: int,
        initial_phase: MembershipPhase,
    )
        requires
            raft_membership_log_is_well_formed(log, initial_phase),
            0 <= earlier_len <= later_len <= log.len(),
            forall |a: int, b: int|
                earlier_len <= a < later_len
                && earlier_len <= b < later_len
                && log[a].payload is Configuration
                && log[b].payload is Configuration
                ==> a == b,
        ensures
            is_legal_phase_progression(
                active_membership_phase_from_raft_log(
                    log, earlier_len, initial_phase),
                active_membership_phase_from_raft_log(
                    log, later_len, initial_phase),
            ),
    {
        if forall |index: int|
            earlier_len <= index < later_len
            ==> !(log[index].payload is Configuration)
        {
            lemma_configuration_free_interval_preserves_active_phase(
                log, earlier_len, later_len, initial_phase);
            lemma_phase_progression_reflexive(
                active_membership_phase_from_raft_log(
                    log, earlier_len, initial_phase),
            );
        } else {
            let boundary = choose |index: int|
                earlier_len <= index < later_len
                && log[index].payload is Configuration;

            assert forall |index: int|
                earlier_len <= index < boundary
                implies !(log[index].payload is Configuration)
            by {
                if log[index].payload is Configuration {
                    assert(index == boundary);
                    assert(false);
                }
            };

            assert forall |index: int|
                boundary + 1 <= index < later_len
                implies !(log[index].payload is Configuration)
            by {
                if log[index].payload is Configuration {
                    assert(index == boundary);
                    assert(false);
                }
            };

            lemma_configuration_free_interval_preserves_active_phase(
                log, earlier_len, boundary, initial_phase);
            lemma_adjacent_committed_raft_prefixes_progress_legally(
                log, boundary + 1, initial_phase);
            lemma_configuration_free_interval_preserves_active_phase(
                log, boundary + 1, later_len, initial_phase);
        }
    }

    /// Every prefix of the actual tagged Raft log is a legal
    /// joint-consensus membership history.
    pub open spec fn raft_membership_log_is_well_formed(
        log: Seq<LLogEntry>,
        initial_phase: MembershipPhase,
    ) -> bool {
        forall |prefix_len: int|
            0 <= prefix_len <= log.len()
            ==> committed_raft_membership_history_is_well_formed(
                log,
                prefix_len,
                initial_phase,
            )
    }

    /// The empty physical Raft log has a legal membership history.
    pub proof fn lemma_empty_raft_membership_log_is_well_formed(
        initial_phase: MembershipPhase,
    )
        ensures
            raft_membership_log_is_well_formed(
                Seq::<LLogEntry>::empty(),
                initial_phase,
            ),
    {
        assert forall |prefix_len: int|
            0 <= prefix_len <= Seq::<LLogEntry>::empty().len()
            implies committed_raft_membership_history_is_well_formed(
                Seq::<LLogEntry>::empty(),
                prefix_len,
                initial_phase,
            )
        by {
            assert(prefix_len == 0);
            lemma_empty_committed_raft_membership_history_is_well_formed(
                Seq::<LLogEntry>::empty(),
                initial_phase,
            );
        };
    }

    /// Appending one legal next physical entry preserves legality of
    /// every prefix of the actual Raft log.
    pub proof fn lemma_legal_raft_append_preserves_full_history(
        log: Seq<LLogEntry>,
        entry: LLogEntry,
        initial_phase: MembershipPhase,
    )
        requires
            raft_membership_log_is_well_formed(
                log,
                initial_phase,
            ),
            is_legal_next_raft_membership_log_entry(
                log.push(entry),
                log.len() as int,
                initial_phase,
            ),
        ensures
            raft_membership_log_is_well_formed(
                log.push(entry),
                initial_phase,
            ),
    {
        let extended_log = log.push(entry);

        assert forall |prefix_len: int|
            0 <= prefix_len <= extended_log.len()
            implies committed_raft_membership_history_is_well_formed(
                extended_log,
                prefix_len,
                initial_phase,
            )
        by {
            if prefix_len <= log.len() {
                lemma_membership_history_ignores_uncommitted_raft_append(
                    log,
                    entry,
                    prefix_len,
                );

                assert(committed_raft_membership_history_is_well_formed(
                    log,
                    prefix_len,
                    initial_phase,
                ));
            } else {
                assert(prefix_len == log.len() + 1);

                lemma_membership_history_ignores_uncommitted_raft_append(
                    log,
                    entry,
                    log.len() as int,
                );

                assert(committed_raft_membership_history_is_well_formed(
                    log,
                    log.len() as int,
                    initial_phase,
                ));

                assert(committed_membership_log_is_well_formed(
                    membership_history_from_raft_log(
                        extended_log,
                        log.len() as int,
                    ),
                    log.len() as int,
                    initial_phase,
                ));

                assert(0 <= log.len() <= extended_log.len());

                assert(committed_raft_membership_history_is_well_formed(
                    extended_log,
                    log.len() as int,
                    initial_phase,
                ));

                lemma_legal_next_raft_entry_extends_actual_history(
                    extended_log,
                    log.len() as int,
                    initial_phase,
                );
            }
        };
    }

    /// The guarded leader configuration append is a legal extension
    /// of every actual-log prefix, not only of the committed prefix.
    pub proof fn lemma_append_configuration_preserves_full_history(
        s: LState,
        s_: LState,
        c: LConstants,
        phase: LMembershipPhase,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            LAppendConfigurationEntry(
                s,
                s_,
                c,
                phase,
                sent_packets,
            ),
            raft_membership_log_is_well_formed(
                s.log,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ),
        ensures
            raft_membership_log_is_well_formed(
                s_.log,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ),
    {
        let initial_phase = MembershipPhase::Stable {
            config: c.servers,
        };

        let entry = LLogEntry {
            term: s.current_term,
            value: 0int,
            payload: LLogValue::Configuration {
                phase,
            },
        };

        assert(s_.log == s.log.push(entry));

        lemma_configuration_free_interval_preserves_active_phase(
            s.log,
            s.commit_index,
            s.log.len() as int,
            initial_phase,
        );

        assert(is_legal_phase_progression(
            active_membership_phase_from_raft_log(
                s.log,
                s.log.len() as int,
                initial_phase,
            ),
            membership_phase_view(phase),
        ));

        lemma_uncommitted_raft_entry_does_not_affect_active_phase(
            s.log,
            entry,
            s.log.len() as int,
            initial_phase,
        );

        assert(s.log.push(entry)[s.log.len() as int] == entry);
        assert(s.log.push(entry)[s.log.len() as int].payload
            == (LLogValue::Configuration {
                phase,
            }));

        assert(is_legal_next_raft_membership_log_entry(
            s.log.push(entry),
            s.log.len() as int,
            initial_phase,
        ));

        lemma_legal_raft_append_preserves_full_history(
            s.log,
            entry,
            initial_phase,
        );
    }

    /// An empty committed actual-log prefix is always a legal
    /// membership history.
    pub proof fn lemma_empty_committed_raft_membership_history_is_well_formed(
        log: Seq<LLogEntry>,
        initial_phase: MembershipPhase,
    )
        ensures
            committed_raft_membership_history_is_well_formed(
                log,
                0,
                initial_phase,
            ),
    {
        lemma_empty_committed_membership_log_is_well_formed(
            membership_history_from_raft_log(log, 0),
            initial_phase,
        );
    }

    /// Appending an entry beyond committed_len cannot change whether
    /// the existing committed prefix is a well-formed membership history.
    pub proof fn lemma_uncommitted_entry_does_not_affect_membership_log_well_formed(
        log: Seq<MembershipLogEntry>,
        uncommitted_entry: MembershipLogEntry,
        committed_len: int,
        initial_phase: MembershipPhase,
    )
        requires
            0 <= committed_len,
            committed_len <= log.len(),
        ensures
            committed_membership_log_is_well_formed(
                log.push(uncommitted_entry),
                committed_len,
                initial_phase,
            ) == committed_membership_log_is_well_formed(
                log,
                committed_len,
                initial_phase,
            ),
        decreases committed_len
    {
        if committed_len == 0 {
        } else {
            assert(0 < committed_len);
            assert(0 <= committed_len - 1);
            assert(committed_len - 1 < log.len());

            assert(
                log.push(uncommitted_entry)[committed_len - 1]
                    == log[committed_len - 1]
            );

            lemma_uncommitted_entry_does_not_affect_membership_log_well_formed(
                log,
                uncommitted_entry,
                committed_len - 1,
                initial_phase,
            );

            lemma_uncommitted_entry_does_not_affect_active_phase(
                log,
                uncommitted_entry,
                committed_len - 1,
                initial_phase,
            );

            match log[committed_len - 1] {
                MembershipLogEntry::Data { value: _ } => {
                    assert(
                        is_legal_next_membership_log_entry(
                            log.push(uncommitted_entry),
                            committed_len - 1,
                            initial_phase,
                            log.push(uncommitted_entry)[committed_len - 1],
                        ) == is_legal_next_membership_log_entry(
                            log,
                            committed_len - 1,
                            initial_phase,
                            log[committed_len - 1],
                        )
                    );
                },
                MembershipLogEntry::Configuration { phase: _ } => {
                    assert(
                        is_legal_next_membership_log_entry(
                            log.push(uncommitted_entry),
                            committed_len - 1,
                            initial_phase,
                            log.push(uncommitted_entry)[committed_len - 1],
                        ) == is_legal_next_membership_log_entry(
                            log,
                            committed_len - 1,
                            initial_phase,
                            log[committed_len - 1],
                        )
                    );
                },
            }
        }
    }

    /// Extending a well-formed committed membership history with one
    /// legal committed entry produces another well-formed history.
    pub proof fn lemma_legal_entry_extends_well_formed_committed_log(
        log: Seq<MembershipLogEntry>,
        initial_phase: MembershipPhase,
        entry: MembershipLogEntry,
    )
        requires
            committed_membership_log_is_well_formed(
                log,
                log.len() as int,
                initial_phase,
            ),
            is_legal_next_membership_log_entry(
                log,
                log.len() as int,
                initial_phase,
                entry,
            ),
        ensures
            committed_membership_log_is_well_formed(
                log.push(entry),
                (log.len() + 1) as int,
                initial_phase,
            ),
    {
        lemma_uncommitted_entry_does_not_affect_membership_log_well_formed(
            log,
            entry,
            log.len() as int,
            initial_phase,
        );

        lemma_uncommitted_entry_does_not_affect_active_phase(
            log,
            entry,
            log.len() as int,
            initial_phase,
        );

        assert(
            committed_membership_log_is_well_formed(
                log.push(entry),
                log.len() as int,
                initial_phase,
            )
        );

        assert(
            log.push(entry)[log.len() as int]
                == entry
        );

        match entry {
            MembershipLogEntry::Data { value: _ } => {
                assert(is_legal_next_membership_log_entry(
                    log.push(entry),
                    log.len() as int,
                    initial_phase,
                    entry,
                ));
            },
            MembershipLogEntry::Configuration { phase: _ } => {
                assert(is_legal_next_membership_log_entry(
                    log.push(entry),
                    log.len() as int,
                    initial_phase,
                    entry,
                ));
            },
        }
    }

    /// Committing a legal next entry preserves the legal membership-phase
    /// progression required by joint consensus.
    pub proof fn lemma_legal_committed_entry_preserves_phase_progression(
        log: Seq<MembershipLogEntry>,
        initial_phase: MembershipPhase,
        entry: MembershipLogEntry,
    )
        requires
            is_legal_next_membership_log_entry(
                log,
                log.len() as int,
                initial_phase,
                entry,
            ),
        ensures
            is_legal_phase_progression(
                active_membership_phase(
                    log,
                    log.len() as int,
                    initial_phase,
                ),
                active_membership_phase(
                    log.push(entry),
                    (log.len() + 1) as int,
                    initial_phase,
                ),
            ),
    {
        let previous_phase = active_membership_phase(
            log,
            log.len() as int,
            initial_phase,
        );

        match entry {
            MembershipLogEntry::Data { value } => {
                lemma_committed_data_preserves_active_phase(
                    log,
                    initial_phase,
                    value,
                );

                lemma_phase_progression_reflexive(
                    previous_phase,
                );
            },
            MembershipLogEntry::Configuration { phase } => {
                assert(is_legal_phase_progression(
                    previous_phase,
                    phase,
                ));

                lemma_committed_configuration_becomes_active(
                    log,
                    initial_phase,
                    phase,
                );
            },
        }
    }

    /// Quorums before and after every legal membership-phase
    /// progression share at least one server.
    pub proof fn lemma_legal_phase_progression_quorums_intersect(
        quorum: Set<int>,
        quorum_: Set<int>,
        phase: MembershipPhase,
        phase_: MembershipPhase,
    )
        requires
            is_legal_phase_progression(phase, phase_),
            is_quorum_for_phase(quorum, phase),
            is_quorum_for_phase(quorum_, phase_),
        ensures
            exists |server: int|
                quorum.contains(server)
                && quorum_.contains(server),
    {
        match phase {
            MembershipPhase::Stable { config } => {
                match phase_ {
                    MembershipPhase::Stable { config: config_ } => {
                        assert(config_ == config);
                        lemma_majorities_intersect(
                            quorum,
                            quorum_,
                            config,
                        );
                    },
                    MembershipPhase::Joint {
                        old_config,
                        new_config,
                    } => {
                        assert(old_config == config);
                        lemma_stable_to_joint_quorums_intersect(
                            quorum,
                            quorum_,
                            config,
                            new_config,
                        );
                    },
                }
            },
            MembershipPhase::Joint {
                old_config,
                new_config,
            } => {
                match phase_ {
                    MembershipPhase::Joint {
                        old_config: old_config_,
                        new_config: new_config_,
                    } => {
                        assert(old_config_ == old_config);
                        assert(new_config_ == new_config);
                        lemma_joint_quorums_intersect(
                            quorum,
                            quorum_,
                            old_config,
                            new_config,
                        );
                    },
                    MembershipPhase::Stable { config } => {
                        assert(config == new_config);
                        lemma_joint_to_stable_quorums_intersect(
                            quorum,
                            quorum_,
                            old_config,
                            new_config,
                        );
                    },
                }
            },
        }
    }

    /// Exposing the underlying set does not change the meaning
    /// of the existing count-based helper.
    pub proof fn lemma_replicator_count_matches_set(
        s: LState,
        c: LConstants,
        idx: int,
    )
        ensures
            replicator_count(s, c, idx)
                == replicator_set(s, c, idx).len() as int,
    {
    }

    /// The existing fixed-membership commit guard implies that
    /// the replicating servers form a valid stable-phase quorum.
    pub proof fn lemma_fixed_commit_guard_implies_stable_phase_quorum(
        s: LState,
        c: LConstants,
        idx: int,
    )
        requires
            c.servers.len() > 0,
            c.quorum_size == c.servers.len() / 2 + 1,
            replicator_count(s, c, idx) >= c.quorum_size,
        ensures
            is_quorum_for_phase(
                replicator_set(s, c, idx),
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ),
    {
        let replicators = replicator_set(s, c, idx);

        assert(replicators.subset_of(c.servers)) by {
            assert forall |server: int|
                replicators.contains(server)
                implies c.servers.contains(server)
            by {
            };
        };

        lemma_replicator_count_matches_set(s, c, idx);

        assert(replicators.len() as int >= c.quorum_size);
        assert(replicators.len() >= c.servers.len() / 2 + 1);
        assert(is_majority_of(replicators, c.servers));
        assert(is_quorum_for_phase(
            replicators,
            MembershipPhase::Stable {
                config: c.servers,
            },
        ));
    }

    /// While the committed membership remains the original stable
    /// configuration, the existing fixed replication-count guard is
    /// sufficient for the new active-phase commit guard.
    pub proof fn lemma_fixed_commit_guard_implies_active_stable_quorum(
        s: LState,
        c: LConstants,
        idx: int,
    )
        requires
            c.servers.len() > 0,
            c.quorum_size == c.servers.len() / 2 + 1,
            replicator_count(s, c, idx) >= c.quorum_size,
            active_membership_phase_for_state(s, c)
                == (MembershipPhase::Stable {
                    config: c.servers,
                }),
        ensures
            has_active_commit_quorum(s, c, idx),
    {
        lemma_fixed_commit_guard_implies_stable_phase_quorum(
            s,
            c,
            idx,
        );

        assert(is_quorum_for_phase(
            replicator_set(s, c, idx),
            active_membership_phase_for_state(s, c),
        ));
    }

    /// The existing fixed-quorum commit transition is a valid
    /// active-membership commit transition while membership is stable.
    pub proof fn lemma_fixed_advance_commit_implies_membership_advance_commit(
        s: LState,
        s_: LState,
        c: LConstants,
        new_commit_index: int,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            LAdvanceCommitIndex(
                s,
                s_,
                c,
                new_commit_index,
                sent_packets,
            ),
            c.servers.len() > 0,
            c.quorum_size == c.servers.len() / 2 + 1,
            active_membership_phase_for_state(s, c)
                == (MembershipPhase::Stable {
                    config: c.servers,
                }),
        ensures
            LAdvanceCommitIndexWithMembership(
                s,
                s_,
                c,
                new_commit_index,
                sent_packets,
            ),
    {
        assert(
            LAdvanceCommitIndex(
                s, s_, c, new_commit_index, sent_packets,
            ) == LAdvanceCommitIndexWithMembership(
                s, s_, c, new_commit_index, sent_packets,
            )
        );
    }

    /// While membership is still the original stable configuration,
    /// the fixed composite commit handler is also a valid
    /// dynamic-membership composite commit handler.
    pub proof fn lemma_fixed_try_advance_commit_implies_membership_try_advance_commit(
        s: LState,
        s_: LState,
        c: LConstants,
        new_commit_index: int,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            LTryAdvanceCommitIndex(
                s,
                s_,
                c,
                new_commit_index,
                sent_packets,
            ),
            c.servers.len() > 0,
            c.quorum_size == c.servers.len() / 2 + 1,
            active_membership_phase_for_state(s, c)
                == (MembershipPhase::Stable {
                    config: c.servers,
                }),
        ensures
            LTryAdvanceCommitIndexWithMembership(
                s,
                s_,
                c,
                new_commit_index,
                sent_packets,
            ),
    {
        assert(
            LTryAdvanceCommitIndex(
                s, s_, c, new_commit_index, sent_packets,
            ) == LTryAdvanceCommitIndexWithMembership(
                s, s_, c, new_commit_index, sent_packets,
            )
        );
    }

    /// If every prefix of a Raft log is a legal membership history,
    /// then each existing physical entry is legal at the point where
    /// it was appended.
    pub proof fn lemma_full_history_next_raft_entry_is_legal(
        log: Seq<LLogEntry>,
        index: int,
        initial_phase: MembershipPhase,
    )
        requires
            raft_membership_log_is_well_formed(
                log,
                initial_phase,
            ),
            0 <= index < log.len(),
        ensures
            is_legal_next_raft_membership_log_entry(
                log,
                index,
                initial_phase,
            ),
    {
        let previous_history =
            membership_history_from_raft_log(
                log,
                index,
            );

        let history =
            membership_history_from_raft_log(
                log,
                index + 1,
            );

        let entry = membership_log_entry_view(
            log[index].payload,
        );

        lemma_membership_history_from_raft_log_len(
            log,
            index,
        );

        lemma_membership_history_from_raft_log_index(
            log,
            index + 1,
            index,
        );

        assert(history == previous_history.push(entry));

        assert(committed_raft_membership_history_is_well_formed(
            log,
            index + 1,
            initial_phase,
        ));

        assert(committed_membership_log_is_well_formed(
            history,
            index + 1,
            initial_phase,
        ));

        lemma_well_formed_committed_log_decomposes(
            history,
            index + 1,
            initial_phase,
        );

        lemma_uncommitted_entry_does_not_affect_active_phase(
            previous_history,
            entry,
            index,
            initial_phase,
        );

        lemma_projected_membership_history_has_same_active_phase(
            log,
            index,
            initial_phase,
        );

        match log[index].payload {
            LLogValue::Data { value: _ } => {
            },
            LLogValue::Configuration { phase } => {
                assert(entry
                    == (MembershipLogEntry::Configuration {
                        phase: membership_phase_view(phase),
                    }));
                assert(is_legal_phase_progression(
                    active_membership_phase(
                        history,
                        index,
                        initial_phase,
                    ),
                    membership_phase_view(phase),
                ));
                assert(is_legal_phase_progression(
                    active_membership_phase_from_raft_log(
                        log,
                        index,
                        initial_phase,
                    ),
                    membership_phase_view(phase),
                ));
            },
        }
    }

    /// Advancing a well-formed physical Raft log by one committed entry
    /// performs one legal membership-phase step. Data entries are a
    /// reflexive step; Configuration entries follow the guarded progression.
    pub proof fn lemma_adjacent_committed_raft_prefixes_progress_legally(
        log: Seq<LLogEntry>,
        committed_len: int,
        initial_phase: MembershipPhase,
    )
        requires
            raft_membership_log_is_well_formed(
                log,
                initial_phase,
            ),
            0 < committed_len <= log.len(),
        ensures
            is_legal_phase_progression(
                active_membership_phase_from_raft_log(
                    log,
                    committed_len - 1,
                    initial_phase,
                ),
                active_membership_phase_from_raft_log(
                    log,
                    committed_len,
                    initial_phase,
                ),
            ),
    {
        let previous_phase =
            active_membership_phase_from_raft_log(
                log,
                committed_len - 1,
                initial_phase,
            );

        lemma_full_history_next_raft_entry_is_legal(
            log,
            committed_len - 1,
            initial_phase,
        );

        match log[committed_len - 1].payload {
            LLogValue::Data { value: _ } => {
                assert(active_membership_phase_from_raft_log(
                    log,
                    committed_len,
                    initial_phase,
                ) == previous_phase);

                lemma_phase_progression_reflexive(
                    previous_phase,
                );
            },
            LLogValue::Configuration { phase } => {
                assert(active_membership_phase_from_raft_log(
                    log,
                    committed_len,
                    initial_phase,
                ) == membership_phase_view(phase));
            },
        }
    }

    /// Quorums attached to adjacent committed Raft prefixes overlap.
    /// This is the concrete-log temporal bridge for one physical entry.
    pub proof fn lemma_adjacent_committed_raft_prefix_quorums_intersect(
        log: Seq<LLogEntry>,
        committed_len: int,
        initial_phase: MembershipPhase,
        earlier_quorum: Set<int>,
        later_quorum: Set<int>,
    )
        requires
            raft_membership_log_is_well_formed(
                log,
                initial_phase,
            ),
            0 < committed_len <= log.len(),
            is_quorum_for_phase(
                earlier_quorum,
                active_membership_phase_from_raft_log(
                    log,
                    committed_len - 1,
                    initial_phase,
                ),
            ),
            is_quorum_for_phase(
                later_quorum,
                active_membership_phase_from_raft_log(
                    log,
                    committed_len,
                    initial_phase,
                ),
            ),
        ensures
            exists |server: int|
                earlier_quorum.contains(server)
                && later_quorum.contains(server),
    {
        lemma_adjacent_committed_raft_prefixes_progress_legally(
            log,
            committed_len,
            initial_phase,
        );

        lemma_legal_phase_progression_quorums_intersect(
            earlier_quorum,
            later_quorum,
            active_membership_phase_from_raft_log(
                log,
                committed_len - 1,
                initial_phase,
            ),
            active_membership_phase_from_raft_log(
                log,
                committed_len,
                initial_phase,
            ),
        );
    }

    /// Every physical entry in an interval of a well-formed Raft log
    /// advances membership by one legal step.
    ///
    /// This deliberately describes a chain of adjacent steps rather than
    /// claiming that quorums at arbitrarily distant endpoints overlap.
    pub proof fn lemma_well_formed_raft_log_interval_progresses_legally(
        log: Seq<LLogEntry>,
        earlier_len: int,
        later_len: int,
        initial_phase: MembershipPhase,
    )
        requires
            raft_membership_log_is_well_formed(
                log,
                initial_phase,
            ),
            0 <= earlier_len <= later_len <= log.len(),
        ensures
            forall |committed_len: int|
                earlier_len < committed_len <= later_len
                ==> is_legal_phase_progression(
                    active_membership_phase_from_raft_log(
                        log,
                        committed_len - 1,
                        initial_phase,
                    ),
                    #[trigger] active_membership_phase_from_raft_log(
                        log,
                        committed_len,
                        initial_phase,
                    ),
                ),
    {
        assert forall |committed_len: int|
            earlier_len < committed_len <= later_len
            implies is_legal_phase_progression(
                active_membership_phase_from_raft_log(
                    log,
                    committed_len - 1,
                    initial_phase,
                ),
                #[trigger] active_membership_phase_from_raft_log(
                    log,
                    committed_len,
                    initial_phase,
                ),
            )
        by {
            lemma_adjacent_committed_raft_prefixes_progress_legally(
                log,
                committed_len,
                initial_phase,
            );
        };
    }

    /// A legal commit-index advancement changes membership by at most one
    /// phase step.
    ///
    /// The boundary guard makes every entry before the final newly committed
    /// entry Data, so that prefix preserves the old phase. The final entry is
    /// then either Data (a reflexive step) or one legal Configuration entry.
    pub proof fn lemma_commit_boundary_progresses_membership_once(
        log: Seq<LLogEntry>,
        old_committed_len: int,
        new_committed_len: int,
        initial_phase: MembershipPhase,
    )
        requires
            raft_membership_log_is_well_formed(
                log,
                initial_phase,
            ),
            commit_interval_stops_at_first_configuration(
                log,
                old_committed_len,
                new_committed_len,
            ),
        ensures
            is_legal_phase_progression(
                active_membership_phase_from_raft_log(
                    log,
                    old_committed_len,
                    initial_phase,
                ),
                active_membership_phase_from_raft_log(
                    log,
                    new_committed_len,
                    initial_phase,
                ),
            ),
    {
        lemma_configuration_free_interval_preserves_active_phase(
            log,
            old_committed_len,
            new_committed_len - 1,
            initial_phase,
        );

        lemma_adjacent_committed_raft_prefixes_progress_legally(
            log,
            new_committed_len,
            initial_phase,
        );

        assert(
            active_membership_phase_from_raft_log(
                log,
                new_committed_len - 1,
                initial_phase,
            ) == active_membership_phase_from_raft_log(
                log,
                old_committed_len,
                initial_phase,
            )
        );
    }

    /// Quorums used immediately before and after one legal commit-index
    /// advancement overlap, even when that step commits a Configuration
    /// entry as its final entry.
    pub proof fn lemma_commit_boundary_quorums_intersect(
        log: Seq<LLogEntry>,
        old_committed_len: int,
        new_committed_len: int,
        initial_phase: MembershipPhase,
        old_quorum: Set<int>,
        new_quorum: Set<int>,
    )
        requires
            raft_membership_log_is_well_formed(
                log,
                initial_phase,
            ),
            commit_interval_stops_at_first_configuration(
                log,
                old_committed_len,
                new_committed_len,
            ),
            is_quorum_for_phase(
                old_quorum,
                active_membership_phase_from_raft_log(
                    log,
                    old_committed_len,
                    initial_phase,
                ),
            ),
            is_quorum_for_phase(
                new_quorum,
                active_membership_phase_from_raft_log(
                    log,
                    new_committed_len,
                    initial_phase,
                ),
            ),
        ensures
            exists |server: int|
                old_quorum.contains(server)
                && new_quorum.contains(server),
    {
        lemma_commit_boundary_progresses_membership_once(
            log,
            old_committed_len,
            new_committed_len,
            initial_phase,
        );

        lemma_legal_phase_progression_quorums_intersect(
            old_quorum,
            new_quorum,
            active_membership_phase_from_raft_log(
                log,
                old_committed_len,
                initial_phase,
            ),
            active_membership_phase_from_raft_log(
                log,
                new_committed_len,
                initial_phase,
            ),
        );
    }

    /// The concrete logical commit action changes the active membership by
    /// at most one legal joint-consensus step.
    pub proof fn lemma_advance_commit_index_progresses_membership_once(
        s: LState,
        s_: LState,
        c: LConstants,
        new_commit_index: int,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            LAdvanceCommitIndex(
                s,
                s_,
                c,
                new_commit_index,
                sent_packets,
            ),
            raft_membership_log_is_well_formed(
                s.log,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ),
        ensures
            is_legal_phase_progression(
                active_membership_phase_for_state(s, c),
                active_membership_phase_for_state(s_, c),
            ),
    {
        let initial_phase = MembershipPhase::Stable {
            config: c.servers,
        };

        assert(s_.log == s.log);
        assert(s_.commit_index == new_commit_index);

        lemma_commit_boundary_progresses_membership_once(
            s.log,
            s.commit_index,
            new_commit_index,
            initial_phase,
        );

        assert(
            active_membership_phase_for_state(s, c)
                == active_membership_phase_from_raft_log(
                    s.log,
                    s.commit_index,
                    initial_phase,
                )
        );

        assert(
            active_membership_phase_for_state(s_, c)
                == active_membership_phase_from_raft_log(
                    s.log,
                    new_commit_index,
                    initial_phase,
                )
        );
    }

    /// The composite commit attempt either stutters or performs the same
    /// one-step legal membership progression as LAdvanceCommitIndex.
    pub proof fn lemma_try_advance_commit_index_progresses_membership_once(
        s: LState,
        s_: LState,
        c: LConstants,
        new_commit_index: int,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            LTryAdvanceCommitIndex(
                s,
                s_,
                c,
                new_commit_index,
                sent_packets,
            ),
            raft_membership_log_is_well_formed(
                s.log,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ),
        ensures
            is_legal_phase_progression(
                active_membership_phase_for_state(s, c),
                active_membership_phase_for_state(s_, c),
            ),
    {
        if !(s.role is Leader)
            || new_commit_index <= s.commit_index
            || !has_active_commit_quorum(
                s,
                c,
                new_commit_index,
            )
            || !commit_interval_stops_at_first_configuration(
                s.log,
                s.commit_index,
                new_commit_index,
            )
        {
            assert(s_ == s);
            lemma_phase_progression_reflexive(
                active_membership_phase_for_state(s, c),
            );
        } else {
            assert(LAdvanceCommitIndex(
                s,
                s_,
                c,
                new_commit_index,
                sent_packets,
            ));

            lemma_advance_commit_index_progresses_membership_once(
                s,
                s_,
                c,
                new_commit_index,
                sent_packets,
            );
        }
    }

    /// If an interval contains only Data entries, its endpoint membership
    /// phases are equal and any valid endpoint quorums overlap.
    pub proof fn lemma_configuration_free_raft_interval_quorums_intersect(
        log: Seq<LLogEntry>,
        earlier_len: int,
        later_len: int,
        initial_phase: MembershipPhase,
        earlier_quorum: Set<int>,
        later_quorum: Set<int>,
    )
        requires
            0 <= earlier_len <= later_len <= log.len(),
            forall |index: int|
                earlier_len <= index < later_len
                ==> !(log[index].payload is Configuration),
            is_quorum_for_phase(
                earlier_quorum,
                active_membership_phase_from_raft_log(
                    log,
                    earlier_len,
                    initial_phase,
                ),
            ),
            is_quorum_for_phase(
                later_quorum,
                active_membership_phase_from_raft_log(
                    log,
                    later_len,
                    initial_phase,
                ),
            ),
        ensures
            exists |server: int|
                earlier_quorum.contains(server)
                && later_quorum.contains(server),
    {
        lemma_configuration_free_interval_preserves_active_phase(
            log,
            earlier_len,
            later_len,
            initial_phase,
        );

        let phase = active_membership_phase_from_raft_log(
            log,
            earlier_len,
            initial_phase,
        );

        assert(active_membership_phase_from_raft_log(
            log,
            later_len,
            initial_phase,
        ) == phase);

        lemma_phase_quorums_intersect(
            earlier_quorum,
            later_quorum,
            phase,
        );
    }

    /// A normal client command is a Data entry, so appending it cannot
    /// violate the legal Stable-to-Joint-to-Stable membership order.
    pub proof fn lemma_client_request_preserves_full_membership_history(
        s: LState,
        s_: LState,
        c: LConstants,
        value: int,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            LClientRequest(
                s,
                s_,
                c,
                value,
                sent_packets,
            ),
            raft_membership_log_is_well_formed(
                s.log,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ),
        ensures
            raft_membership_log_is_well_formed(
                s_.log,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ),
    {
        let initial_phase = MembershipPhase::Stable {
            config: c.servers,
        };

        let entry = LLogEntry {
            term: s.current_term,
            value,
            payload: LLogValue::Data {
                value,
            },
        };

        assert(s_.log == s.log.push(entry));
        assert(s_.log[s.log.len() as int] == entry);
        assert(is_legal_next_raft_membership_log_entry(
            s_.log,
            s.log.len() as int,
            initial_phase,
        ));

        lemma_legal_raft_append_preserves_full_history(
            s.log,
            entry,
            initial_phase,
        );
    }

    /// A follower append preserves full membership-history legality
    /// once provenance reasoning has established that the received
    /// entry is a legal next entry for the follower's prefix.
    pub proof fn lemma_follower_append_preserves_full_membership_history_if_legal(
        s: LState,
        s_: LState,
        c: LConstants,
        ae_term: int,
        ae_leader: int,
        ae_prev_index: int,
        ae_prev_term: int,
        ae_value: int,
        ae_payload: LLogValue,
        ae_has_entry: bool,
        ae_leader_commit: int,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            LFollowerAppendEntries(
                s,
                s_,
                c,
                ae_term,
                ae_leader,
                ae_prev_index,
                ae_prev_term,
                ae_value,
                ae_payload,
                ae_has_entry,
                ae_leader_commit,
                sent_packets,
            ),
            raft_membership_log_is_well_formed(
                s.log,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ),
            ae_has_entry ==> is_legal_next_raft_membership_log_entry(
                s_.log,
                s.log.len() as int,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ),
        ensures
            raft_membership_log_is_well_formed(
                s_.log,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ),
    {
        if ae_has_entry {
            let entry = LLogEntry {
                term: ae_term,
                value: ae_value,
                payload: ae_payload,
            };

            assert(s_.log == s.log.push(entry));
            lemma_legal_raft_append_preserves_full_history(
                s.log,
                entry,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            );
        } else {
            assert(s_.log == s.log);
        }
    }

    /// If two logs have the same prefix and the same tagged payload at
    /// the next index, legality of that next entry transfers between
    /// the logs. Terms and legacy scalar values do not affect membership.
    pub proof fn lemma_equal_prefix_and_payload_transfer_next_entry_legality(
        source_log: Seq<LLogEntry>,
        target_log: Seq<LLogEntry>,
        index: int,
        initial_phase: MembershipPhase,
    )
        requires
            raft_membership_log_is_well_formed(
                source_log,
                initial_phase,
            ),
            0 <= index < source_log.len(),
            index < target_log.len(),
            forall |prefix_index: int|
                0 <= prefix_index < index
                ==> source_log[prefix_index]
                    == target_log[prefix_index],
            source_log[index].payload
                == target_log[index].payload,
        ensures
            is_legal_next_raft_membership_log_entry(
                target_log,
                index,
                initial_phase,
            ),
    {
        lemma_full_history_next_raft_entry_is_legal(
            source_log,
            index,
            initial_phase,
        );

        lemma_equal_committed_raft_prefixes_have_same_active_phase(
            source_log,
            target_log,
            index,
            initial_phase,
        );

        match target_log[index].payload {
            LLogValue::Data { value: _ } => {
            },
            LLogValue::Configuration { phase } => {
                assert(source_log[index].payload
                    == (LLogValue::Configuration {
                        phase,
                    }));

                assert(is_legal_phase_progression(
                    active_membership_phase_from_raft_log(
                        source_log,
                        index,
                        initial_phase,
                    ),
                    membership_phase_view(phase),
                ));

                assert(is_legal_phase_progression(
                    active_membership_phase_from_raft_log(
                        target_log,
                        index,
                        initial_phase,
                    ),
                    membership_phase_view(phase),
                ));
            },
        }
    }

    /// Advancing commit_index never changes the physical Raft log,
    /// so it preserves legality of every log prefix.
    pub proof fn lemma_try_advance_commit_preserves_full_membership_history(
        s: LState,
        s_: LState,
        c: LConstants,
        new_commit_index: int,
        sent_packets: Seq<LRaftMessage>,
    )
        requires
            LTryAdvanceCommitIndex(
                s,
                s_,
                c,
                new_commit_index,
                sent_packets,
            ),
            raft_membership_log_is_well_formed(
                s.log,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ),
        ensures
            raft_membership_log_is_well_formed(
                s_.log,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ),
    {
        assert(s_.log == s.log);
    }

    /// Every protocol action preserves all physical log entries that were
    /// already present before the action. An action may append one entry,
    /// but it never rewrites the existing prefix in this Raft model.
    pub proof fn lemma_lnext_preserves_existing_raft_log_prefix(
        s: LState,
        s_: LState,
        c: LConstants,
    )
        requires
            LNext(s, s_, c),
        ensures
            s.log.len() <= s_.log.len(),
            forall |index: int|
                0 <= index < s.log.len()
                ==> s_.log[index] == s.log[index],
    {
    }

    /// No protocol action moves a server's commit index backward.
    /// The old commit bound is needed for the follower AppendEntries branch,
    /// whose new index is capped by the (possibly extended) log length.
    pub proof fn lemma_lnext_commit_index_nondecreasing_for_membership(
        s: LState,
        s_: LState,
        c: LConstants,
    )
        requires
            LNext(s, s_, c),
            0 <= s.commit_index <= s.log.len(),
        ensures
            s.commit_index <= s_.commit_index,
    {
    }

    /// Across any one local Raft transition, the newly committed portion of
    /// the post-state log follows a legal Stable-to-Joint-to-Stable chain.
    ///
    /// This theorem deliberately permits a follower to learn several already
    /// committed configuration changes from a leader in one AppendEntries
    /// step. It proves legality of every adjacent boundary in that interval;
    /// it does not incorrectly claim that the two distant endpoint quorums
    /// must overlap directly.
    pub proof fn lemma_lnext_newly_committed_membership_interval_is_legal(
        s: LState,
        s_: LState,
        c: LConstants,
    )
        requires
            LNext(s, s_, c),
            0 <= s.commit_index <= s.log.len(),
            0 <= s_.commit_index <= s_.log.len(),
            raft_membership_log_is_well_formed(
                s_.log,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ),
        ensures
            s.commit_index <= s_.commit_index,
            active_membership_phase_from_raft_log(
                s.log,
                s.commit_index,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ) == active_membership_phase_from_raft_log(
                s_.log,
                s.commit_index,
                MembershipPhase::Stable {
                    config: c.servers,
                },
            ),
            forall |committed_len: int|
                s.commit_index < committed_len
                    <= s_.commit_index
                ==> is_legal_phase_progression(
                    active_membership_phase_from_raft_log(
                        s_.log,
                        committed_len - 1,
                        MembershipPhase::Stable {
                            config: c.servers,
                        },
                    ),
                    #[trigger] active_membership_phase_from_raft_log(
                        s_.log,
                        committed_len,
                        MembershipPhase::Stable {
                            config: c.servers,
                        },
                    ),
                ),
    {
        let initial_phase = MembershipPhase::Stable {
            config: c.servers,
        };

        lemma_lnext_preserves_existing_raft_log_prefix(
            s,
            s_,
            c,
        );

        lemma_lnext_commit_index_nondecreasing_for_membership(
            s,
            s_,
            c,
        );

        assert forall |index: int|
            0 <= index < s.commit_index
            implies s.log[index] == s_.log[index]
        by {
            assert(index < s.log.len());
        };

        lemma_equal_committed_raft_prefixes_have_same_active_phase(
            s.log,
            s_.log,
            s.commit_index,
            initial_phase,
        );

        lemma_well_formed_raft_log_interval_progresses_legally(
            s_.log,
            s.commit_index,
            s_.commit_index,
            initial_phase,
        );
    }

    /// A valid configuration-commit certificate's saved quorum overlaps every
    /// quorum for the membership phase installed by its Configuration entry.
    /// This is the local handoff from Stable-old to Joint, or from Joint to
    /// Stable-new.
    pub proof fn lemma_configuration_certificate_quorum_intersects_resulting_phase(
        certificate: ConfigurationCommitCertificate,
        witness_log: Seq<LLogEntry>,
        initial_phase: MembershipPhase,
        resulting_quorum: Set<int>,
    )
        requires
            configuration_commit_certificate_matches_log(
                certificate,
                witness_log,
                initial_phase,
            ),
            match certificate.entry.payload {
                LLogValue::Configuration { phase } => {
                    is_quorum_for_phase(
                        resulting_quorum,
                        membership_phase_view(phase),
                    )
                },
                LLogValue::Data { value: _ } => false,
            },
        ensures
            exists |server: int|
                certificate.quorum.contains(server)
                && resulting_quorum.contains(server),
    {
        match certificate.entry.payload {
            LLogValue::Configuration { phase } => {
                assert(is_quorum_for_phase(
                    certificate.quorum,
                    certificate.governing_phase,
                ));
                assert(is_legal_phase_progression(
                    certificate.governing_phase,
                    membership_phase_view(phase),
                ));
                lemma_legal_phase_progression_quorums_intersect(
                    certificate.quorum,
                    resulting_quorum,
                    certificate.governing_phase,
                    membership_phase_view(phase),
                );
            },
            LLogValue::Data { value: _ } => {
                assert(false);
            },
        }
    }
}
