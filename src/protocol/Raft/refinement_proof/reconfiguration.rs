use crate::common::collections::sets::lemma_quorum_intersection;
use crate::protocol::Raft::membership::*;
use crate::protocol::Raft::raft::{
    LAdvanceCommitIndex,
    LAdvanceCommitIndexWithMembership,
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

    /// A leader appends a legal membership configuration entry.
    ///
    /// The entry is initially uncommitted, so it does not immediately
    /// change either active membership or application-visible output.
    pub open spec fn LAppendConfigurationEntry(
        s: LState,
        s_: LState,
        c: LConstants,
        phase: LMembershipPhase,
        sent_packets: Seq<LRaftMessage>,
    ) -> bool {
        let initial_phase = MembershipPhase::Stable {
            config: c.servers,
        };

        let current_phase = active_membership_phase_from_raft_log(
            s.log,
            s.commit_index,
            initial_phase,
        );

        let requested_phase = membership_phase_view(phase);

        &&& s.role is Leader
        &&& 0 <= s.commit_index
        &&& s.commit_index <= s.log.len()
        &&& is_legal_phase_progression(
            current_phase,
            requested_phase,
        )
        &&& s_.current_term == s.current_term
        &&& s_.role == s.role
        &&& s_.has_voted == s.has_voted
        &&& s_.voted_for == s.voted_for
        &&& s_.log == s.log.push(
            LLogEntry {
                term: s.current_term,
                value: 0int,
                payload: LLogValue::Configuration {
                    phase,
                },
            },
        )
        &&& s_.commit_index == s.commit_index
        &&& s_.votes_granted == s.votes_granted
        &&& s_.match_index == s.match_index
        &&& s_.next_index == s.next_index
        &&& sent_packets == Seq::<LRaftMessage>::empty()
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
            c.servers.finite(),
            c.servers.len() > 0,
            c.quorum_size == c.servers.len() / 2 + 1,
            s.votes_granted.subset_of(c.servers),
            s.votes_granted.len() >= c.quorum_size,
            active_membership_phase_for_state(s, c)
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
            c.servers.finite(),
            c.servers.len() > 0,
            c.quorum_size == c.servers.len() / 2 + 1,
            s.votes_granted.subset_of(c.servers),
            active_membership_phase_for_state(s, c)
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
            c.servers.finite(),
            c.servers.len() > 0,
            c.quorum_size == c.servers.len() / 2 + 1,
            step_down_if_needed(s, term).votes_granted
                .subset_of(c.servers),
            active_membership_phase_for_state(
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
            == Some(active_membership_phase_for_state(s, c)));
        assert(is_quorum_for_phase(
            s_.votes_granted,
            active_membership_phase_for_state(s, c),
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

    /// Legal membership-phase progression for joint consensus.
    ///
    /// A stable configuration may remain stable or enter a joint phase
    /// whose old configuration matches it. A joint phase may remain
    /// unchanged or finish at its new configuration.
    pub open spec fn is_legal_phase_progression(
        phase: MembershipPhase,
        phase_: MembershipPhase,
    ) -> bool {
        match phase {
            MembershipPhase::Stable { config } => {
                match phase_ {
                    MembershipPhase::Stable { config: config_ } => {
                        config_ == config
                    },
                    MembershipPhase::Joint {
                        old_config,
                        new_config: _,
                    } => {
                        old_config == config
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
                        old_config_ == old_config
                            && new_config_ == new_config
                    },
                    MembershipPhase::Stable { config } => {
                        config == new_config
                    },
                }
            },
        }
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
            c.servers.finite(),
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
            c.servers.finite(),
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
}
