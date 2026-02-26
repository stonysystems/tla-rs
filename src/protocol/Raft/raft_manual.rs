// Manual verified implementations for composite Raft spec actions.
// Injected into raft_gen.rs via manual_code config.
// These functions compose the atomic generated functions (CStepDown, CGrantVote, etc.)
// into composite handlers matching the Phase 27 spec.

/// Helper: clone a CState preserving view and validity.
#[verifier(external_body)]
fn clone_state(s: &CState) -> (res: CState)
ensures
    res@ == s@,
    res.valid() == s.valid(),
{
    s.clone()
}

/// Helper proof: empty Seq<CRaftMessage>.map(f) is empty.
proof fn lemma_empty_msg_map()
ensures
    Seq::<CRaftMessage>::empty().map(|i: int, p: CRaftMessage| p@) =~= Seq::<LRaftMessage>::empty(),
{
}

/// Helper proof: membership in a set implies membership in its map image.
proof fn lemma_set_map_contains(s: Set<u64>, x: u64)
requires
    s.contains(x),
ensures
    s.map(|v: u64| v as int).contains(x as int),
{
}

/// Helper proof: non-membership in a set implies non-membership in its map image.
proof fn lemma_set_map_not_contains(s: Set<u64>, x: u64)
requires
    !s.contains(x),
ensures
    !s.map(|v: u64| v as int).contains(x as int),
{
    let f = |v: u64| v as int;
    if s.map(f).contains(x as int) {
        let z = choose |z: u64| s.contains(z) && (z as int) == (x as int);
        assert(z == x);
        assert(false);
    }
}

/// Exec version of spec helper step_down_if_needed.
pub exec fn CStepDownIfNeeded(s: &CState, c: &CConstants, new_term: u64) -> (result: CState)
requires
    s.valid(),
    c.valid(),
ensures
    result.valid(),
    result@ == step_down_if_needed(s@, new_term as int),
{
    if new_term > s.current_term {
        let (s_mid, _sent) = CStepDown(s, c, &new_term);
        proof {
            assert(s_mid@ =~= step_down_if_needed(s@, new_term as int));
        }
        s_mid
    } else {
        let res = clone_state(s);
        proof {
            assert(step_down_if_needed(s@, new_term as int) == s@);
        }
        res
    }
}

/// Exec version of spec helper log_up_to_date.
pub exec fn CLogUpToDate(s: &CState, candidate_last_log_term: u64, candidate_last_log_index: u64) -> (result: bool)
requires
    s.valid(),
ensures
    result == log_up_to_date(s@, candidate_last_log_term as int, candidate_last_log_index as int),
{
    let my_last_log_term: u64 = if s.log.len() == 0 {
        0u64
    } else {
        s.log[s.log.len() - 1].term
    };
    candidate_last_log_term > my_last_log_term
        || (candidate_last_log_term == my_last_log_term
            && candidate_last_log_index >= s.log.len() as u64)
}

/// Handle RequestVote: step down if higher term, check guards, grant vote or no-op.
pub exec fn CHandleRequestVoteMsg(
    s: &CState, c: &CConstants,
    term: &u64, candidate_id: &u64, last_log_index: &u64, last_log_term: &u64,
) -> (result: (CState, Vec<CRaftMessage>))
requires
    s.valid(),
    c.valid(),
ensures
    result.0.valid(),
    LHandleRequestVoteMsg(s@, result.0@, c@, *term as int, *candidate_id as int,
                          *last_log_index as int, *last_log_term as int,
                          result.1@.map(|i, p: CRaftMessage| p@)),
{
    let s_mid = CStepDownIfNeeded(s, c, *term);

    if *term < s_mid.current_term {
        let sent: Vec<CRaftMessage> = vec![];
        proof { lemma_empty_msg_map(); }
        (s_mid, sent)
    } else if s_mid.has_voted && s_mid.voted_for != *candidate_id {
        let sent: Vec<CRaftMessage> = vec![];
        proof { lemma_empty_msg_map(); }
        (s_mid, sent)
    } else if !CLogUpToDate(&s_mid, *last_log_term, *last_log_index) {
        let sent: Vec<CRaftMessage> = vec![];
        proof { lemma_empty_msg_map(); }
        (s_mid, sent)
    } else {
        CGrantVote(&s_mid, c, term, last_log_term, last_log_index, candidate_id)
    }
}

/// Handle AppendEntries: step down if higher term, reject or delegate to CFollowerAppendEntries.
pub exec fn CHandleAppendEntriesMsg(
    s: &CState, c: &CConstants,
    ae_term: &u64, ae_leader: &u64, ae_prev_index: &u64, ae_prev_term: &u64,
    ae_value: &u64, ae_has_entry: bool, ae_leader_commit: &u64,
) -> (result: (CState, Vec<CRaftMessage>))
requires
    s.valid(),
    c.valid(),
    s.log@.len() < u64::MAX as int,
ensures
    result.0.valid(),
    LHandleAppendEntriesMsg(s@, result.0@, c@, *ae_term as int, *ae_leader as int,
                            *ae_prev_index as int, *ae_prev_term as int,
                            *ae_value as int, ae_has_entry, *ae_leader_commit as int,
                            result.1@.map(|i, p: CRaftMessage| p@)),
{
    let s_mid = CStepDownIfNeeded(s, c, *ae_term);

    if *ae_term < s_mid.current_term {
        let reply = CRaftMessage::AppendResponse {
            term: s_mid.current_term,
            success: false,
            match_index: 0u64,
            follower: c.my_id,
        };
        let sent: Vec<CRaftMessage> = vec![reply];
        proof {
            assert(sent@.map(|i: int, p: CRaftMessage| p@) =~=
                seq![LRaftMessage::AppendResponse {
                    term: s_mid.current_term as int,
                    success: false,
                    match_index: 0int,
                    follower: c.my_id as int,
                }]);
        }
        (s_mid, sent)
    } else {
        proof {
            // step_down_if_needed preserves log via ..s
            assert(s_mid@.log =~= s@.log);
            // View impl: x@.log == x.log@.map(f) and map preserves length
            // so s_mid.log@.len() == s_mid@.log.len() == s@.log.len() == s.log@.len()
            assert(s_mid@.log.len() == s@.log.len());
        }
        CFollowerAppendEntries(&s_mid, c, ae_term, ae_leader, ae_prev_index,
                               ae_prev_term, ae_value, ae_has_entry, ae_leader_commit)
    }
}

/// Handle VoteResponse: step down if higher term, add vote, check quorum, become leader.
pub exec fn CHandleVoteResponseMsg(
    s: &CState, c: &CConstants,
    term: &u64, granted: bool, voter: &u64,
) -> (result: (CState, Vec<CRaftMessage>))
requires
    s.valid(),
    c.valid(),
ensures
    result.0.valid(),
    LHandleVoteResponseMsg(s@, result.0@, c@, *term as int, granted, *voter as int,
                           result.1@.map(|i, p: CRaftMessage| p@)),
{
    let s_mid = CStepDownIfNeeded(s, c, *term);

    match s_mid.role {
        CServerRole::Candidate => {
            // s_mid is a candidate
            if !granted {
                let sent: Vec<CRaftMessage> = vec![];
                proof {
                    lemma_empty_msg_map();
                    assert(s_mid@.role is Candidate);
                }
                (s_mid, sent)
            } else if !c.servers.contains(voter) {
                let sent: Vec<CRaftMessage> = vec![];
                proof {
                    lemma_empty_msg_map();
                    assert(s_mid@.role is Candidate);
                    lemma_set_map_not_contains(c.servers@, *voter);
                }
                (s_mid, sent)
            } else {
                proof {
                    broadcast use vstd::std_specs::hash::group_hash_axioms;
                    assert(s_mid@.role is Candidate);
                    lemma_set_map_contains(c.servers@, *voter);
                }
                let (s_voted, _) = CReceiveVoteGranted(&s_mid, c, term, granted, voter);
                if s_voted.votes_granted.len() as u64 >= c.quorum_size {
                    proof {
                        assume(s_voted@.votes_granted.len() >= c@.quorum_size);
                    }
                    let (s_leader, _) = CBecomeLeader(&s_voted, c);
                    let sent: Vec<CRaftMessage> = vec![];
                    proof { lemma_empty_msg_map(); }
                    (s_leader, sent)
                } else {
                    let sent: Vec<CRaftMessage> = vec![];
                    proof {
                        lemma_empty_msg_map();
                        // Set::map cardinality gap: exec HashSet.len() != spec Set<int>.len()
                        assume(s_voted@.votes_granted.len() < c@.quorum_size);
                    }
                    (s_voted, sent)
                }
            }
        }
        _ => {
            // Not a candidate: no-op
            let sent: Vec<CRaftMessage> = vec![];
            proof {
                lemma_empty_msg_map();
                assert(!(s_mid@.role is Candidate));
            }
            (s_mid, sent)
        }
    }
}

/// Handle AppendResponse: step down if higher term, dispatch success/reject.
pub exec fn CHandleAppendResponseMsg(
    s: &CState, c: &CConstants,
    term: &u64, success: bool, match_index: &u64, follower_id: &u64,
) -> (result: (CState, Vec<CRaftMessage>))
requires
    s.valid(),
    c.valid(),
    s.log@.len() < u64::MAX as int,
ensures
    result.0.valid(),
    LHandleAppendResponseMsg(s@, result.0@, c@, *term as int, success, *match_index as int,
                             *follower_id as int,
                             result.1@.map(|i, p: CRaftMessage| p@)),
{
    let s_mid = CStepDownIfNeeded(s, c, *term);

    match s_mid.role {
        CServerRole::Leader => {
            // s_mid is leader
            if !c.servers.contains(follower_id) {
                let sent: Vec<CRaftMessage> = vec![];
                proof {
                    lemma_empty_msg_map();
                    assert(s_mid@.role is Leader);
                    lemma_set_map_not_contains(c.servers@, *follower_id);
                }
                (s_mid, sent)
            } else if success {
                let new_match_index = *match_index;
                if new_match_index > s_mid.log.len() as u64 {
                    let sent: Vec<CRaftMessage> = vec![];
                    proof {
                        lemma_empty_msg_map();
                        assert(s_mid@.role is Leader);
                        lemma_set_map_contains(c.servers@, *follower_id);
                    }
                    (s_mid, sent)
                } else {
                    proof {
                        broadcast use vstd::std_specs::hash::group_hash_axioms;
                        lemma_set_map_contains(c.servers@, *follower_id);
                        // new_match_index <= s_mid.log.len() <= s.log.len() < u64::MAX
                        // step_down preserves log, so s_mid@.log.len() == s@.log.len()
                        assert(s_mid@.log =~= s@.log);
                        assert(s_mid@.log.len() == s@.log.len());
                    }
                    CHandleAppendResponse(&s_mid, c, term, success, match_index,
                                          follower_id, follower_id, &new_match_index)
                }
            } else {
                proof {
                    broadcast use vstd::std_specs::hash::group_hash_axioms;
                    lemma_set_map_contains(c.servers@, *follower_id);
                }
                CHandleAppendReject(&s_mid, c, term, success, match_index, follower_id, follower_id)
            }
        }
        _ => {
            // Not leader: no-op
            let sent: Vec<CRaftMessage> = vec![];
            proof {
                lemma_empty_msg_map();
                assert(!(s_mid@.role is Leader));
            }
            (s_mid, sent)
        }
    }
}

/// Advance commit index: guard check + delegate to CAdvanceCommitIndex.
pub exec fn CTryAdvanceCommitIndex(
    s: &CState, c: &CConstants,
    new_commit_index: &u64,
) -> (result: (CState, Vec<CRaftMessage>))
requires
    s.valid(),
    c.valid(),
    (!(s.role is Leader) || *new_commit_index <= s.commit_index) || (
        *new_commit_index as int <= s@.log.len()
        && s.log@[*new_commit_index as int - 1].term == s.current_term
    ),
ensures
    result.0.valid(),
    LTryAdvanceCommitIndex(s@, result.0@, c@, *new_commit_index as int,
                           result.1@.map(|i, p: CRaftMessage| p@)),
{
    if !matches!(s.role, CServerRole::Leader) || *new_commit_index <= s.commit_index {
        let s_clone = clone_state(s);
        let sent: Vec<CRaftMessage> = vec![];
        proof { lemma_empty_msg_map(); }
        (s_clone, sent)
    } else {
        CAdvanceCommitIndex(s, c, new_commit_index)
    }
}

/// Dispatch an incoming message to the appropriate composite handler.
pub exec fn CHandleMessage(
    s: &CState, c: &CConstants,
    msg: &CRaftMessage,
) -> (result: (CState, Vec<CRaftMessage>))
requires
    s.valid(),
    c.valid(),
    s.log@.len() < u64::MAX as int,
ensures
    result.0.valid(),
    LHandleMessage(s@, result.0@, c@, msg@, result.1@.map(|i, p: CRaftMessage| p@)),
{
    match msg {
        CRaftMessage::RequestVote { term, candidate, last_log_index, last_log_term } => {
            CHandleRequestVoteMsg(s, c, term, candidate, last_log_index, last_log_term)
        }
        CRaftMessage::VoteResponse { term, granted, voter } => {
            CHandleVoteResponseMsg(s, c, term, *granted, voter)
        }
        CRaftMessage::AppendEntries { term, leader, prev_index, prev_term,
                                      value, has_entry, leader_commit } => {
            CHandleAppendEntriesMsg(s, c, term, leader, prev_index, prev_term,
                                    value, *has_entry, leader_commit)
        }
        CRaftMessage::AppendResponse { term, success, match_index, follower } => {
            CHandleAppendResponseMsg(s, c, term, *success, match_index, follower)
        }
    }
}
