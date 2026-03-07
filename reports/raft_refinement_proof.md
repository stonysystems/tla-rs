# Raft Refinement Proof — Status and Architecture

**Date**: 2026-03-06
**Last Updated**: Phase 34.10 (deep analysis of remaining assumes)
**Codebase**: `src/protocol/Raft/refinement_proof/`
**Status**: 12 assumes remaining (7 `assume(false)` + 4 sound Z3 workarounds + 1 SMS)

## 1. What the Proof Shows

The refinement theorem (`refinement.rs:105`, `lemma_refinement_correct`) states:

> For any valid Raft distributed behavior, there exists a corresponding abstract sequential state machine behavior that refines it.

Concretely: the committed log extracted from the distributed Raft state evolves as a monotonically growing prefix — no matter how servers elect leaders, replicate logs, or fail, external observers see a sequential append-only log.

## 2. Proof Architecture

```
refinement.rs          Top-level refinement theorem
    |
    +-- induction.rs   Behavior-level induction scaffolding
    |
    +-- invariants.rs  Safety invariant definitions + inductive proofs (~9400 LOC)
    |
    +-- message_invariants.rs   Network packet invariant definitions (499 LOC)
    |
    +-- committed.rs   Committed log extraction + monotonicity (232 LOC)
    |
    +-- state_machine.rs   Distributed state, network model, ghost state (641 LOC)
```

### Refinement Mapping

`AbstractifyRaftState(ds)` maps distributed state to abstract state:
- `committed_log` = `GetCommittedLog(ds)` — extract entries committed by majority
- `server_ids` = `{0, ..., num_servers - 1}`

### Proof Structure

The refinement theorem depends on `RaftSafetyInvariant(ds)` holding at every step.
`lemma_safety_invariant_inductive` proves `RaftSafetyInvariant(ds) && RaftDistributedNext(ds, ds') ==> RaftSafetyInvariant(ds')`.

## 3. Invariant Dependency Chain

```
Network Model (sentPackets + receive guards)              -- Phase 34.1 DONE
    |
    +--- Message Invariants (VoteResponseIntegrity,       -- Phase 34.2-34.3 DONE
    |    AppendEntriesIntegrity, OneVotePerTermInNetwork,
    |    SenderIntegrity, LogAppendOnly, CandidateVoteDestinationUnique)
    |
    +--- VotersVotedForCandidate                          -- Phase 34.4 DONE
    |        |
    +--------+--- ElectionSafety                          -- Phase 34.5 DONE
    |
    +--- LogMatching                                      -- Phase 34.6 DONE
    |
    +--- LeaderCompleteness                               -- Phase 34.7-34.9 PARTIAL
    |        |                                               (7 assume(false) remain)
    |        +--- ETHVQ vote dest uniqueness              -- Phase 34.9 DONE
    |        |    (resolved 3 of 10 assume(false))
    |        |
    |        +--- LogMatching-at-k fallback               -- Phase 34.8 DONE
    |             (structured 10 assumes into assume(false))
    |
    +--- StateMachineSafety                               -- Phase 34.8 spec FIXED
             |                                               (proof blocked on LC)
             +--- CommittedLogPrefix                      -- (blocked on SMS)
```

## 4. Full Invariant List (30+ conjuncts in RaftSafetyInvariant)

### Core Safety Invariants
| Invariant | Proved | Description |
|-----------|--------|-------------|
| ElectionSafety | YES | At most one leader per term |
| LogMatching | YES | Same index + same term => same entry and all preceding entries match |
| LeaderCompleteness | **NO** (7 assume(false)) | Every leader's log contains all previously committed entries |
| StateMachineSafety | **NO** (1 assume, blocked) | Committed entries at same index agree |

### Structural Invariants (all proved)
| Invariant | Description |
|-----------|-------------|
| VotesGrantedAreServers | votes_granted contains valid server IDs |
| CandidateOrLeaderVotedForSelf | Candidates/leaders have voted for themselves |
| CandidateOrLeaderVotedForSelfId | ...with matching voted_for field |
| VotersVotedForCandidate | Each voter in votes_granted sent a VoteResponse |
| LeaderHasQuorum | Leaders have majority in votes_granted |
| CommitIndexBounded | commit_index <= log.len() |
| EntryTermLeaderWitness | Each log entry has a leader witness at its term |
| EntryTermHasVoteQuorum | Each entry's witness has a vote quorum |

### Message Invariants (all proved)
| Invariant | Description |
|-----------|-------------|
| SenderIntegrity | Packet src is a valid server |
| VoteResponseIntegrity | Granted votes imply voter state consistency |
| VoteResponseHasRequestVote | Every granted VoteResponse has matching RequestVote |
| VoteResponseSummaryStillValidAtOrAboveTerm | Vote summary preserved when voter term >= vote term |
| AppendEntriesIntegrity | AE packets reflect sender's log |
| OneVotePerTermInNetwork | At most one granted vote per (voter, term) |
| RequestVoteSenderState | RequestVote sender is candidate at packet term |
| RequestVoteSummaryStillValidAtSameTerm | RV log summary valid when sender at same term |
| RequestVoteLogParamsConsistent | Consistent log params across RV packets from same sender/term |
| CandidateVoteDestinationUnique | Each candidate sends to each voter at most once per term |
| RequestVoteSummaryAlwaysValid | RV summary consistent at any term |
| RequestVoteLastLogTermBound | RV last log term bounded by sender's current term |

### Ghost State Invariants (all proved)
| Invariant | Description |
|-----------|-------------|
| VoteLogLenCoversNetwork | Every granted VoteResponse has (voter, term) in vote_log_len |
| VoteLogLenBounded | Recorded log length <= current log length, >= 0, current_term >= t |
| VoteLogLenEntryTermBound | Entries at indices >= vote-time log length have term >= vote term |
| VoteGrantedLogUpToDateAtVoteTime | log_up_to_date holds with vote-time log length |

### Log Structure Invariants (all proved)
| Invariant | Description |
|-----------|-------------|
| CurrentTermGeLogTerms | All log entry terms <= server's current_term |
| LogTermsMonotonic | Log entry terms are non-decreasing |
| TermsNonNegative | All terms >= 0 |

## 5. Remaining Assumes (11 total)

### A. LeaderCompleteness — 7 `assume(false)` (the `d_rli ≤ k` wall)

All 7 represent the same fundamental gap: when ETHVQ vote dest `d` has pre-election log length ≤ k, LogMatching coverage is below index k, and there's no anchor to transfer the committed entry from a lower-term server to `d`.

| # | Line | Function | Case |
|---|------|----------|------|
| 1 | 1156 | `lemma_ethvq_entry_transfer_from_overlap_voter` | k == d_rli-1, d.log[k].term > entry.term |
| 2 | 1171 | `lemma_ethvq_entry_transfer_from_overlap_voter` | k > d_rli-1, d.log too short or wrong term |
| 3 | 1729 | `lemma_ethvq_committed_entry_transfer` | d2_rlt > entry.term, k ≥ d2_rli-1, wrong term |
| 4 | 2576 | `lemma_overlap_voter_entry_transfer` | Equal-term, rli > L, wrong term |
| 5 | 2618 | `lemma_overlap_voter_entry_transfer` | Strict-term, rli > L, wrong term |
| 6 | 2642 | `lemma_overlap_voter_entry_transfer` | Strict-term, k < rli, wrong term |
| 7 | 2656 | `lemma_overlap_voter_entry_transfer` | Strict-term, k ≥ rli, wrong term or too short |

**Root cause**: The Raft paper's proof uses strong induction on leader terms ("smallest failing term"), which doesn't directly map to our ETHVQ vote-dest term descent. See `reports/leader_completeness_strict_term.md` for full analysis.

### B. Sound Z3 Workaround Assumes — 4 (permanent)

ETHVQ witness extraction via `choose` crashes Z3 (OOM). Using `assume` is sound because ETHVQ is in requires. Permanent until Z3/Verus improves Skolemization.

| Line | Function |
|------|----------|
| 2163 | `lemma_same_term_committed_entry_transfer` |
| 2186 | `lemma_same_term_committed_entry_transfer` |
| 2281 | `lemma_ethvq_committed_overlap` |
| 3745 | `lemma_leader_log_quorum_intersection` |

### C. StateMachineSafety — 1 assume (blocked on LeaderCompleteness)

| Line | Function |
|------|----------|
| 6120 | `lemma_state_machine_safety_inductive` — `assume(StateMachineSafety(ds_))` |

Requires LeaderCompleteness + quorum overlap argument. Spec fixed in Phase 34.8 (quorum replication guard added to `LAdvanceCommitIndex`). Proof deferred until LeaderCompleteness is fully proved.

## 6. Approaches for Remaining 7 Assumes

See `reports/leader_completeness_strict_term.md` §7 for full analysis. Summary:

| Approach | Feasibility | Risk |
|----------|-------------|------|
| Leader-term induction (matches Raft paper) | Most promising | Z3 rlimit with recursive calls + ETHVQ |
| Ghost provenance chain | Feasible but invasive | Significant spec refactoring |
| Accept as documented gaps | Pragmatic | Increases trusted base |
| Stronger invariant (CEUA) | True but faces same wall | Same mechanization challenge |

## 7. Proof Techniques Used

### Z3 Isolation Pattern
Heavy quantifiers (ETHVQ, LogTermsMonotonic, message invariants) cause Z3 blow-up when combined in one function. Solution: extract into separate helper lemmas with only one "heavy" invariant family each.

### Ghost State (vote_log_len)
Map `vote_log_len: Map<(int, int), int>` records voter log length at vote time. Enables stale-vote reasoning.

### ETHVQ Vote Dest Uniqueness (Phase 34.9)
Two ETHVQ vote dests at the same term must be the same server (quorum intersection + OneVotePerTermInNetwork + CandidateVoteDestinationUnique). Resolved 3 of 10 assume(false) instances.

### LogMatching-at-k Fallback (Phase 34.8)
When proving `server.log[k] == entry` given `ov.log[k] == entry`: if `server.log[k].term == entry.term`, LogMatching works. Otherwise, `assume(false)` marks the unreachable divergence case.

### Packet Provenance Chain
`VoteResponse(v→c, term t, granted)` → `VoteResponseHasRequestVote` → `RequestVote(c→v, term t)` → `RequestVoteSummaryStillValidAtSameTerm` → concrete log summary facts.

## 8. Key Raft Spec Constraints

Discovered during Phase 34.10 analysis, important for proof architecture:

- `LSendAppendEntries` (raft.rs:149): `has_entry ==> s.log[prev_log_index].term == s.current_term` — leaders ONLY replicate entries matching current_term.
- `LHandleAppendEntriesMsg` (raft.rs:409): Index mismatch check — entries placed at correct log position only (first-come-first-served per index in no-truncation model).
- `LFollowerAppendEntries`: `s_.log == s.log.push(...)` — append-only, entries permanent once set.

## 9. Key Files

| File | LOC | Role |
|------|-----|------|
| `invariants.rs` | ~9400 | Core: all invariant definitions + 35+ inductive proof functions |
| `state_machine.rs` | 641 | Distributed state, network model, ghost state definitions |
| `message_invariants.rs` | 499 | Network packet invariant definitions (17 invariants) |
| `committed.rs` | 232 | Committed log extraction via MaxCommitIndex + monotonicity |
| `refinement.rs` | 154 | Top-level refinement theorem |
| `induction.rs` | 69 | Behavior-level induction scaffolding |

## 10. Timeline

| Date | Milestone |
|------|-----------|
| Phase 32 | Initial proof structure, 6 assumes |
| Phase 34.1-34.3 | Network model + message invariants (all proved) |
| Phase 34.4 | VotersVotedForCandidate proved |
| Phase 34.5 | ElectionSafety proved |
| Phase 34.6 | LogMatching proved |
| Phase 34.7 | LeaderCompleteness: equal-term cases done, strict-term blocked |
| Phase 34.8 | StateMachineSafety spec fixed (quorum guard). LogMatching-at-k fallback applied. 10 structured assume(false). |
| Phase 34.9 | ETHVQ vote dest uniqueness. 3 assume(false) resolved → 7 remain. |
| Phase 34.10 | Deep analysis: all 7 assumes are same `d_rli ≤ k` wall. NoConflictAtCommittedIndex and CEUA explored and found insufficient. |
