# LeaderCompleteness Strict-Term Case — Proof Blocker Analysis

**Date**: 2026-03-06
**Last Updated**: Phase 34.7.1.e.4.b.2.b.3.a (analysis complete — all 6 assumes same gap)
**Context**: The hardest step in the Raft refinement proof.

## 1. The Goal

Prove: if entry `e` (with `e.term = T_e`) is committed at index `k`, and server `leader_id` is a leader at term `T_leader > T_e`, then `leader.log[k] == e`.

## 2. High-Level Proof Strategy

```
committed entry (k, e, term T_e)
    |
    | commit quorum Q_c: majority of servers have log[k] == e
    |
leader at term T_leader (> T_e)
    |
    | vote quorum Q_v: majority voted for leader
    |
    +-- Q_c and Q_v are both majorities
    |   ==> they overlap (pigeonhole)
    |   ==> exists overlap voter "ov" in both
    |
    | ov has log[k] == e  (from Q_c)
    | ov voted for leader  (from Q_v)
    |
    +-- Need to prove: leader.log[k] == e
        (transfer entry from ov's log to leader's log)
```

## 3. Entry Transfer: How It Works

When `ov` voted for `leader`, the Raft protocol checked `log_up_to_date`:
- `ov` received `RequestVote(last_log_index=li, last_log_term=lt)` from `leader`
- `ov` granted the vote only if leader's log is "at least as up-to-date" as voter's log
- Up-to-date means: `lt > voter_last_term` OR (`lt == voter_last_term` AND `li >= voter_log_len`)

This gives us two cases based on the relationship between `lt` (leader's last log term from the RequestVote) and `voter_vtl` (voter's last log term at vote time):

### Case A: Equal-term (`lt == voter_vtl`) — SOLVED

```
leader log:  [... entry_at_k ... | last entry term=lt ]
                                        |
                                   same term
                                        |
voter log:   [... entry_at_k ... | last entry term=vtl ]
                                 (vtl == lt)
```

Both logs have entries with the same term at some index. LogMatching says: if two servers have entries at the same index with the same term, all preceding entries match. Since `k` is before both last entries, `leader.log[k] == voter.log[k] == e`.

This case is fully proved via `lemma_equal_term_log_transfer` and `lemma_log_matching_chain`.

### Case B: Strict-term (`lt > voter_vtl`) — PARTIALLY SOLVED

```
leader log:  [... ??? at k ... | ... | last entry term=lt ]
                                              |
                                         lt > vtl
                                              |
voter log:   [... entry_at_k=e ... | last entry term=vtl ]
```

We know leader's log ends with a higher term than voter's. But we have NO "same term anchor point" to apply LogMatching directly.

**Sub-case B.1: d_rlt == entry.term** — SOLVED (Phase 34.9)
When ETHVQ vote dest `d` has `d.current_term == entry.term`, use vote dest uniqueness: the commitment quorum's ETHVQ vote dest at the same term must be the same server `d`. LogMatching then transfers the entry. Resolved 3 of 10 assumes.

**Sub-case B.2: d_rlt > entry.term AND d_rli > k** — SOLVED
When ETHVQ vote dest `d` has pre-election log length > k, LogMatching at anchor index d_rli-1 (which is ≥ k) covers index k. Recursive descent on `decreases (term_gap, anchor_gap)` terminates.

**Sub-case B.3: d_rlt > entry.term AND d_rli ≤ k** — BLOCKED (the `d_rli ≤ k` wall)
This is the fundamental remaining blocker. See §4.

## 4. The `d_rli ≤ k` Wall — The Fundamental Blocker

When ETHVQ vote dest `d` has pre-election log length `d_rli ≤ k`:

```
d's log at vote time:  [e0, e1, ..., e_{d_rli-1}]  (length d_rli ≤ k)
                                                     |
                                          after election, d creates entries via LClientRequest:
                                                     |
d's log now:           [e0, e1, ..., e_{d_rli-1}, ..., d.log[k], ..., d.log[L-1]]
                                                       ^^^^^^^^^
                                                       term = T_k (d's current term)
                                                       ≠ T_e (entry's term)
```

- LogMatching at `d_rli-1` covers indices `0..d_rli-1` — NOT index k.
- By IH/recursion, intermediate vote dest `d2` at lower term `d_rlt` has `d2.log[k] == entry`.
- But `d.log[k].term = T_k ≠ T_e = d2.log[k].term` — different terms at index k.
- No LogMatching anchor exists at or above k between d and d2.

### Why the Raft Paper's Argument Works (But We Can't Mechanize It)

Ongaro's proof (PhD thesis §3.6.1) uses **strong induction on terms**:

1. Assume LeaderCompleteness fails for some term T. Pick the **smallest** such T.
2. The T-leader got votes from majority Q_v. Committed entry has majority Q_c. They overlap at voter w.
3. (strict-term case) T-leader's last log term T' > w's last log term. Then T' < T.
4. The T'-leader wrote the T-leader's last log entry. **By minimality of T**, the T'-leader has the committed entry.
5. LogMatching from T'-leader to T-leader (they share a term-T' entry at T-leader's log end) gives T-leader the committed entry. Contradiction.

**Step 4 is the key**: "By minimality of T, the T'-leader has the committed entry" uses strong induction on **the leader's term**, NOT on the ETHVQ term descent. In our Verus mechanization:

- We use `decreases (term_gap, anchor_gap)` on ETHVQ term descent, which tracks the **vote dest's term**, not the leader's term.
- The vote dest `d` at term `T_k` has `d_rli ≤ k`, so anchor descent terminates at `d_rli-1 < k`.
- Getting from `d2.log[k] == entry` to `d.log[k] == entry` requires an anchor AT k — which doesn't exist.
- The Raft paper sidesteps this by using the **T'-leader** (who created d's entry at d_rli-1), not d's ETHVQ vote dest d2.

### The Gap Between ETHVQ Term Descent and Leader Term Induction

Our current recursive structure descends on **ETHVQ vote dests**: each step goes from one vote dest to a lower-term vote dest, trying to bridge entries via LogMatching. The Raft paper instead descends on **leader terms**: the T'-leader (who created entries in the T-leader's log) must have the committed entry by minimality.

These are different objects:
- ETHVQ vote dest at term T_k: the server that "won" the election at term T_k (received quorum-1 votes)
- Leader at term T_k: the server that actually became leader (received quorum votes and transitioned to Leader state)

In our model, these are the same server (ETHVQ is derived from the leader's vote quorum). But the Raft paper's argument uses the **leader's log content** as the bridge (the leader wrote entries → its log contains them → LogMatching from leader to next leader), while our ETHVQ argument uses the **vote dest's log content**.

## 5. Current Status of All Assumes

### 6 `assume(false)` for LeaderCompleteness (all `d_rli ≤ k` wall)

Former #4 (equal-term, rli > L) resolved in Phase 34.7.1.e.4.b.2.b.2.b.4.c.d.b.e via ETHVQ+vote_dest_unique at same term vtl.

| # | Line | Function | Specific Case |
|---|------|----------|---------------|
| 1 | 1206 | `lemma_ethvq_entry_transfer_from_overlap_voter` | k == d_rli-1, d.log.len() == k+1, d.log[k].term > entry.term |
| 2 | 1221 | `lemma_ethvq_entry_transfer_from_overlap_voter` | k > d_rli-1, d.log too short or d.log[k].term ≠ entry.term |
| 3 | 1779 | `lemma_ethvq_committed_entry_transfer` | d2_rlt > entry.term, k ≥ d2_rli-1, server.log[k].term ≠ entry.term |
| 4 | 2694 | `lemma_overlap_voter_entry_transfer` | Strict-term, rli > L, leader.log[k].term ≠ entry.term |
| 5 | 2718 | `lemma_overlap_voter_entry_transfer` | Strict-term, k < rli, leader.log[k].term ≠ entry.term |
| 6 | 2732 | `lemma_overlap_voter_entry_transfer` | Strict-term, k ≥ rli, leader.log too short or wrong term |

### 5 Sound Z3 Workaround Assumes (permanent)

| Line | Purpose |
|------|---------|
| 2213 | ETHVQ witness extraction in `lemma_same_term_committed_entry_transfer` |
| 2236 | ETHVQ witness extraction in `lemma_same_term_committed_entry_transfer` |
| 2331 | ETHVQ witness extraction in `lemma_ethvq_committed_overlap` |
| 2633 | ETHVQ+vote_dest_unique extraction in `lemma_overlap_voter_entry_transfer` (equal-term rli>L) |
| 3826 | ETHVQ witness extraction in `lemma_leader_log_quorum_intersection` |

### 1 SMS Assume (depends on LeaderCompleteness)

| Line | Purpose |
|------|---------|
| 6218 | `assume(ds_.server_states[i].log[k] == ds_.server_states[j].log[k])` for newly committed entries — needs full LeaderCompleteness |

## 6. Approaches Explored and Rejected

### NoConflictAtCommittedIndex (Phase 34.10)

Define: `s.log.len() > k ∧ EntryCommittedAt(ds, k, e) → s.log[k].term ≤ e.term`

**NOT globally inductive for fresh commits**: A leader at high term T can create `log[k].term = T > T_e` via LClientRequest BEFORE the commit quorum for entry e forms at index k. The entry at index k was created by the leader locally — it has `term = T` where T is the leader's current term. Meanwhile, the committed entry has `term = T_e < T`. So a fresh commit creates `EntryCommittedAt(ds_, k, e)` in the post-state, but the server already has `log[k].term = T > T_e`.

The near-quorum argument (near-quorum + vote quorum + stepping server > n → overlap → log_up_to_date blocks the candidate) DOES prevent this, but mechanizing it requires the same term induction.

### CommittedEntryUniversalAgreement / CEUA (Phase 34.10)

Define: `s.log.len() > k ∧ EntryCommittedAt(ds, k, e) → s.log[k] == e` (for ALL servers, not just leaders)

This IS a true invariant of Raft (by the paper's argument). Would make LeaderCompleteness trivial. But proving inductiveness faces the exact same `d_rli ≤ k` wall — the fresh-commit case requires showing that no server has a conflicting entry at index k, which requires the term induction argument.

### Concrete Counterexample Construction (Phase 34.10)

All attempts to construct a trace violating LeaderCompleteness in this no-truncation Raft model FAILED. Timing constraints prevent it:
- AE packets at term T_e are rejected by servers with current_term > T_e
- `log_up_to_date` check prevents candidates with stale logs from winning elections
- Pigeonhole: near-quorum (servers replicating committed entry) + vote quorum + stepping server > n forces overlap

This confirms LeaderCompleteness is true in the model but doesn't help mechanize the proof.

## 7. Possible Forward Paths

### Option A: Leader-Term Induction (matches Raft paper) — Most Promising

Instead of descending on ETHVQ vote dests, descend on **leader terms**. For each entry `leader.log[j]` with term T' < T_leader, the T'-leader must have had the committed entry (by IH on T'). LogMatching from the T'-leader to the T_leader (they share a term-T' entry at index j) transfers the committed entry.

**Challenge**: Requires a **term-indexed ghost invariant** carrying per-term LC information. In the fresh-commit path, `!EntryCommittedAt(ds, k, entry)`, so `LeaderCompleteness(ds)` from IH provides no information about the committed entry. The T'-leader (ETHVQ vote dest at term T') may not be a current Leader in ds, so LC(ds) can't be applied directly.

Would need something like: `forall T, k. (quorum_size - 1 servers have log[k].term == T_e at term T_e) && leader_at_term_T.log[k].term != T_e ==> false`. This requires expressing "all leaders at terms < T have the entry" within a single behavioral step — essentially embedding strong induction on terms inside the step-induction proof.

**Estimated effort**: ~500-1000 LOC refactoring with significant Z3 instability risk.

### Option B: Prove Unreachable — REJECTED

Explored in Phase 34.10 (NoConflictAtCommittedIndex, CEUA) and Phase 34.7.1.e.4.b.2.b.3.a analysis. A leader at high term T CAN have `log[k].term = T > T_e` via LClientRequest before the commit quorum forms. `leader.log[k].term != entry.term` IS reachable in isolation; only the full system (quorum overlap + vote comparison + LogMatching chains across ALL terms) prevents it, which requires term induction.

### Option C: Ghost Provenance Chain — Insufficient Alone

Add `creator_id: Ghost<int>` to log entries recording which leader created each entry. Analysis shows this doesn't solve the core problem: proving `creator.log[k] == committed_entry` hits the same `d_rli ≤ k` wall. The creator's quorum overlaps the commit quorum, but the overlap voter comparison requires the same term induction argument.

**Could be useful IN COMBINATION with Option A** to simplify the term-indexed invariant.

### Option D: Accept Assumes as Pragmatic Gaps — RECOMMENDED

Mark the 6 `assume(false)` as documented proof gaps with soundness argument: "LeaderCompleteness holds by the Raft paper's term induction argument (Ongaro §3.6.1). Mechanization is blocked by the `d_rli ≤ k` wall where behavioral step-induction cannot express 'smallest failing term' strong induction on leader terms."

This is the pragmatic path. The trusted base increases by 6 assumes, all representing the same well-understood gap.

### Option E: Restructured Invariant (EntryUniquePerTermIndex) — Same Wall

Define: `forall s1, s2, k. s1.log[k].term == s2.log[k].term → s1.log[k] == s2.log[k]`

This is exactly LogMatching restricted to a single index. Would resolve the wall IF we could establish `d.log[k].term == entry.term`. But we can't — that's precisely the gap. The server created a new entry at index k with a different term.

## 7.1. Why Fresh Commits Block Term Induction (Phase 34.7.1.e.4.b.2.b.3.a)

The fundamental insight: in `lemma_leader_completeness_fresh_commit_unchanged_leader`, the entry is committed in ds' but NOT in ds. The commit quorum in ds' includes the stepping server (which just appended the entry at index k = ds.server_states[stepping].log.len()). Removing stepping leaves quorum_size - 1 servers with the entry in ds — a near-quorum, but NOT enough for `EntryCommittedAt(ds, k, entry)`.

Since `!EntryCommittedAt(ds, k, entry)`, `LeaderCompleteness(ds)` (from behavioral IH) says nothing about this entry. We can't apply LC(ds) to ANY leader at ANY term for this entry. The Raft paper avoids this because it uses term induction (not behavioral step induction): "for the smallest failing term T, all terms < T satisfy LC" — this is a statement about ALL committed entries, including ones committed in the same state. Our step induction only gives us LC for the pre-state.

## 8. What's Already Been Done

Infrastructure built (bottom-up):

1. **Ghost state** (`vote_log_len`): Records voter's log length at vote time.
2. **VoteGrantedLogUpToDateAtVoteTime**: Captures log_up_to_date check using ghost state.
3. **LogMatching chain** (`lemma_log_matching_chain`): Same term at same index → all preceding entries match.
4. **Equal-term transfer** (`lemma_equal_term_log_transfer`): Fully handles equal-term case.
5. **LogTermsMonotonic**: Log entry terms are non-decreasing.
6. **VoteLogLenEntryTermBound**: Entries after vote-time have term ≥ vote term (proves k < L).
7. **ETHVQ vote dest uniqueness** (Phase 34.9): Two vote dests at same term must be same server.
8. **`lemma_same_term_committed_entry_transfer`** (Phase 34.9): Resolved 3 assumes for d_rlt == entry.term.
9. **`lemma_ethvq_entry_transfer_from_overlap_voter`**: ETHVQ-safe wrapper for pre-state committed cases.
10. **`lemma_ethvq_committed_entry_transfer`**: Recursive with `decreases (term_gap, anchor_gap)`.

**Key Raft spec constraints discovered (Phase 34.10)**:
- `LSendAppendEntries` (raft.rs:149): Leaders only replicate entries matching current_term.
- `LHandleAppendEntriesMsg` (raft.rs:409): Index mismatch check — entries placed at correct index only.
- `LFollowerAppendEntries`: Append-only — entries at a given index set once permanently.

## 9. Summary

The remaining 6 `assume(false)` instances all represent the same fundamental gap: the `d_rli ≤ k` case where ETHVQ term descent produces a vote dest whose pre-election log doesn't reach index k, and LogMatching coverage is below k. The Raft paper resolves this via strong induction on leader terms (smallest failing term argument).

**Key finding (Phase 34.7.1.e.4.b.2.b.3.a)**: The gap is irreducible within behavioral step-induction. In the fresh-commit path, `!EntryCommittedAt(ds, k, entry)`, so `LeaderCompleteness(ds)` from the behavioral IH provides no information. Term induction (Option A) requires a term-indexed ghost invariant (~500-1000 LOC, high Z3 risk). Ghost provenance (Option C) doesn't help alone. **Recommendation: accept as documented gaps (Option D)** with Option A as future work.
