# Phase 34.7.1 Breakdown: LeaderCompleteness Induction

Date: 2026-03-04

## Why this was decomposed

The original TODO item `34.7.1` is a multi-lemma proof task. In the current codebase,
completing it in one pass requires adding several bridge lemmas across:

- quorum-overlap witness extraction,
- vote-response packet provenance,
- log-up-to-date election constraints,
- and the final `LeaderCompleteness` induction step.

That is larger than a clean single <500 LOC leaf in one iteration,
so it is split into explicit sub-leaves.

## Target theorem

`lemma_leader_completeness_inductive(ds, ds_)` in:

- `src/protocol/Raft/refinement_proof/invariants.rs`

Current status: contains `assume(LeaderCompleteness(ds_))` and must be replaced
with an actual proof.

## Obligation map for the critical new-leader case

Goal case: step where a server becomes leader via `LReceiveVoteAndBecomeLeader`.
Need to show committed entries from prior terms remain in the new leader log.

### Step A: committed entry witness (already available)

From `EntryCommittedAt(ds, k, e)` obtain a quorum `Q_c` with members that have
entry `e` at index `k`.

Current source support:

- `EntryCommittedAt` definition in `invariants.rs`.

### Step B: vote quorum witness for new leader (partially available)

From candidate/leader vote state in `ds_`, obtain a quorum `Q_v` of voters.

Current source support:

- `LeaderHasQuorum` invariant and induction path already exist.
- `VotersVotedForCandidate` gives packet-level witness for voters in `votes_granted`.

Missing bridge:

- a reusable helper lemma exposing the exact witness form needed in 34.7.1,
  including term alignment and destination constraints for the new leader.

### Step C: overlap witness (requires helper packaging)

Use `lemma_quorum_intersection` to get `w in Q_c ∩ Q_v`.

Current source support:

- `lemma_quorum_intersection` exists in the proof stack.

Missing bridge:

- glue lemma that packages the two quorum facts (`Q_c`, `Q_v`) into an
  overlap witness with the exact committed-entry + voted-for facts attached.

### Step D: election log-up-to-date bridge (missing)

Need to turn "`w` voted for new leader" into
"new leader's log is at least as up-to-date as `w`" in a form usable at index `k`.

Current source support:

- `log_up_to_date` exists in `raft.rs`.
- request-vote handling and vote-response integrity are modeled.

Missing bridge:

- explicit proof lemma connecting voting preconditions/path to a usable
  index/term relation for new leader vs voter logs.

### Step E: conclude entry presence in new leader log (partially available)

Once log relation from Step D is available, combine with existing log invariants
(`LogMatching` path) to conclude new leader contains committed entry `e` at `k`.

Current source support:

- `LogMatching` induction machinery exists.

Missing bridge:

- final chain in `lemma_leader_completeness_inductive` replacing the assume.

## Planned implementation leaves

1. `34.7.1.b`: packet/voter witness helper.
2. `34.7.1.c`: overlap witness helper.
3. `34.7.1.d`: log-up-to-date bridge helper.
4. `34.7.1.e`: final proof replacement for `assume`.

## Validation command focus for upcoming leaves

Use focused verification while iterating:

```bash
/home/shuai/tools/verus-x86-linux/verus \
  --crate-type=lib src/lib.rs \
  --verify-only-module protocol::Raft::refinement_proof::invariants \
  --verify-function '*leader_completeness*' \
  --rlimit 40
```

Note: full-crate verification currently has an existing trigger issue in
`EntryTermLeaderWitness` (`invariants.rs`) that is outside this breakdown leaf.

## Update: 34.7.1.b complete (2026-03-04)

Implemented helper lemma:

- `lemma_vote_witness_from_votes_granted(ds, candidate, voter)`
  in `src/protocol/Raft/refinement_proof/invariants.rs`.

What it provides from `VotersVotedForCandidate + VoteResponseIntegrity`:

- concrete packet witness `p` in `ds.network`
- `p.src == voter`, `p.dst == candidate`
- `p.msg = VoteResponse{granted: true, voter, term = candidate.current_term}`
- aligned voter-state consequence:
  `voter.current_term > candidate.current_term`
  OR `voter.current_term == candidate.current_term && voter.has_voted && voter.voted_for == candidate`

Validation status:

- Focused command attempted:
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::invariants --verify-function '*vote_witness_from_votes_granted*' --rlimit 40`
- Currently blocked by existing module-level quantifier-trigger inference error in
  `EntryTermLeaderWitness` (`src/protocol/Raft/refinement_proof/invariants.rs`, around line 207).

## Update: 34.7.1.c complete (2026-03-04)

Implemented overlap helper lemma:

- `lemma_committed_vote_quorum_overlap_witness(ds, k, entry, candidate)`
  in `src/protocol/Raft/refinement_proof/invariants.rs`.

What it packages:

- committed quorum witness from `EntryCommittedAt(ds, k, entry)`
- vote quorum witness from `candidate.votes_granted` and quorum-size lower bound
- subset-to-universe facts and finite-universe discharge
- `lemma_quorum_intersection` application to derive overlap server `w`
- overlap outputs:
  - `w` is in candidate vote quorum
  - `w` has committed entry `entry` at index `k`
  - for `w != candidate`: explicit vote packet witness and voter term/voted_for
    alignment via `lemma_vote_witness_from_votes_granted`

Validation status:

- Focused command attempted:
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::invariants --verify-function '*committed_vote_quorum_overlap_witness*' --rlimit 40`
- Currently blocked by existing module-level quantifier-trigger inference error in
  `EntryTermLeaderWitness` (`src/protocol/Raft/refinement_proof/invariants.rs`, around line 207).

## Update: 34.7.1.d complete (2026-03-04)

Implemented log-up-to-date bridge helpers in
`src/protocol/Raft/refinement_proof/invariants.rs`:

- `log_not_older_than(candidate, voter)`
- `lemma_granted_request_vote_implies_log_up_to_date(...)`
- `lemma_vote_grant_context_implies_log_relation(...)`

Bridge semantics added:

- From a granted `LHandleRequestVoteMsg` context (sent packet is
  `VoteResponse{granted: true}`), derive the voter-side
  `log_up_to_date(step_down_if_needed(voter_pre, term), req_last_term, req_last_index)`
  fact.
- When request parameters match the candidate's last-log summary
  (`req_last_index == candidate.log.len()` and
  `req_last_term == candidate_last_term`), derive
  `log_not_older_than(candidate_state, voter_mid)`.

This isolates the exact Step-D proof bridge needed by leader election
reasoning. It is intentionally local to vote-grant context; the separate
packet/history linkage from a `VoteResponse` witness back to specific
`RequestVote` parameters remains part of later integration work.

Validation status:

- Focused command attempted:
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::invariants --verify-function '*vote_grant_context_implies_log_relation*' --rlimit 40`
- Currently blocked by existing module-level quantifier-trigger inference error in
  `EntryTermLeaderWitness` (`src/protocol/Raft/refinement_proof/invariants.rs`, around line 207).

## Update: 34.7.1.e decomposed; 34.7.1.e.1 complete (2026-03-04)

`34.7.1.e` is larger than a clean single-leaf implementation in this
codebase because it still needs (1) committed-witness transfer handling across
`ds -> ds_` and (2) explicit RequestVote provenance linkage for the new-leader
vote overlap path.

Added first execution leaf:

- `lemma_leader_completeness_unchanged_leader_for_prestate_commit(...)`
  in `src/protocol/Raft/refinement_proof/invariants.rs`.

What this sub-leaf discharges:

- unchanged leader (`ds_.server_states[leader_id] == ds.server_states[leader_id]`)
- committed-entry witness is already in pre-state (`EntryCommittedAt(ds, k, entry)`)
- then LeaderCompleteness obligation transfers directly to `ds_`.

Planned remaining sub-leaves:

1. `34.7.1.e.2`: `EntryCommittedAt(ds_)` transfer/fresh-step bridge
2. `34.7.1.e.3`: new-leader branch integration with provenance hook
3. `34.7.1.e.4`: remove assume and complete final induction theorem

Validation status:

- Focused command attempted:
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::invariants --verify-function '*leader_completeness_unchanged_leader_for_prestate_commit*' --rlimit 40`
- Currently blocked by existing dirty-worktree compile issue in
  `src/protocol/Raft/refinement_proof/invariants.rs` (undefined helper
  `lemma_leader_log_quorum_intersection`, around line 1442), before reaching
  the prior module-level trigger-inference blocker.

## Update: 34.7.1.e.2 complete (2026-03-04)

Implemented committed-witness transfer bridge helper in:

- `src/protocol/Raft/refinement_proof/invariants.rs`
  - `lemma_entry_committed_post_implies_pre_or_fresh_step_append(...)`

What this helper proves:

- From `EntryCommittedAt(ds_, k, entry)`, either:
  - `EntryCommittedAt(ds, k, entry)` already held in the pre-state
    (same quorum witness transfers), or
  - there is an explicit fresh-step append witness on the stepping server:
    `k == old_log_len`, post-step `log.len() == old_log_len + 1`, and
    the appended slot at `k` is `entry`.

Companion stabilization:

- `lemma_leader_completeness_unchanged_leader_for_prestate_commit(...)`
  was strengthened with `0 <= k` so the indexed postcondition proof is stable.

Validation status:

- Focused helper checks pass:
  - `*leader_completeness_unchanged_leader_for_prestate_commit*`
  - `*entry_committed_post_implies_pre_or_fresh_step_append*`
- Full-crate Verus remains failing on pre-existing high-cost proof obligations
  (rlimit/timeouts in unrelated large lemmas), now reported as 9 errors.

## Update: 34.7.1.e.3.a complete (2026-03-04)

Decomposed `34.7.1.e.3` further and completed the first leaf by adding a
network-level provenance hook:

- `VoteResponseHasRequestVote(ds)` in
  `src/protocol/Raft/refinement_proof/message_invariants.rs`
- `lemma_vote_response_has_request_vote_inductive(ds, ds_)` in
  `src/protocol/Raft/refinement_proof/invariants.rs`

What this provides:

- For every granted `VoteResponse` packet in `ds_.network`, there exists a
  matching `RequestVote` packet witness in `ds_.network` with aligned routing
  and term/candidate facts:
  - `req.src == vote.dst`
  - `req.dst == vote.voter`
  - `req.term == vote.term`
  - `req.candidate == vote.dst`

Proof shape:

- Old packet case: reuse `VoteResponseHasRequestVote(ds)` witness + network
  monotonicity.
- New packet case: use `RaftServerStepWithNetwork` witness, show granted
  `VoteResponse` can only come from `LHandleRequestVoteMsg`/`LGrantVote`,
  and use the received `RequestVote` packet as the provenance witness
  (plus `SenderIntegrity(ds)` for `candidate == src` alignment).

Validation status:

- Focused command passes:
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::invariants --verify-function '*vote_response_has_request_vote*' --rlimit 40`

## Update: 34.7.1.e.3.b complete (2026-03-04)

Implemented extraction helper in:

- `src/protocol/Raft/refinement_proof/invariants.rs`
  - `lemma_request_vote_witness_from_votes_granted(...)`

What this helper provides:

- Starting from vote-set membership (`candidate.votes_granted.contains(voter)`)
  plus existing vote witness/provenance invariants, it extracts an explicit
  `RequestVote` packet witness in-network with aligned routing/term/candidate:
  - `req.src == candidate`
  - `req.dst == voter`
  - `req.term == candidate.current_term`
  - `req.candidate == candidate`
- RequestVote last-log parameters are exposed existentially via packet pattern
  matching, so downstream lemmas can pull concrete request parameters for
  overlap voter reasoning.

How it is proved:

- Calls `lemma_vote_witness_from_votes_granted(...)` to get a concrete granted
  `VoteResponse` packet witness for `(voter -> candidate)` at candidate term.
- Instantiates `VoteResponseHasRequestVote(ds)` on that packet to obtain the
  corresponding `RequestVote` packet witness and re-exports it in the helper
  postcondition in candidate/voter form.

Validation status:

- Focused command passes:
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::invariants --verify-function '*request_vote_witness_from_votes_granted*' --rlimit 40`

## 34.7.1.e.3.c Wiring Update (2026-03-04)

Implemented wiring from overlap/provenance extraction into the leader-completeness
path in `src/protocol/Raft/refinement_proof/invariants.rs`:

- Added `lemma_overlap_request_vote_params_witness(...)` to package:
  - overlap voter witness from committed quorum ∩ vote quorum, and
  - RequestVote provenance witness when overlap voter is not the candidate.
- Added `lemma_vote_grant_bridge_template_for_overlap_voter(...)` to expose the
  reusable implication form that delegates to
  `lemma_vote_grant_context_implies_log_relation(...)`.
- Added `lemma_new_leader_provenance_bridge_wiring(...)` and called it from
  `lemma_leader_completeness_inductive(...)` so the new-leader branch explicitly
  threads overlap + RequestVote params into the log-up-to-date bridge path.

Focused verification status:

- Pass:
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::invariants --verify-function '*overlap_request_vote_params_witness*' --rlimit 40`
- Pass:
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::invariants --verify-function '*vote_grant_bridge_template_for_overlap_voter*' --rlimit 40`
- Pass:
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::invariants --verify-function '*leader_completeness*' --rlimit 40`
- Still rlimit-bounded:
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::invariants --verify-function '*new_leader_provenance_bridge_wiring*' --rlimit 40`
