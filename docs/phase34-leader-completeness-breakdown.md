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

## Update: 34.7.1.e.4.b.2.b.2.b blocker analysis (2026-03-04)

Current branch status in
`lemma_leader_completeness_inductive`:

- overlap voter `ov` is constructed and transferred to pre-state:
  `ds.server_states[ov].log[k] == entry`
- vote provenance wiring is in place:
  `lemma_request_vote_witness_from_votes_granted`
- bridge template is instantiated:
  `lemma_vote_grant_bridge_template_for_overlap_voter(...)`

Why the final transfer still cannot be closed yet:

- The bridge template proves a conditional implication from
  RequestVote handling to `log_not_older_than(leader, voter_mid)`.
- To use it for concrete leader-state transfer at index `k`, the proof still
  needs a packet-history bridge that relates in-network `RequestVote` summary
  fields (`last_log_index`, `last_log_term`) to the sender's concrete log
  state strongly enough in the current state.

Required follow-up obligations (split in TODO leaf `34.7.1.e.4.b.2.b.2.b`):

1. Align RequestVote send semantics with sender log summary at send time.
2. Prove an inductive invariant that current sender log remains at least as
   up-to-date as any retained RequestVote summary for the same election term.
3. Consume that bridge in the overlap-voter subcase to replace the local
   `assume(ds_.server_states[leader_id].log[k] == entry)` with a proof.

## Update: 34.7.1.e.4.b.2.b.2.b.2 complete (2026-03-04)

Implemented RequestVote send-parameter alignment in:

- `src/protocol/Raft/raft.rs` (`LTimeout`)
- `src/generated/Raft/raft_gen.rs` (`CTimeout`)

Change made:

- Replaced fixed RequestVote `(last_log_index, last_log_term) = (0, 0)` with
  sender-derived values:
  - `last_log_index = s.log.len()`
  - `last_log_term = if s.log.len() == 0 { 0 } else { s.log[last].term }`

This removes the immediate mismatch between packet parameters and candidate log
state at election start, which is required before proving the remaining
packet-history bridge in the next leaf (`...b.3`).

## Update: 34.7.1.e.4.b.2.b.2.b.3 decomposition (2026-03-04)

Implemented the first concrete slice for `...b.3`:

- Added message-level invariant definition
  `RequestVoteSummaryStillValidAtSameTerm` in
  `src/protocol/Raft/refinement_proof/message_invariants.rs`.
- Invariant intent: for any in-network `RequestVote` packet, if sender
  candidate is still at that packet term, sender log still contains the
  packet summary slot/term (`last_idx`, `last_term`).

Proof status:

- A direct inductive proof attempt in `invariants.rs` hit persistent rlimit
  blowups (focused `*request_vote_summary_still_valid*`, even with higher
  rlimit), so the TODO leaf was split into smaller sub-leaves:
  1. invariant definition (done),
  2. old-packet preservation proof,
  3. new-packet establishment from `LTimeout`,
  4. integration into `RaftSafetyInvariant`.

This keeps the work honest and incremental without masking the unresolved proof
search bottleneck.

## Update: 34.7.1.e.4.b.2.b.2.b.3.b complete (2026-03-04)

Completed the old-packet slice in
`src/protocol/Raft/refinement_proof/invariants.rs`:

- Added helper
  `lemma_request_vote_summary_old_packet_preserved(ds, ds_, p)`.
- Scope: pre-state packet only (`ds.network.contains(p)`, `p.msg is RequestVote`).
- Result: if candidate `d` is still at packet term `t` in post-state, then
  packet summary fields remain justified by `ds_.server_states[d].log`.

Proof split:

1. `d != server_id` (non-stepping sender): direct state-frame equality
   transfer.
2. `d == server_id` (stepping sender): use `RequestVoteSenderState(ds)` plus
   term monotonicity to force pre-term equality (`current_term == t`), then
   lift summary facts with `lemma_lnext_log_preserved_or_extended`.

Focused verification:

- Pass:
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::invariants --verify-function '*request_vote_summary_old_packet_preserved*' --rlimit 40`

## Update: 34.7.1.e.4.b.2.b.2.b.3.c complete (2026-03-04)

Completed the new-packet slice in
`src/protocol/Raft/refinement_proof/invariants.rs`:

- Added helper
  `lemma_request_vote_summary_new_packet_established(ds, ds_, p)`.
- Scope: post-state new packet only (`ds_.network.contains(p)` and
  `!ds.network.contains(p)`), with `p.msg is RequestVote`.
- Result: if candidate `d` is still at packet term `t` in `ds_`, then the
  packet summary constraints hold in `ds_`:
  - `0 <= last_idx <= ds_.server_states[d].log.len()`
  - `last_idx == 0 ==> last_term == 0`
  - `last_idx > 0 ==> ds_.server_states[d].log[last_idx - 1].term == last_term`

Proof shape:

1. Extracted `server_id` + `(sent_packets, received_from)` witnesses from
   `RaftServerStepWithNetwork`.
2. Used new-packet membership to recover `p.msg` from `sent_packets`.
3. Instantiated the `LTimeout` send shape and transferred equalities:
   candidate identity (`d == server_id`), last-index (`s.log.len()`), and
   last-term (`0` or `s.log[last].term`).
4. Lifted to `ds_` via the timeout frame fact `s_.log == s.log`.

Focused verification:

- Pass:
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::invariants --verify-function '*request_vote_summary_new_packet_established*' --rlimit 40`

## Update: 34.7.1.e.4.b.2.b.2.b.3.d complete (2026-03-04)

Integrated the packet-history bridge into the composite safety invariant:

- Added `RequestVoteSummaryStillValidAtSameTerm(ds)` to
  `RaftSafetyInvariant` in
  `src/protocol/Raft/refinement_proof/invariants.rs`.
- Added inductive proof
  `lemma_request_vote_summary_still_valid_inductive(ds, ds_)`.
- Wired the new inductive lemma into
  `lemma_safety_invariant_inductive`.
- Narrowed `lemma_leader_completeness_inductive` preconditions to explicit
  needed invariants (instead of `RaftSafetyInvariant(ds)`) to avoid pulling
  unrelated new message-invariant quantifiers into that proof obligation.

Proof structure for `lemma_request_vote_summary_still_valid_inductive`:

1. Quantify over any `p` in `ds_.network`.
2. Restrict to `RequestVote` packets and same-term candidate case
   (`ds_.server_states[d].current_term == t`).
3. Split old vs new packet membership:
   - old packet (`ds.network.contains(p)`): use
     `lemma_request_vote_summary_old_packet_preserved`.
   - new packet (`!ds.network.contains(p)`): use
     `lemma_request_vote_summary_new_packet_established`.

Focused verification:

- Pass:
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::invariants --verify-function '*request_vote_summary_still_valid_inductive*' --rlimit 40`

Status note:

- Existing focused check
  `*leader_completeness*` at `--rlimit 40` currently still reports rlimit
  pressure in `lemma_leader_completeness_inductive`. This is tracked in the
  remaining TODO leaf `34.7.1.e.4.b.2.b.3` (proof search reduction / stability).

## Update: 34.7.1.e.4.b.2.b.2.b.4.a-b complete (2026-03-04)

Completed the first two slices of `...b.4` in
`src/protocol/Raft/refinement_proof/invariants.rs`:

- `lemma_overlap_voter_request_vote_summary_context(...)` (leaf `...b.4.a`)
  packages overlap-voter RequestVote provenance with same-term sender-summary
  validity (`RequestVoteSummaryStillValidAtSameTerm`), yielding concrete packet
  summary facts against the current leader log.
- `lemma_log_not_older_than_case_split_at_index(...)` +
  `lemma_vote_grant_bridge_overlap_index_relation_template(...)`
  (leaf `...b.4.b`) specialize the existing vote-grant bridge at target index
  `k` and expose an explicit Raft last-log split:
  - `leader_last_term > voter_last_term`, or
  - `leader_last_term == voter_last_term && leader_log_len > k`.

Integration note:

- In `lemma_leader_completeness_inductive`, the unchanged-leader fresh-step
  overlap branch now uses the packaged RequestVote-summary helper and the new
  index-path relation template helper.
- The final transfer to concrete
  `ds_.server_states[leader_id].log[k] == entry` remains in next leaf
  (`...b.4.c`), where the local `assume` is still present.

Focused verification:

- Pass:
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::invariants --verify-function '*overlap_voter_request_vote_summary_context*' --rlimit 40`
- Pass:
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::invariants --verify-function '*log_not_older_than_case_split_at_index*' --rlimit 40`
- Pass:
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::invariants --verify-function '*vote_grant_bridge_overlap_index_relation_template*' --rlimit 40`
- Still rlimit-bounded (existing):
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::invariants --verify-function '*leader_completeness*' --rlimit 40`

## Update: 34.7.1.e.4.b.2.b.2.b.4.c.a-c.b complete (2026-03-04)

Completed the next two decomposition slices for `...b.4.c` in
`src/protocol/Raft/refinement_proof/invariants.rs`:

- `lemma_overlap_voter_vote_request_packet_context(...)` (leaf `...c.a`)
  packages both concrete overlap-voter packet witnesses:
  - granted `VoteResponse` (`overlap_voter -> leader_id`) with aligned leader
    term plus voter-term/voted_for consistency facts, and
  - corresponding `RequestVote` (`leader_id -> overlap_voter`) with same-term
    sender summary validity (`last_log_index`/`last_log_term`) against the
    leader's current log.
- In `lemma_leader_completeness_inductive` unchanged-leader fresh-step overlap
  branch (leaf `...c.b`), replaced the prior RequestVote-only extraction with
  the new combined packet-context helper and explicit term split:
  - same-term subcase: `overlap_voter.current_term == req_term`, deriving
    concrete `has_voted && voted_for == leader_id` and reusing
    `lemma_vote_grant_bridge_overlap_index_relation_template(...)`.
  - stale-vote subcase: `overlap_voter.current_term > req_term`, isolated as a
    separate proof obligation for follow-up leaf `...c.c`.

Status after this update:

- The local final transfer `assume(ds_.server_states[leader_id].log[k] == entry)`
  remains in place.
- Focused leader-completeness verification is still rlimit-bounded (no new hard
  proof error observed in this slice).

Focused verification:

- Rlimit-bounded (existing):
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::invariants --verify-function '*leader_completeness_inductive*' --rlimit 40`

## Update: 34.7.1.e.4.b.2.b.2.b.4.c.c.a complete (2026-03-04)

Analyzed stale-vote branch (`overlap_voter.current_term > req_term`) and
split the old monolithic leaf `...c.c` into smaller prerequisites.

Key finding:

- Under current state-only packet invariants, stale-vote is not contradictory:
  `VoteResponseIntegrity` explicitly allows
  `voter.current_term > vote_term`, and this can coexist with the overlap path.
  So closing stale-vote needs additional historical/provenance strength, not
  just local contradiction.

Implemented first stale sub-leaf:

- Added helper
  `lemma_overlap_voter_stale_vote_packet_context(...)` in
  `src/protocol/Raft/refinement_proof/invariants.rs`.
- This helper specializes the overlap packet context to stale-vote and packages:
  - concrete granted `VoteResponse` witness (`overlap_voter -> leader_id`),
  - concrete matching `RequestVote` witness (`leader_id -> overlap_voter`) with
    request-summary validity facts,
  - strict stale inequality
    `ds.server_states[overlap_voter].current_term > req_term`.
- Wired this helper into stale branch of
  `lemma_leader_completeness_inductive` so the remaining gap is isolated to a
  dedicated stale-vote provenance obligation.

Focused verification:

- Pass:
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::invariants --verify-function '*overlap_voter_stale_vote_packet_context*' --rlimit 40`
- Still rlimit-bounded (existing):
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::invariants --verify-function '*leader_completeness_inductive*' --rlimit 40`

## Update: 34.7.1.e.4.b.2.b.2.b.4.c.c.b.a complete (2026-03-04)

Decomposed stale-provenance leaf `...c.c.b` into smaller model/proof slices.
The full closure is larger than a clean <500 LOC single iteration because it
needs a new history-carrying invariant, not just local branch reasoning.

Concrete non-vacuous stale-provenance contract (required by follow-up leaves):

- For a granted stale vote packet witness
  `VoteResponse{term: t, voter: v} (v -> leader)` with `v.current_term > t`,
  and matching `RequestVote{term: t, candidate: leader, last_idx, last_term}`,
  we need a vote-time witness state `v_pre` such that:
  - `LHandleRequestVoteMsg(v_pre, v_post, c_v, t, leader, last_idx, last_term, sent)`
    with `sent == [VoteResponse{term: t, granted: true, voter: v}]`.
  - `v_pre.log` is prefix-preserved by current voter log (append-only transfer).
  - For overlap path usage, `v_pre.log` still carries the overlap entry at `k`
    (or an equivalent relation strong enough to recover it).

Why current invariants are insufficient:

- `VoteResponseIntegrity` allows stale packets via `v.current_term > t`, but
  does not preserve vote-time voter-log witness.
- `VoteResponseHasRequestVote` gives packet provenance only.
- `RequestVoteSummaryStillValidAtSameTerm` constrains candidate summary only,
  not voter vote-time log when voter term advanced.
- `LogAppendOnly` is step-local and does not by itself reconstruct the specific
  historical state that produced an old packet.

So `...c.c.b` must introduce explicit stale-history carrier (ghost/payload) and
its inductive preservation before the stale branch can discharge `...c.c.c`.

## Update: 34.7.1.e.4.b.2.b.2.b.4.c.c.b.b complete (2026-03-04)

Implemented the model-level stale-vote provenance carrier using packet-attached
vote-time voter-log summary data.

Changes:

- Extended `LRaftMessage::VoteResponse` in `src/protocol/Raft/types.rs` with:
  - `voter_last_log_index`
  - `voter_last_log_term`
- Strengthened `LGrantVote` in `src/protocol/Raft/raft.rs` to populate these
  fields from the voter's current log summary at vote time.
- Threaded the new `VoteResponse` payload shape through:
  - Raft message dispatch/refinement glue
  - generated Raft model types/exec code (`src/generated/Raft/types_gen.rs`,
    `src/generated/Raft/raft_gen.rs`)
  - host wire conversion boundary (`src/implementation/Raft/host.rs`)
- Updated refinement-proof vote-packet matching/witness formulas to account for
  the widened message payload (using `..` where summary fields are irrelevant,
  and existential packet witnesses where exact packet literals were too rigid).
- Added the carrier contract definition in
  `src/protocol/Raft/refinement_proof/message_invariants.rs`:
  - `VoteResponseSummaryStillValidAtOrAboveTerm(ds)`.

Scope note:

- This leaf introduces the carrier and its state-level contract.
- Inductive preservation and integration into `RaftSafetyInvariant` remain in
  next leaf `...c.c.b.c`.

Focused verification:

- Pass:
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::invariants --verify-function '*vote_witness_from_votes_granted*' --rlimit 40`
- Pass:
  `/home/shuai/tools/verus-x86-linux/verus --crate-type=lib src/lib.rs --verify-only-module protocol::Raft::refinement_proof::message_invariants --verify-function '*log_append_only*' --rlimit 40`

## Update: 34.7.1.e.4.b.2.b.2.b.4.c.d.b.c decomposition start (2026-03-04)

Strict-term closure (`req_last_log_term > voter_vtl`) is now the first open leaf
in the unchanged-leader overlap transfer path.

Executed prerequisite leaf `...b.c.1` as an analysis checkpoint:

- Audited the strict-term branch preconditions and identified that widened
  `VoteResponse` payload matching (`voter_last_log_index`,
  `voter_last_log_term`) touches stale-vote proof helpers in:
  - `src/protocol/Raft/refinement_proof/state_machine.rs`
  - `src/protocol/Raft/refinement_proof/message_invariants.rs`
  - `src/protocol/Raft/refinement_proof/invariants.rs`
- Recorded these as explicit prerequisite touchpoints so `...b.c.2` can focus
  on strict-term obligation isolation without conflating compile-shape drift
  with proof obligations.

Remaining strict-term decomposition:

1. `...b.c.2`: isolate strict-term-only obligations and remove shared branch
   ambiguity with other residual cases (`L == 0`, `req_last_log_index > L`).
2. `...b.c.3`: close the strict-term transfer constructively (no local assume)
   while keeping focused verification stable.

## Update: 34.7.1.e.4.b.2.b.2.b.4.c.d.b.c.2.a complete (2026-03-04)

Prepared an explicit branch-partition obligation map for
`lemma_overlap_entry_transfer_equal_term_equal_len(...)` so the strict-term
work is isolated from the other residual sub-cases.

Current residual branch (old single `else`) covers three disjoint sub-cases:

1. Strict-term:
   `req_last_log_term > voter_vtl`.
2. Equal-term + empty vote-time log:
   `req_last_log_term == voter_vtl && L == 0`.
3. Equal-term + strictly longer request summary:
   `req_last_log_term == voter_vtl && req_last_log_index > L`.

For `...b.c.2`, only case (1) is in scope. The shared strict-term facts that
must be explicit before constructive transfer (`...b.c.3`) are:

- `L >= 0` and `L <= overlap_voter.log.len()` from `VoteLogLenBounded`.
- `k < L` from `VoteLogLenEntryTermBound` + `entry.term < vote_term`.
- packet alignment facts already required by the lemma preconditions:
  - `vote_pkt.src == overlap_voter`, `vote_pkt.dst == leader_id`
  - `req_pkt.src == leader_id`, `req_pkt.dst == overlap_voter`
  - `vote_pkt.term == req_pkt.term == leader.current_term`
- strict-term guard itself:
  `req_last_log_term > voter_vtl`.

Planned immediate code refactor for next sub-leaf (`...b.c.2.b`):

- Replace the merged residual `else` with explicit three-way branch structure.
- Keep equal-term/equal-length branch unchanged.
- Keep non-strict residual cases isolated so strict-term proof obligations can
  be discharged without conflating assumptions across unrelated branches.
