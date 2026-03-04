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
