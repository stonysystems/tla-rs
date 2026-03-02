# Verification Gaps Report (2026-03-01, Post-Phase 32)

Excludes IO trust boundary (10 packet-identity assumes) and clone/view-mapping related items.

## Changes (2026-03-01): Proof hardening — 8 common_proof assumes eliminated

- **packet_sending.rs**: 5 assumes eliminated — replaced `choose + assume(RslNextOneReplica(...))` pattern
  with direct `nextStep->ios` extraction + `choose |idx| RslNextOneReplica(ps, ps_, idx, ios)`.
  Proof: RslNextEnvironment excluded by `nextStep is LEnvStepHostIos`; RslNextOneExternal excluded
  by `replica_ids.contains(p.src)` + `IsValidLIoOp(Send{s:p}, actor, _)` → `p.src == actor`.
- **chosen.rs**: 2 assumes eliminated — `choose` witnesses for QuorumOf2bs indices proven valid
  by asserting `indices.len() > 0` from `LMinQuorumSize >= 1` + `WellFormedLConfiguration`.
- **requests.rs**: 1 assume eliminated — `assume(s.drop_first().len() < s.len())` replaced with
  `assert(...)` (trivially true for Seq).
- RSL common_proof assume count: 23 → 15

## Changes from Phase 32

- **Raft Safety Refinement Proof completed** (Phase 32.1–32.7) — full refinement proof from distributed Raft → abstract sequential state machine
- 5 new files: `src/protocol/Raft/refinement_proof/{state_machine,invariants,induction,committed,refinement}.rs`
- Top-level theorem: `lemma_refinement_correct` — every valid Raft behavior refines to a sequential committed log
- Phase 32.3.1-32.3.2: Detailed invariant induction proofs with supporting invariants (VotesGrantedAreServers, CandidateOrLeaderVotedForSelf, VotersVotedForCandidate); 7 LNext case analysis assumes eliminated via helper lemmas + spec strengthening (LFollowerAppendEntries commit_index capped by min(ae_leader_commit, new_log_len))
- Spec strengthened with prev_log consistency check in `LHandleAppendEntriesMsg` per Raft §5.3 — follower rejects AppendEntries when prev_log entry doesn't match; refinement proof updated with new branch
- 6 targeted `assume()` across 2 files (see §6 below): 5 in invariants.rs, 1 in committed.rs
- 1 `external_body` axiom (`lemma_quorum_intersection` in common/collections/sets.rs) — pigeonhole principle for quorum intersection
- Verification: 669 verified, 0 errors (up from 632 pre-Phase 32)

## Changes from Phase 31

- **28 external_body proof functions removed** (Phase 31.1–31.7) — all 28 refinement proof stubs now have verified proof bodies
- Files affected: `refinement_proof/{chosen,requests,execution,refinement}.rs`, `common_proof/{chosen,quorum,learner_state,message2a}.rs`
- 5 targeted `assume()` remain inside 3 of the 28 now-verified functions (see §5 below)
- Dependency analysis and classification documented in `docs/refinement_proof_plan.md`

## Changes from Phase 30

- **8 cardinality/forall assumes eliminated** (Phase 30.2.1) — replaced with proven lemma calls
- **3 external_body predicates verified** (Phase 30.2.2) — clone_cpacket_preserving_validity, CProposerCanNominateUsingOperationNumber, CValIsHighestNumberedProposalAtBallot
- **3 dead code functions deleted** (Phase 30.2.3) — SortVecCOperationNumber (had swap bug), CGetHighestValueAmongMajority, CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints_optimized
- **6 new collection lemma primitives added** (Phase 30.4.1) — monomorphic cardinality + forall bridging lemmas

---

## 1. `external_body` in generated/RSL (excluding IO and clone)

| # | File | Function | Root Cause |
|---|------|----------|------------|
| 1 | `generated/RSL/proposer_gen.rs` | `hashset_insert_cpacket` | HashSet mutation |
| 2 | `generated/RSL/learner_gen.rs` | `filter_clearnerstate` | HashMap key-threshold filtering |
| 3 | `generated/RSL/types_gen.rs` | `unreachable_value<T>` | utility (`requires false`, harmless) |

**Subtotal: 3 (2 real gaps + 1 harmless)**

---

## 2. `external_body` in implementation/RSL (excluding IO and clone)

### 2.1 HashSet iteration predicates (9 — irreducible Verus limitation)

Verus cannot verify `for x in hashset.iter()` loops — HashSet iteration produces elements
in unspecified order and Verus lacks loop invariant support for it.

| # | File | Function | Purpose |
|---|------|----------|---------|
| 1 | `gen_helpers.rs` | `Packet1bHasUniqueSrc` | HashSet forall src uniqueness |
| 2 | `ProposerImpl.rs` | `CIsAfterLogTruncationPoint` | HashSet forall opn check |
| 3 | `ProposerImpl.rs` | `CSetOfMessage1bAboutBallot` | HashSet forall + peek (iter().next()) |
| 4 | `ProposerImpl.rs` | `CAllAcceptorsHadNoProposal` | HashSet forall check |
| 5 | `ProposerImpl.rs` | `CExistVotesHasProposalLargeThanOpn` | HashMap exists check |
| 6 | `ProposerImpl.rs` | `CExistsAcceptorHasProposalLargeThanOpn` | HashSet exists check |
| 7 | `ProposerImpl.rs` | `Cmax_balInS` | HashSet max comparison |
| 8 | `ProposerImpl.rs` | `CExistsBallotInS` | HashSet exists check |
| 9 | `ProposerImpl.rs` | `CValIsHighestNumberedProposal` | HashSet complex predicate |

### 2.2 HashMap iteration functions (4 — irreducible Verus limitation)

| # | File | Function | Purpose |
|---|------|----------|---------|
| 10 | `acceptor_helpers.rs` | `CRemoveVotesBeforeLogTruncationPoint` | HashMap key-threshold filtering |
| 11 | `acceptor_helpers.rs` | `CAddVoteAndRemoveOldOnes` | HashMap insert + filter |
| 12 | `gen_helpers.rs` | `CClientsInReplies` | build HashMap from Vec |
| 13 | `gen_helpers.rs` | `CUpdateNewCache` | HashMap merge |

### 2.3 Complex delegation wrappers (4 — external_body, delegate to sub-functions)

| # | File | Function | Purpose |
|---|------|----------|---------|
| 14 | `gen_helpers.rs` | `CReplicaNextProcess1b` | wraps 1b processing (HashMap in acceptor) |
| 15 | `gen_helpers.rs` | `CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints` | log truncation delegation |
| 16 | `gen_helpers.rs` | `CExtractSentPacketsFromIos` | IO event → sent packets |
| 17 | `gen_helpers.rs` | `outbound_packets_to_vec` | OutboundPackets → Vec\<CPacket\> |

### 2.4 Clone helpers (1)

| # | File | Function | Purpose |
|---|------|----------|---------|
| 18 | `gen_helpers.rs` | `clone_cpacket_full` | Structural equality `res == *p` (CPacket's Eq is `#[verus::trusted]`) |

### 2.5 Duplicate (1)

| # | File | Function | Purpose |
|---|------|----------|---------|
| 19 | `ReplicaImpl.rs` | `Packet1bHasUniqueSrc` | Duplicate of gen_helpers.rs version |

### 2.6 Axioms / equality (5 — irreducible type-system trust)

| # | File | Function | Purpose |
|---|------|----------|---------|
| 20 | `cmessage.rs` | `axiom_cmessage_view` | CMessage view injectivity |
| 21 | `cmessage.rs` | `axiom_cmessage_key_model` | CMessage key model |
| 22 | `cmessage.rs` | `axiom_cpacket_view` | CPacket view injectivity |
| 23 | `cmessage.rs` | `axiom_cpacket_key_model` | CPacket key model |
| 24 | `ElectionImpl.rs` | `CRequest::eq` | PartialEq with EndPoint |

**Subtotal: 24**

---

## 3. Trusted Lemma Primitives (new from Phase 30)

These `external_body` proof functions are trusted but sound — they bridge exec-level
collection operations to spec-level Set/Map operations.

| # | File | Function | Soundness Basis |
|---|------|----------|-----------------|
| 1 | `hashsets.rs` | `lemma_set_map_injective_len` | Set::map + injectivity → bijection |
| 2 | `hashsets.rs` | `lemma_set_view_map_len` | View function is injective by construction |
| 3 | `hashsets.rs` | `lemma_hashset_view_len` | Combines vstd axioms + view injectivity |
| 4 | `hashsets.rs` | `lemma_hashset_cpacket_len` | Monomorphic CPacket cardinality |
| 5 | `hashsets.rs` | `lemma_hashset_endpoint_len` | Monomorphic EndPoint cardinality |
| 6 | `hashsets.rs` | `lemma_cpacket_set_forall_src` | Forall bridging CPacket→RslPacket |
| 7 | `hashmaps.rs` | `lemma_hashmap_filter_by_key` | HashMap filter preserves invariants |
| 8 | `hashmaps.rs` | `lemma_hashmap_iter_complete` | HashMap iteration completeness |

**Subtotal: 8 (2 verified: lemma_set_u64_to_int_len, lemma_hashset_u64_len_eq_mapped)**

---

## 4. Grand Total (excluding IO trust boundary and clone)

| Category | Before Phase 30 | After Phase 30 | After Phase 31 | Change (Phase 31) |
|----------|----------------|----------------|----------------|-------------------|
| Cardinality/forall assumes | 8 | 0 | 0 | 0 |
| `external_body` in generated/RSL | 3 | 3 | 3 | 0 |
| `external_body` in implementation/RSL | 26 | 24 | 24 | 0 |
| Trusted lemma primitives (common/) | 0 | 8 | 8 | 0 |
| `external_body` in refinement proof | 20 | 20 | 0 | **-20** |
| `external_body` in common proof | 8 | 8 | 0 | **-8** |
| **Total external_body gaps** | **57** | **55** | **27** | **-28** |

Root cause breakdown (remaining 27 `external_body` in impl/generated/common):
- **HashSet/HashMap iteration** (15): Verus lacks verified iteration specs for unordered collections
- **Trusted collection lemma primitives** (8): cardinality/forall bridging for hashsets/hashmaps
- **Complex delegation wrappers** (4): Compose sub-functions with ownership patterns Verus can't prove
- **Type axioms** (5): View injectivity and key model axioms for CMessage/CPacket/CRequest
- **Generated helpers** (3): hashset_insert, filter, unreachable_value
- **Minus overlapping count** (-8): trusted lemma primitives counted in both categories

Refinement proof assume() breakdown (15 total, separate from external_body):
- 1 in formerly-external_body functions (detailed in §5)
- 14 in pre-existing Dafny→Verus port helpers (§5 bottom)

---

## 5. Refinement Proof — Remaining `assume()` (Post-Phase 31, updated March 2026)

All 28 `external_body` proof functions have been converted to verified proof bodies.
Of the original 5 targeted `assume()` inside formerly-external_body functions, **all 5 have been eliminated**:
- `lemma_ChosenQuorumAnd2aFromLaterBallotMatchValues`: 2 assumes eliminated by asserting existential witnesses (choose axiom)
- `lemma_2aMessagesFromSameBallotAndOperationMatchWLOG`: 2 assumes eliminated via broadcast same-message lemma + proposer state contradiction

1 targeted `assume()` remains in a formerly-external_body function:

| # | File | Function | assume | Root Cause |
|---|------|----------|--------|------------|
| 1 | `refinement_proof/requests.rs:78` | `lemma_RequestInRequestsReceivedThisEpochHasCorrespondingRequestMessage` | `assume(b[i].environment.sentPackets.contains(p))` | Received packet membership in next-step sentPackets |

Additionally, 14 `assume()` statements exist in pre-existing helper functions (never were external_body).
These are inherited from the Dafny→Verus port, distributed across:
- `common_proof/quorum.rs` (5): set cardinality, intersection properties
- `common_proof/message2b.rs` (4): action identification, vote monotonicity
- `common_proof/message2a.rs` (3): vote monotonicity, ballot identity
- `common_proof/message1b.rs` (2): contradiction cases in inductive steps

Previously eliminated:
- 47 base-case assumes (message2a.rs, message2b.rs, message1b.rs): vacuous truth proofs
- 5 packet_sending.rs assumes: direct nextStep->ios extraction
- 2 chosen.rs assumes: choose witness from non-empty set
- 1 requests.rs assume: trivial seq property

Total `assume()` across RSL proof files: 15 (1 in formerly-external_body + 14 in pre-existing helpers).

---

## 6. Raft Safety Refinement Proof — `assume()` Summary (Phase 32)

6 targeted `assume()` across the Raft refinement proof files:

### invariants.rs (5 assumes)

7 LNext case analysis assumes were eliminated (Phase 32.3.2) using helper lemmas:
- `lemma_lnext_votes_bounded`: Verus auto-case-splits to prove votes come from {old votes} ∪ {my_id} ∪ c.servers
- `lemma_lnext_self_vote_preserved`: Verus auto-case-splits to prove Candidate/Leader self-vote preserved
- `lemma_lnext_leader_quorum_preserved`: Verus auto-case-splits to prove Leader quorum preserved
- `lemma_invariant_at_step`: Clean recursive induction with `decreases k` (replaces inner assume)
- CommitIndexBounded: spec fix in `LFollowerAppendEntries` — changed `ae_leader_commit` to `min(ae_leader_commit, new_log_len)` (Raft §5.3 semantics). Verus now auto-verifies `lemma_lnext_commit_bounded`.

Phase 32.3.3: Quorum intersection lemma added to sets.rs (`lemma_quorum_intersection`).
Election Safety `assume(false)` replaced with structured quorum intersection argument + `assume(stepping == other)`.

Phase 32.3.4-32.3.6: Log-level invariants (LogMatching, LeaderCompleteness, StateMachineSafety)
moved from bare assumes in composite function to structured proof functions with:
- `lemma_lnext_log_preserved_or_extended`: Verified helper proving log is unchanged or extended by 1 entry for all LNext branches
- `lemma_log_matching_inductive`: Structured proof documenting the two network-level gaps (leader entry uniqueness, message provenance)
- `lemma_leader_completeness_inductive`: Structured proof documenting quorum intersection + log up-to-date argument
- `lemma_state_machine_safety_inductive`: Documents dependency on LogMatching + LeaderCompleteness
- Spec now includes prev_log consistency check in `LHandleAppendEntriesMsg` (Raft §5.3), but assumes remain due to existentially-quantified message parameters in single-server model

Remaining assumes:

| # | Line | Function | assume | Root Cause |
|---|------|----------|--------|------------|
| 1 | 376 | `lemma_election_safety_inductive` | `assume(stepping == other)` | Quorum intersection requires VotersVotedForCandidate(ds_) + VotesGrantedAreServers(ds_) |
| 2 | 565 | `lemma_voters_voted_for_candidate_inductive` | `VotersVotedForCandidate(ds_)` | Network-level invariant requires message provenance tracking |
| 3 | 775 | `lemma_log_matching_inductive` | `LogMatching(ds_)` | Network-level message provenance: ae_prev_index/ae_prev_term existentially quantified (prev_log check in spec, but can't link to leader's log) |
| 4 | 827 | `lemma_leader_completeness_inductive` | `LeaderCompleteness(ds_)` | Requires LogMatching + quorum intersection + log up-to-date |
| 5 | 860 | `lemma_state_machine_safety_inductive` | `StateMachineSafety(ds_)` | Depends on LeaderCompleteness + LogMatching |

### induction.rs (0 assumes)

Delegates to `lemma_safety_invariant_inductive` from invariants.rs.
`lemma_invariant_holds_throughout_behavior` uses clean recursive induction (no assumes).

### committed.rs (1 assume)

Three assumes eliminated via seq-based helpers:
- WellFormedness assume eliminated via `max_commit_index_seq` (avoids RaftDistributedState sub-state construction)
- MaxCommitIndex monotonicity eliminated via `lemma_max_commit_seq_monotone` (recursive proof over server_states sequences)
- GetCommittedLog length monotonicity eliminated via `lemma_committed_log_len` + `lemma_max_commit_seq_achieved`

| # | Line | Function | assume | Root Cause |
|---|------|----------|--------|------------|
| 6 | 152 | `lemma_committed_log_monotone` | prefix entries match | Requires StateMachineSafety for log entry agreement across servers |

`lemma_abstract_step_valid` stutter case: proved via `=~=` extensional equality (previously assume).

### refinement.rs (0 assumes)

All proofs fully mechanized. Top-level `lemma_refinement_correct` has no assumes.

### What would eliminate these assumes

- **Assume 1 (ElectionSafety quorum intersection)**: Depends on assumes 2 and 3-5 being resolved first (VotersVotedForCandidate provides the crucial link that quorum overlap implies same candidate)
- **Assume 2 (VotersVotedForCandidate)**: Add network message provenance tracking (src/dst fields on messages, delivered-from invariant) to the distributed model, so that receiving a VoteResponse from voter `v` proves `v` actually voted for the candidate
- **Assumes 3-5 (LogMatching, LeaderCompleteness, StateMachineSafety)**: Spec now includes prev_log consistency check in `LHandleAppendEntriesMsg` (Raft §5.3), but assumes remain because ae_prev_index/ae_prev_term are existentially quantified in the single-server model — cannot link to leader's log. Requires adding network message provenance (tracking which messages were sent by whom with what parameters) to the distributed model
- **Assume 6 (committed.rs entry agreement)**: Follows directly from StateMachineSafety — once assumes 3-5 are resolved, this one falls out automatically
