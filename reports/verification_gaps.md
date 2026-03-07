# Verification Gaps Report (2026-03-06, Post-Phase 34.15)

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
- Spec strengthened with prev_log consistency check in `LHandleAppendEntriesMsg` per Raft §5.3
- 1 `external_body` axiom (`lemma_quorum_intersection` in common/collections/sets.rs) — pigeonhole principle for quorum intersection
- Verification: 669 verified, 0 errors (up from 632 pre-Phase 32)

## Changes from Phase 34 (34.1–34.15)

- **RSL-style network model** added (Phase 34.1): `sentPackets`, `LRaftPacket`, receive guards, ghost `vote_log_len` state
- **30+ invariants proved** (Phase 34.2–34.15): 19 message invariants, 4 ghost state invariants, 4 SMS infrastructure invariants, 3 log structure invariants, plus structural invariants
- **ElectionSafety, VotersVotedForCandidate, LogMatching fully proved** (Phase 34.4–34.6): Phase 32 assumes 1-3 eliminated
- **LeaderCompleteness partially proved** (Phase 34.7–34.9): equal-term cases done, ETHVQ vote dest uniqueness resolved 3 of 10 `assume(false)`. 7 remain, all blocked on `d_rli ≤ k` wall
- **StateMachineSafety spec fixed** (Phase 34.8): quorum replication guard in `LAdvanceCommitIndex`
- **SMS infrastructure invariants** (Phase 34.12–34.14): ARLA, MILA, MIB, AELCB all fully proved
- **Committed log prefix preservation proved** (Phase 34.15): `committed.rs` now assume-free (Phase 32 assume 6 eliminated)
- **24 inductive lemma requires narrowed** from `RaftSafetyInvariant` to minimal sub-invariants (Phase 34.15)
- **Current Raft assumes**: 12 total in invariants.rs (see §6): 7 LC, 4 Z3 workarounds, 1 SMS

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

RSL refinement proof assume() breakdown: **0 total** — all RSL proof assumes fully eliminated.
Raft refinement proof assume() breakdown: **12 total** — 7 LC `assume(false)` (blocked on `d_rli ≤ k` wall), 4 sound Z3 workarounds, 1 SMS (blocked on LC). See §6.

---

## 5. Refinement Proof — `assume()` Status (Post-Phase 31, updated March 2026)

All 28 `external_body` proof functions have been converted to verified proof bodies.
**All `assume()` statements in RSL proof files have been eliminated (70 → 0).**

Elimination summary (cumulative):
- 47 base-case assumes (message2a.rs, message2b.rs, message1b.rs): vacuous truth — `sentPackets.len() == 0` at init
- 5 packet_sending.rs assumes: direct `nextStep->ios` extraction + single-variable `choose`
- 5 quorum.rs assumes: vstd set cardinality broadcast axioms + inductive finiteness proofs
- 4 message2b.rs assumes: votes monotonicity (RemoveVotesBeforeLogTruncationPoint), recv type + LAcceptorProcess2a (guard elimination via non-empty pkts)
- 3 message2a.rs assumes: votes monotonicity (LAcceptorTruncateLog), ballot identity (LBroadcastToEveryone msg field)
- 2 chosen.rs assumes: `Set::choose()` with `LMinQuorumSize >= 1`
- 2 message1b.rs assumes: contradiction — 1b-only action can't produce 2b packets (`!pkts.contains(p_2b)`)
- 1 requests.rs assume: received packet in sentPackets via `IsValidLIoOp` + `lemma_PacketStaysInSentPackets`
- 1 replica.rs `ExtractSentPacketsFromIos_Ensures2`: inductive proof mirroring `Ensures1`

Remaining `external_body` in proof code:
- `lemma_ExtractSentPacketsFromIos` (replica.rs): biconditional wrapper — both halves now proven separately (`Ensures1` + `Ensures2`), but the combined `<==>` is still `external_body`

Total `assume()` across RSL proof files: **0**.

---

## 6. Raft Safety Refinement Proof — `assume()` Summary (Phase 34.15)

12 `assume()` in invariants.rs, 0 in all other files. See `reports/raft_refinement_proof.md` for full architecture and invariant list.

### Phase evolution

- **Phase 32**: Initial proof structure with 6 assumes (5 in invariants.rs, 1 in committed.rs). Network model not yet added.
- **Phase 34.1-34.3**: Added RSL-style network model (`sentPackets` + receive guards), 19 message invariants proved.
- **Phase 34.4-34.5**: ElectionSafety and VotersVotedForCandidate fully proved (Phase 32 assumes 1-2 eliminated).
- **Phase 34.6**: LogMatching fully proved (Phase 32 assume 3 eliminated).
- **Phase 34.7-34.9**: LeaderCompleteness partially proved. Equal-term cases done. ETHVQ vote dest uniqueness resolved 3 of 10 strict-term `assume(false)`. 7 remain.
- **Phase 34.8**: StateMachineSafety spec fixed (quorum replication guard in `LAdvanceCommitIndex`).
- **Phase 34.11-34.14**: SMS infrastructure: `AppendResponseLogAgreement`, `MatchIndexImpliesLogAgreement`, `MatchIndexBounded`, `AppendEntriesLeaderCommitBound` invariants added and fully proved. SMS proof restructured.
- **Phase 34.15**: Committed log prefix preservation fully proved (`committed.rs` now assume-free, Phase 32 assume 6 eliminated). 24 inductive lemma requires narrowed from `RaftSafetyInvariant` to minimal sub-invariants.

### invariants.rs (12 assumes)

**A. LeaderCompleteness — 7 `assume(false)` (the `d_rli ≤ k` wall)**

All 7 represent the same fundamental gap: when ETHVQ vote dest `d` has pre-election log length ≤ k, LogMatching coverage is below index k, and there's no anchor to transfer the committed entry.

| # | Line | Function | Case |
|---|------|----------|------|
| 1 | 1206 | `lemma_ethvq_entry_transfer_from_overlap_voter` | k == d_rli-1, d.log[k].term > entry.term |
| 2 | 1221 | `lemma_ethvq_entry_transfer_from_overlap_voter` | k > d_rli-1, d.log too short or wrong term |
| 3 | 1779 | `lemma_ethvq_committed_entry_transfer` | d2_rlt > entry.term, k ≥ d2_rli-1, wrong term |
| 4 | 2626 | `lemma_overlap_voter_entry_transfer` | Equal-term, rli > L, wrong term |
| 5 | 2668 | `lemma_overlap_voter_entry_transfer` | Strict-term, rli > L, wrong term |
| 6 | 2692 | `lemma_overlap_voter_entry_transfer` | Strict-term, k < rli, wrong term |
| 7 | 2706 | `lemma_overlap_voter_entry_transfer` | Strict-term, k ≥ rli, wrong term or too short |

Root cause: The Raft paper's proof uses strong induction on leader terms ("smallest failing term" per Ongaro PhD §3.6.1), which doesn't map directly to single-step state machine induction with ETHVQ vote-dest term descent.

**B. Sound Z3 workaround assumes — 4 (permanent)**

ETHVQ witness extraction via `choose` crashes Z3 (OOM/stack overflow). Using `assume` is sound because `EntryTermHasVoteQuorum` is in requires. Permanent until Z3/Verus improves Skolemization.

| # | Line | Function |
|---|------|----------|
| 8 | 2213 | `lemma_same_term_committed_entry_transfer` |
| 9 | 2236 | `lemma_same_term_committed_entry_transfer` |
| 10 | 2331 | `lemma_ethvq_committed_overlap` |
| 11 | 3800 | `lemma_leader_log_quorum_intersection` |

**C. StateMachineSafety — 1 assume (blocked on LeaderCompleteness)**

| # | Line | Function | Description |
|---|------|----------|-------------|
| 12 | 6218 | `lemma_state_machine_safety_inductive` | Newly committed entries: `assume(ds_.server_states[i].log[k] == ...)` |

SMS proof restructured (Phase 34.14): frame cases proved via SMS(ds) + LogAppendOnly. Assume narrowed to only the case where stepping server's commit_index newly covers k. Requires LC + quorum overlap.

### committed.rs (0 assumes) ✓

All 4 original assumes eliminated:
- WellFormedness: `max_commit_index_seq` (avoids sub-state construction)
- MaxCommitIndex monotonicity: `lemma_max_commit_seq_monotone` (recursive proof)
- GetCommittedLog length: `lemma_committed_log_len` + `lemma_max_commit_seq_achieved`
- Prefix entries match (Phase 34.15): `lemma_committed_log_monotone` proved via SMS(ds_) + LogAppendOnly bridge

### induction.rs, refinement.rs (0 assumes) ✓

All fully mechanized. Top-level `lemma_refinement_correct` has no assumes.

### What would eliminate the remaining assumes

- **7 LC `assume(false)`**: Requires mechanizing leader-term strong induction (Ongaro PhD §3.6.1). When ETHVQ vote dest `d` has pre-election log length `d_rli ≤ k`, entries at indices `d_rli..k` were created via `LClientRequest` at term `d.current_term`. LogMatching at `d_rli-1` doesn't cover index k. The paper resolves via "smallest failing term T" strong induction; mechanizing this in single-step state machine induction is the open problem. Alternative: ghost provenance chain (feasible but invasive spec refactoring).
- **1 SMS assume**: Follows directly from LeaderCompleteness — once LC is fully proved, the SMS assume falls out via quorum overlap.
- **4 Z3 workaround assumes**: Sound and permanent. Will be removed if/when Z3/Verus improves nested existential Skolemization to avoid OOM on `choose |d: int| exists |voters: Seq<int>| { ... }`.
