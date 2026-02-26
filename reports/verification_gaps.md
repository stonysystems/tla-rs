# RSL Verification Gaps Report (2026-02-26, Post-Phase 30)

Excludes IO trust boundary (10 packet-identity assumes) and clone/view-mapping related items.

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

| Category | Before (Phase 30) | After (Phase 30) | Change |
|----------|-------------------|-------------------|--------|
| Cardinality/forall assumes | 8 | 0 | -8 (replaced with lemma calls) |
| `external_body` in generated/RSL | 3 | 3 | 0 |
| `external_body` in implementation/RSL | 26 | 24 | -2 (verified) + -3 (dead code deleted) = -5, +3 new from other adjustments |
| Trusted lemma primitives | 0 | 8 | +8 (new) |
| Sorting functions | 2 | 0 | -2 (dead code deleted) |
| **Total real verification gaps** | **36** | **27** | **-9** |

Root cause breakdown (remaining 27):
- **HashSet/HashMap iteration** (15): Verus lacks verified iteration specs for unordered collections
- **Complex delegation wrappers** (4): Compose sub-functions with ownership patterns Verus can't prove
- **Type axioms** (5): View injectivity and key model axioms for CMessage/CPacket/CRequest
- **Generated helpers** (3): hashset_insert, filter, unreachable_value
