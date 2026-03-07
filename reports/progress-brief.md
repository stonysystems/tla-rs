# Progress Summary (2026-03-06)

## 1. RSL Code Generation & Proof
- **8 RSL modules** fully transpiler-generated, all standalone (no hand-written delegates)
- 4,149 LOC generated (`src/generated/RSL/`), 69 verified exec functions

**36 verification gaps** (excluding IO trust boundary and clone), nearly all caused by **Verus lacking verified HashSet/HashMap support**:

| Category | Count | Description |
|----------|-------|-------------|
| `assume` — set cardinality | 7+1 | `HashSet.len()` vs `Set.map(f).len()` (7), exec bool vs spec forall (1) |
| `external_body` — generated | 3 | HashSet insert, HashMap filter, unreachable utility |
| `external_body` — implementation | 26 | HashSet/HashMap predicates (19), sorting (2), axioms (5) |

**Root cause:** Multi-Paxos uses set predicates extensively (quorum checks, forall/exists over 1b packets, HashMap insert/filter). These are concise at spec level but require HashSet/HashMap iteration at exec level, which Verus cannot verify.

**Planned solution (Phase 30):** Write operation-level `external_body` lemmas for HashSet/HashMap (`lemma_hashset_len`, `lemma_hashset_contains`, `lemma_hashmap_get`, `lemma_set_map_preserves_len`, etc.) that bridge exec operations to spec. Then remove `external_body` from the 19 predicate functions and add lemma calls so Verus can verify the existing iteration logic. The 8 assumes are replaced by `lemma_set_map_preserves_len` calls. Expected result: 36 gaps → ~14 (8 lemma primitives + 5 irreducible axioms + 1 sort).

## 2. Glue Code (Claude-Generated)
- **10 protocols** (RSL, Raft, TwoPhase, PrimaryBackup, ChainReplication, PBFT, LeaderElection, VerticalPaxos, EPaxos, Paxos) each have glue code connecting verified code to networking.
This includes:

- **host.rs** — protocol host logic (message dispatch, timer management, I/O)
- **message.rs** — wire-format serialization/deserialization
- **services/** — service entry points and state machine wrappers

## 3. Raft Benchmark
- 3-node localhost cluster

| Clients | Throughput (ops/sec) | Avg Latency (ms) |
|---------|---------------------|-------------------|
| 1 | 1,297 | 0.79 |
| 4 | 3,607 | 1.15 |



## 4. Raft Spec Enhancement (Phase 27)
**Problem identified:** After Phase 26 (Raft runnable), we reviewed the Raft code and found that the original spec only modeled atomic, fine-grained actions (11 independent state transitions). This created a **verification gap** — the host (`host.rs`) contained ~634 LOC of unverified protocol logic:

- Step-down-on-higher-term logic in every message handler
- Guard condition checks (term comparison, role checks, log-up-to-date)
- Composite action sequencing (e.g., receive vote → check quorum → become leader)

**Solution (Phase 27):** Enriched the Raft spec with **composite actions** that model complete message-handling flows.

## 5. Raft Safety Refinement Proof (Phase 32 + 34)

**Top-level theorem**: `lemma_refinement_correct` — every valid Raft distributed behavior refines to a sequential append-only committed log.

- **6 files**, ~12,000 LOC in `src/protocol/Raft/refinement_proof/`
- **30+ invariants** proved inductively (19 message invariants, 4 ghost state, 4 SMS infrastructure, 3 log structure, plus structural)
- **669 verified, 0 errors**
- **12 assumes remain** in `invariants.rs`: 7 LeaderCompleteness `assume(false)` (blocked on `d_rli ≤ k` wall — requires leader-term strong induction per Ongaro PhD §3.6.1), 4 sound Z3 workarounds (permanent), 1 StateMachineSafety (blocked on LC)
- See `reports/raft_refinement_proof.md` for full architecture, invariant list, and detailed status

## 6. Transpiler Enhancement (Phase 29 — Planned)

**Problem identified:** The 8 composite exec functions in Phase 27 had to be hand-written (`raft_manual.rs`, 369 LOC) because the transpiler cannot translate them. Root cause analysis revealed a single missing capability:

**The transpiler cannot translate value-returning spec helper functions.**

Specifically, the pattern `spec fn step_down_if_needed(s: LState, term: int) -> LState` returning an intermediate state, followed by using that intermediate state as input to another action. This is different from RSL's pattern where actions delegate to sub-components (`s.acceptor → s_.acceptor`).
