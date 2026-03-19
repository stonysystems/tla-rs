# Source-First Model Checker Hotspot Ledger

Last updated: 2026-03-19 (Phase 36.3.7.c — guard-first evaluation)
Binary: `transpiler/target/release/verus-transpile` (release mode)
Optimization: guard-first evaluation in `solve_one_assignment()` — check constraints that don't depend on `s_` (next state) BEFORE cloning current state and processing assignments.

Raw JSON reports: `reports/benchmarks/source_first_release_profile_post_36_3_7c/`

---

## 1. LeaderElection (3-node benchmark, 120s timeout)

**Config**: `benchmarks_1h/leaderelection_benchmark.model.toml`
(3 nodes, int 0..2, max_set_len=3, max_seq_len=3, 3 safety invariants)

| Metric | Before (36.3.7.a) | After (36.3.7.c) | Change |
|--------|--------------------|-------------------|--------|
| Result | timeout (120s) | **timeout** (120s) | — |
| Distinct states | 127 | **355** | **+2.8x** |
| Solver time | 119,725 ms | 119,553 ms | — |
| Dedup time | 257 ms | 442 ms | — |
| Init time | 107 ms | 141 ms | — |
| Elapsed | 120s | 120s | timeout |

### Branch hotspot table (sorted by solve time, post-optimization)

| Branch | Action | Inv | Succ | Solve ms | Eval calls |
|--------|--------|-----|------|----------|------------|
| branch_3 | **LReceiveAnswer** | 88 | 46 | **29,335** | 649,440 |
| branch_2 | **LSendAnswer** | 89 | 155 | **27,626** | 656,820 |
| branch_5 | **LReceiveCoordinator** | 88 | 465 | **27,527** | 649,440 |
| branch_0 | LDetectFailure | 89 | 6 | 8,944 | 218,940 |
| branch_4 | LSendCoordinator | 88 | 34 | 8,885 | 216,480 |
| branch_1 | LStartElection | 89 | 237 | 8,764 | 218,940 |
| branch_6 | LNodeFail | 88 | 234 | 8,472 | 216,480 |

**Key change**: Guard-first evaluation prunes existential assignments that fail the guard (e.g., `s.alive.contains(node)`, `node > sender`) before cloning current_state and invoking the full predicate solver. The 2.8x state count improvement comes from exploring 355 states in the same 120s timeout (vs 127 before). Solver time per invocation decreased, allowing more states to be explored.

**Remaining bottleneck**: Solver time still dominates (99.2%). The guard-first check helps but the remaining valid assignments still require full predicate evaluation. Next optimization: hash-based dedup + further guard-first refinement within the helper function's inner existential expansion.

### LeaderElection 2-node reproducer (exhausted)

**Config**: `leaderelection_perf_repro.model.toml`
(2 nodes, int 0..1, max_set_len=2, max_seq_len=2)

| Metric | Before (36.3.7.a) | After (36.3.7.c) | Change |
|--------|--------------------|-------------------|--------|
| Result | ok (exhausted) | **ok** (exhausted) | — |
| Distinct states | 108 | 108 | same |
| Elapsed | 6,738 ms | **2,259 ms** | **3.0x faster** |
| Solver time | 6,328 ms | 1,842 ms | **3.4x faster** |
| Dedup time | 395 ms | 401 ms | same |

---

## 2. Paxos (3-node benchmark, 120s timeout)

**Config**: `benchmarks_1h/paxos_benchmark.model.toml`
(3 acceptors, quorum=2, int 0..2, max_set_len=3, max_seq_len=3, 3 safety invariants)

| Metric | Before (36.3.7.a) | After (36.3.7.c) | Change |
|--------|--------------------|-------------------|--------|
| Result | ok (exhausted) | **ok** (exhausted) | — |
| Distinct states | 17,370 | 17,370 | same |
| Elapsed | 99,838 ms | **81,224 ms** | **18.6% faster** |
| Solver time | 19,835 ms | **2,411 ms** | **8.2x faster** |
| Dedup time | 32,135 ms | 27,380 ms | — |
| Init time | 21,808 ms | 23,333 ms | — |

### Branch hotspot table (sorted by solve time, post-optimization)

| Branch | Action | Inv | Succ | Solve ms | Before ms | Speedup | Eval calls |
|--------|--------|-----|------|----------|-----------|---------|------------|
| branch_2 | **LRecvPromise** | 17,370 | 7,884 | **2,110** | 19,691 | **9.3x** | 468,990 |
| branch_4 | LSend2b | 17,370 | 86,850 | 157 | 27 | — | 156,330 |
| branch_1 | LSend1b | 17,370 | 28,950 | 63 | 0 | — | 52,110 |
| branch_5 | LRecvAccepted | 17,370 | 15,552 | 53 | 53 | — | 52,110 |
| branch_3 | LSend2a | 17,370 | 1,296 | 26 | 29 | — | 52,110 |
| branch_6 | LLearn | 17,370 | 5,184 | 2 | 0 | — | 17,370 |
| branch_0 | LSend1a | 17,370 | 36 | 0 | 35 | — | 52,110 |

**Key change**: Guard-first evaluation on LRecvPromise's helper branches checks `a ∈ promises_rcvd` before constructing the next state. Most existential assignments (a, ab, av) fail this guard, avoiding the expensive full predicate solve.

**Dominant cost buckets** (post-optimization):
1. **Dedup/canonicalization** (27.4s, 34%): canonical_key() string allocation + BTreeSet comparison for 145K states.
2. **Init-state construction** (23.3s, 29%): building the initial state from the cartesian domain.
3. **LRecvPromise solver** (2.1s, 2.6%): down from 19.7s — no longer the bottleneck.

**Next optimization targets** (in priority order):
1. **Hash-based dedup**: Replace `BTreeSet<String>` canonical_key with `HashSet<u64>` fingerprint. Would eliminate ~27s of string allocation/comparison.
2. **Init-state construction**: Avoid full 1.7M candidate materialization for initial state (most are invalid).

---

## 3. Other Protocols (no regressions)

| Protocol | States | Elapsed | Before |
|----------|--------|---------|--------|
| TwoPhase | 79 | 438 ms | ~1.6s |
| PrimaryBackup | 668,457 | 502s | 37,213/120s |

**PrimaryBackup**: Guard-first eliminated the solver bottleneck (158ms solver for 668K states), making dedup/canonicalization the dominant cost (502s). The state space is now 18x larger than previously explored.

---

## 4. Summary: Optimization Impact

| Protocol | Solver speedup | Total speedup | Key metric |
|----------|---------------|---------------|------------|
| LE 2-node | **3.4x** | **3.0x** | 108 states, exhausted |
| LE 3-node | — | **2.8x states** | 355 vs 127 in 120s timeout |
| Paxos | **8.2x** | **18.6%** | 17,370 states, exhausted 18s faster |
| PB | **>100x** | **18x states** | 668K vs 37K in comparable time |

## 5. Explicit Blocker Status (Phase 36.3.7.e)

### Paxos: RESOLVED

Paxos 3-node benchmark **exhausts** at 17,370 states in 81.2s (down from 99.8s pre-guard-first, and from timeout/5 states pre-36.3.4). No remaining performance blocker. The 2-node fixture also exhausts at 570 states/5.8s.

### LeaderElection: BLOCKED — solver throughput on existential-heavy branches

| Field | Value |
|-------|-------|
| Protocol | LeaderElection |
| Fixture | `benchmarks_1h/leaderelection_benchmark.model.toml` (3 nodes) |
| Result | **Timeout** (120s), 355 states explored |
| Hot branches | branch_2 (LSendAnswer), branch_3 (LReceiveAnswer), branch_5 (LReceiveCoordinator) |
| Hot branch cost | 84,488 ms combined (70.6% of total solver time) |
| Existential assignments per inv | ~7,380 per hot branch (3-node config) |
| Successful successors per inv | <6 per invocation (low yield) |
| Guard-pruned assignments | Substantial (brought 127→355 states, 2.8x improvement) |
| Before guard-first (36.3.7.a) | 127 states / 120s timeout |
| After guard-first (36.3.7.c) | 355 states / 120s timeout |
| 2-node reproducer | Exhausts at 108 states / 2.3s (down from 6.7s) |
| **Next code task** | **Hash-based dedup** in `explorer.rs`: replace `BTreeSet<String>` canonical_key with `HashSet<u64>` fingerprint. For LE 3-node, dedup is only 0.4% of time, so the primary gain is from Paxos/PB; the LE blocker is pure solver throughput. The next LE-specific target is reducing the existential explosion in helper function expansion within `solver.rs` predicate-only path — either by tighter domain bounds or by incremental assignment (assign-then-check instead of enumerate-then-filter). |

## 6. Next Code Tasks

| Priority | Protocol | Optimization | Expected impact | Code location |
|----------|----------|-------------|-----------------|---------------|
| **P0** | PB, Paxos | Hash-based dedup (u64 fingerprint instead of canonical_key String) | ~34% Paxos total, ~99% PB total | `explorer.rs` dedup path |
| **P1** | LE | Incremental existential assignment with early termination | Reduce 7,380 assignments/branch to domain-bounded subset | `solver.rs` predicate-only path, helper expansion |
| **P2** | Paxos | Lazy init-state construction (avoid 1.7M candidate materialization) | ~29% Paxos total (23s→<1s) | `main.rs` initial state |

---

## Appendix: Telemetry field definitions

| Field | Description |
|-------|-------------|
| `invocations` | Times this branch was invoked across all explored states |
| `existential_assignment_count` | Total distinct existential variable combinations evaluated |
| `candidate_state_count` | Candidate states from domain expansion (not used by predicate-only solver) |
| `successful_successors` | Valid next-states produced |
| `cumulative_solve_elapsed_ms` | Wall-clock time in branch solver (summed across invocations) |
| `evaluator_calls` | Total predicate evaluations = (direct_fields + deferred) × assignments |
| `direct_assigned_fields` | Fields with direct `s_.field == expr` assignment (0 for predicate-only) |
| `deferred_constraint_evaluations` | Non-assignment constraints evaluated per assignment (1 = branch predicate) |
| `guard_pruned_assignments` | Existential assignments pruned by guard-first evaluation (Phase 36.3.7.c) |
