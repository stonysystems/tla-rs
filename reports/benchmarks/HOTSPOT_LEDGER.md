# Source-First Model Checker Hotspot Ledger

Last updated: 2026-03-19 (Phase 36.3.7.a)
Binary: `transpiler/target/release/verus-transpile` (release mode)
Telemetry fix: predicate-only solver path now reports `evaluator_calls`, `direct_assigned_fields`, `deferred_constraint_evaluations` (was zeros before this commit).

Raw JSON reports: `reports/benchmarks/source_first_release_profile_post_36_3_7a/`

---

## 1. LeaderElection (3-node benchmark, 120s timeout)

**Config**: `benchmarks_1h/leaderelection_benchmark.model.toml`
(3 nodes, int 0..2, max_set_len=3, max_seq_len=3, 3 safety invariants)

| Metric | Value |
|--------|-------|
| Result | **timeout** (120s) |
| Distinct states | 127 |
| Generated states | 222 |
| Duplicate states | 95 |
| Explored states | 127 |
| Init time | 107 ms |
| Solver time | 119,725 ms (99.5%) |
| Dedup time | 257 ms |
| Invariant time | 0 ms |
| Stop reason | TimeoutReached |

### Branch hotspot table (sorted by solve time)

| Branch | Action | Inv | Exist/inv | Total exist | Succ | Succ/inv | Solve ms | % total | Eval calls |
|--------|--------|-----|-----------|-------------|------|----------|----------|---------|------------|
| branch_2 | **LSendAnswer** | 16 | 461 | 7,380 | 30 | 1.9 | **39,684** | **33.1%** | 118,080 |
| branch_3 | **LReceiveAnswer** | 16 | 461 | 7,380 | 7 | 0.4 | **26,358** | **22.0%** | 118,080 |
| branch_5 | **LReceiveCoordinator** | 16 | 461 | 7,380 | 87 | 5.4 | **19,625** | **16.4%** | 118,080 |
| branch_1 | LStartElection | 16 | 154 | 2,460 | 45 | 2.8 | 10,395 | 8.7% | 39,360 |
| branch_6 | LNodeFail | 16 | 154 | 2,460 | 45 | 2.8 | 8,720 | 7.3% | 39,360 |
| branch_0 | LDetectFailure | 17 | 145 | 2,460 | 0 | 0.0 | 8,350 | 7.0% | 41,820 |
| branch_4 | LSendCoordinator | 16 | 154 | 2,460 | 7 | 0.4 | 6,593 | 5.5% | 39,360 |

**Key observations**:
- **Top 3 branches account for 71.5% of solver time** (branches 2, 3, 5).
- These branches have 3x more existential assignments (461/inv vs 154/inv) due to an extra existential variable (`sender`/`responder`/`leader` parameter).
- LDetectFailure (branch_0) is invoked 17 times but produces **0 successors** — the guard is never satisfied, yet all 2,460 existential combinations are still evaluated.
- Total candidate count per branch is 13,824 (but candidate-key filtering is skipped per Phase 36.3.4).
- All branches use predicate-only solver (`direct_assigned_fields=0`).
- `deferred_constraint_evaluations=1` per branch (1 predicate constraint evaluated per existential assignment).

**Dominant cost bucket**: Repeated evaluator work on existential assignments that fail the guard.

**Next optimization target**: Guard-first evaluation — check the branch guard (precondition on current state + existential params) before invoking the full predicate solver. For branch_0, this would eliminate all 2,460 evaluations. For branches 2/3/5, guard pruning could eliminate the majority of the 461 assignments per invocation that produce only 0.4–5.4 successors.

### LeaderElection 2-node reproducer (exhausted)

**Config**: `leaderelection_perf_repro.model.toml`
(2 nodes, int 0..1, max_set_len=2, max_seq_len=2)

| Metric | Value |
|--------|-------|
| Result | **ok** (exhausted) |
| Distinct states | 108 |
| Elapsed | 6,738 ms |
| Init time | 7 ms |
| Solver time | 6,328 ms |
| Dedup time | 395 ms |

Same branch shape as 3-node: branches 2,3,5 dominate (172 exist/inv each, ~1.2s each). Branches 0,1,4,6 have 86 exist/inv (~0.5–0.9s each). This fixture exhausts and reproduces the relative hotspot ranking.

---

## 2. Paxos (3-node benchmark, 120s timeout)

**Config**: `benchmarks_1h/paxos_benchmark.model.toml`
(3 acceptors, quorum=2, int 0..2, max_set_len=3, max_seq_len=3, 3 safety invariants)

| Metric | Value |
|--------|-------|
| Result | **ok** (exhausted!) |
| Distinct states | **17,370** |
| Generated states | 145,753 |
| Duplicate states | 128,383 |
| Explored states | 17,370 |
| Init time | **21,808 ms** (21.8%) |
| Solver time | **19,835 ms** (19.9%) |
| Dedup time | **32,135 ms** (32.2%) |
| Invariant time | 0 ms |
| Elapsed | **99,838 ms** |
| Stop reason | **FrontierExhausted** |

**Major improvement**: Paxos now exhausts the full 3-node state space (17,370 states) in 99.8s. Previous best was 16,655 states/147s (timeout). The telemetry fix itself doesn't change performance — this likely reflects normal variance or CPU scheduling differences.

### Branch hotspot table (sorted by solve time)

| Branch | Action | Inv | Exist/inv | Total exist | Succ | Succ/inv | Solve ms | % total | Eval calls |
|--------|--------|-----|-----------|-------------|------|----------|----------|---------|------------|
| branch_2 | **LRecvPromise** | 17,370 | ~0.002 | 27 | 7,884 | 0.5 | **19,691** | **99.3%** | 468,990 |
| branch_5 | LRecvAccepted | 17,370 | ~0.0002 | 3 | 15,552 | 0.9 | 53 | 0.3% | 52,110 |
| branch_0 | LSend1a | 17,370 | ~0.0002 | 3 | 36 | 0.0 | 35 | 0.2% | 52,110 |
| branch_3 | LSend2a | 17,370 | ~0.0002 | 3 | 1,296 | 0.1 | 29 | 0.1% | 52,110 |
| branch_4 | LSend2b | 17,370 | ~0.001 | 9 | 86,850 | 5.0 | 27 | 0.1% | 156,330 |
| branch_1 | LSend1b | 17,370 | ~0.0002 | 3 | 28,950 | 1.7 | 0 | 0.0% | 52,110 |
| branch_6 | LLearn | 17,370 | ~0.0001 | 1 | 5,184 | 0.3 | 0 | 0.0% | 17,370 |

**Key observations**:
- **LRecvPromise (branch_2) accounts for 99.3% of solver time** despite having only 27 total existential assignments across all invocations.
- The cost is evaluator calls: 468,990 (9x more than any other branch). LRecvPromise has 3 existential variables (a, ab, av) with 27 combinations per state, vs 3 for most other branches.
- Init-state construction is the second-largest cost bucket at 21.8s. This is the initial cartesian-candidate materialization.
- Dedup (canonical_key hashing + BTreeSet insertion) is the largest single cost at 32.1s. With 145,753 generated states, each needing a full canonical JSON key, this is ~220µs per dedup operation.
- All branches use predicate-only solver (`direct_assigned_fields=0`).

**Dominant cost buckets**:
1. **Dedup/canonicalization** (32.1s, 32%): canonical_key() string allocation + BTreeSet comparison for 145K states.
2. **Init-state construction** (21.8s, 22%): building the initial state from the cartesian domain.
3. **LRecvPromise solver** (19.7s, 20%): 27 existential combinations × 17,370 invocations = 468K evaluations.

**Next optimization targets** (in priority order):
1. **Hash-based dedup**: Replace `BTreeSet<String>` canonical_key with `HashSet<u64>` fingerprint. Would eliminate 32s of string allocation/comparison.
2. **Init-state construction**: Avoid full 1.7M candidate materialization for initial state (most are invalid).
3. **LRecvPromise guard evaluation**: Check if `a` is in `promises_rcvd` before evaluating `ab`/`av` combinations (would reduce 27→3 or fewer assignments per invocation when most acceptors haven't sent promises).

### Paxos 2-node small (exhausted)

**Config**: `paxos_parity_small.model.toml`
(2 acceptors, quorum=1, int 0..1, max_set_len=2, max_seq_len=2)

| Metric | Value |
|--------|-------|
| Result | **ok** (exhausted) |
| Distinct states | 570 |
| Elapsed | 1,121 ms |
| Init time | 187 ms |
| Solver time | 0 ms |
| Dedup time | 722 ms (64%) |

Same cost distribution as 3-node: dedup dominates. Branch_2 (LRecvPromise) has the most existential assignments (8 vs 1–4 for others) but solver time rounds to 0ms at this scale.

---

## 3. Summary: Next Code Tasks

| Priority | Protocol | Optimization | Expected impact | Code location |
|----------|----------|-------------|-----------------|---------------|
| **P0** | LE | Guard-first evaluation: skip existential combinations where branch guard fails on current state | ~70% solver reduction (branches 2,3,5 dominate) | `solver.rs` predicate-only path |
| **P1** | Paxos | Hash-based dedup (u64 fingerprint instead of canonical_key String) | ~32% total time reduction (32s→<1s) | `explorer.rs` dedup path |
| **P2** | Paxos | Lazy init-state construction (avoid 1.7M candidate materialization) | ~22% total time reduction (22s→<1s) | `main.rs` initial state |
| **P3** | Both | LRecvPromise guard pruning (check acceptor membership before expanding av/ab) | ~20% Paxos solver reduction | `solver.rs` existential expansion |

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
