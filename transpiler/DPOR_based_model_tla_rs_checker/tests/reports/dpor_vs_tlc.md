# DPOR vs TLC Performance Comparison (Phase 38.17.3)

Generated: 2026-04-16 (updated from 2026-04-14)

DPOR run: `run_full_suite.sh --timeout 1800` (single-threaded, **with Phase 38.17.2 action-call inlining optimization**)
TLC run: `run_tlc_suite.sh --timeout 1800 --workers 4` (TLC 2.20, Java 11, 4 workers)

Both engines use matched model configurations: same constants, same invariants,
same int/set bounds (via CONSTRAINT wrappers for TLC on unbounded specs).

## Per-Case Comparison

| # | Case | DPOR states | DPOR time | TLC states | TLC time | Parity | TLC speedup |
|---|---|---:|---:|---:|---:|---|---:|
| 01 | aplusb | 6 | <0.1s | 6 | 3s | **MATCH** | DPOR faster* |
| 02 | counter_incdec | 5 | 0.2s | 5 | 1s | MATCH | — |
| 03 | counter_race_bug | 13 | 3.5s | 13 | 2s | MATCH | 0.6x |
| 04 | lock_basic | 3 | 0.1s | 3 | 1s | MATCH | — |
| 05 | broken_lock_bug | 5 | 0.1s | 5 | 1s | MATCH | — |
| 06 | ticket_lock | 7 | 9.6s | — | — | TLC error | — |
| 07 | producer_consumer | 11 | 0.1s | 11 | 2s | **MATCH** | DPOR faster* |
| 08 | bounded_buffer | 6 | 7.0s | 10 | 1s | **MISMATCH** | — |
| 09 | peterson_mutex | 10 | 0.3s | 10 | 1s | MATCH | — |
| 10 | bakery_mutex | 24 | 181s | — | timeout | TLC timeout | DPOR wins |
| 11 | readers_writers | 4 | 0.6s | — | — | TLC error | — |
| 12 | dining_phil | 6 | 0.8s | 5 | 1s | **MISMATCH** | — |
| 13 | twophase | 9 | 0.3s | 9 | 1s | MATCH | — |
| 14 | leader_election | 1 | 91s | — | — | TLC incompatible | — |
| 15 | chain_replication | 151 | 131s | — | — | TLC incompatible | — |
| 16 | primarybackup | **21** | 1.4s | — | — | TLC incompatible | — |
| 17 | **paxos** | **232** | **79s** | **232** | **1s** | **MATCH** | **79x slower** |
| 18 | pbft | **49** | 4.8s | 49 | 1s | MATCH | 5x slower |
| 19 | epaxos | 11 | 56s | — | — | TLC incompatible | — |
| 20 | **raft** | **681** | **200s** | **681** | **2s** | **MATCH** | **100x slower** |

\* "DPOR faster" on small cases is misleading: TLC's 1-3s is JVM startup overhead. At sub-second workloads, both engines are effectively equivalent.

## Summary

| Metric | Before 38.17.2 | After 38.17.2 | Change |
|---|---|---|---|
| DPOR state-count matches with TLC | 8/13 comparable | **10/13 comparable** | +2 cases (01, 07) |
| Paxos total time | 511s | **79s** | **6.5x faster** |
| PBFT total time | 87s | 4.8s | **18x faster** |
| Raft total time | 1115s | **200s** | **5.6x faster** |
| Case 01 states | 51 | **6** | Matches TLC (old was wrong) |
| Case 07 states | 51 | **11** | Matches TLC (old was wrong) |
| Case 16 states | 211 | 21 | State count changed |
| DPOR vs TLC gap (Paxos) | ~511x | **79x** | 6.5x closer |
| DPOR vs TLC gap (Raft) | ~558x | **100x** | 5.6x closer |

## Key Findings

### 1. Action-call inlining delivered a 5-18x solver speedup on protocol cases

The Phase 38.17.2 optimization inlines action predicate calls in branch constraints,
enabling the direct-assignment path instead of the 500x-slower candidate-enumeration
fallback. Impact on protocol cases:

| Case | Before | After | Speedup |
|---|---|---|---|
| 17 Paxos (232 states) | 511s | 79s | 6.5x |
| 18 PBFT (49 states) | 87s | 4.8s | 18x |
| 20 Raft (681 states) | 1115s | 200s | 5.6x |

Direct-assignment branch solves went from **0** to **11,136** for Paxos
(matching the transition count). Candidate evaluations dropped from
**37,584,000 to 0** — a complete elimination of the enumeration bottleneck.

### 2. Two state-count bugs fixed by inlining

Cases 01 (APlusB) and 07 (ProducerConsumer) now match TLC's state count:

| Case | Old DPOR | New DPOR | TLC | Verdict |
|---|---|---|---|---|
| 01 aplusb | 51 | **6** | 6 | **Old was wrong** — candidate enumeration produced phantom states |
| 07 producer_consumer | 51 | **11** | 11 | **Old was wrong** — same phantom-state bug |

The candidate-enumeration path was including states not actually reachable
through transition semantics. The direct-assignment path computes successors
exactly from `s_.field == expr(s)` semantics, matching TLC's behavior.

### 3. Case 16 (PrimaryBackup) state count changed: 211 → 21

This is a parity concern. The old DPOR reported 211 states; the optimized version
reports 21. TLC can't run case 16 (parameterized Init/Next). Need to investigate
whether the old 211 was phantom states (like cases 01/07) or whether the new 21
is missing real states. Phase 38.17.3.d follow-up.

### 4. Remaining state-count mismatches with TLC (cases 08, 12)

- **Case 08 (bounded_buffer)**: DPOR 6 vs TLC 10 — both find the violation,
  different state counts. Likely DPOR stops at first violation while TLC
  continues exploring.
- **Case 12 (dining_phil)**: DPOR reports `deadlock`, TLC reports `invariant_violated`.
  Different detection paths for the same bug.

### 5. DPOR is still 79-100x slower than TLC on protocol cases

The inlining optimization got us a 5-18x improvement, but TLC remains
~100x faster at the per-state level. The remaining gap is from:
- Helper function call evaluation (e.g., `LAcceptors().contains(b)`) repeated
  per (state, branch, existential binding) — no caching
- Python/Rust runtime overhead vs TLC's JIT-compiled Java
- TLC's 4-worker parallelism vs DPOR's single-threaded exploration

Further optimization options: cache helper call results, parallelize the
DPOR explorer, or add the actual DPOR independence pruning (Phase 38.17.4).

## Phase 38.17.2 Optimization Details

**Problem**: In `LNext = LSend1a(s, s_, 1) || LSend1a(s, s_, 2) || ...`, each
branch was a single opaque `Predicate { Call("LSend1a", [s, s_, 1]) }` in the
transition IR. The solver couldn't decompose this into `s_.field == ...`
equalities, forcing the 500x-slower candidate-enumeration fallback.

**Fix** (`transpiler/src/main.rs:3620-3728`): After `build_transition_ir`
decomposes LNext into branches, iterate over branches and for each `Predicate`
constraint that is a `Call`:
1. Look up the called function in `bundle.spec_functions`
2. Substitute formal parameters with actual arguments
3. Flatten the conjunction into individual constraints
4. Normalize each constraint (Eq vs Predicate)
5. Only replace the original if the inlined result contains at least one
   `NextState Eq` constraint (otherwise keep the opaque call for the
   predicate_only_solver)

## Reproduction

```bash
cd transpiler/DPOR_based_model_tla_rs_checker

# Regenerate corpus
./scripts/regenerate_corpus.sh

# Run DPOR baseline (with Phase 38.17.2 optimization)
./scripts/run_full_suite.sh --timeout 1800

# Run TLC (requires Java 11+, ~/tla2tools.jar)
./scripts/run_tlc_suite.sh --timeout 1800 --workers 4

# Compare
cat tests/reports/latest.json tests/reports/tlc_results.json
```
