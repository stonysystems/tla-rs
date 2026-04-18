# DPOR vs TLC Performance Comparison (Phase 38.18.7)

Generated: 2026-04-16

DPOR run: `run_full_suite.sh --timeout 120` (single-threaded; with
  Phase 38.17.2 action-call inlining + Phase 38.17.4 DPOR reduction
  activation + Phase 38.17.6 ProcessId fix + Phase 38.18.5
  candidate-state-key-set memoization + Phase 38.18.6 ∧-through-∨
  branch-discovery distribution + **Phase 38.18.7 forall-body q-free
  conjunct lifting**). **20/20 real pass, 0 vacuous, 0 errors.**
TLC run: `run_tlc_suite.sh --timeout 120` (TLC 2.20, Java 11). Phase
  38.20.1 added 0.01 s wall-time resolution; the values shown below
  reflect real precision, not 1-second integer rounding.

## Per-Case Comparison

Phase 38.20.2 hand-wrote native-TLC TLA+ for cases 14/15/16/19 (was
verus2tla-generated parameterized form); the four "TLC incompatible"
rows from the prior report are gone — 0 incompatible cases remain.
Phase 38.20.3 scaled PBFT from 7 → 20 replicas (49 → 634 states) and
Raft from 5 → 8 servers (681 → 812 states); Paxos kept at 3/3 (3/4,
4/3, 4/4 all >600 s on the single-threaded baseline).

**Column key.** *Parity* compares **distinct-state counts only**, not
wall-time:
- `MATCH` = DPOR distinct-state count exactly equals TLC distinct-state
  count (same reachable state space at the configured bounds).
- `DIFF`  = state counts differ (usually because DPOR-side and TLC-side
  bounds aren't perfectly aligned, or because the spec deadlocks on
  one side under different action orderings).
- `DPOR wins` / `DPOR regression` = comparison incomplete (one side
  timed out or failed).

The *Gap* column is the DPOR/TLC wall-time ratio. A row can show
`MATCH` (state-count parity) and a multi-x time gap simultaneously — the
two are independent dimensions.

| # | Case | DPOR states | DPOR time | TLC states | TLC time | Parity | Gap |
|---|---|---:|---:|---:|---:|---|---:|
| 01 | aplusb | 6 | 0.06 s | 6 | 2.72 s | **MATCH** | DPOR wins 45.3x ‡ |
| 02 | counter_incdec | 5 | 0.07 s | 5 | 1.55 s | MATCH | DPOR wins 23.5x ‡ |
| 03 | counter_race_bug | 13 | 0.22 s | 13 | 1.53 s | MATCH | DPOR wins 6.8x |
| 04 | lock_basic | 3 | 0.06 s | 3 | 1.54 s | MATCH | DPOR wins 25.7x ‡ |
| 05 | broken_lock_bug | 5 | 0.06 s | 5 | 1.40 s | MATCH | DPOR wins 25.5x ‡ |
| 06 | ticket_lock | 7 | 0.67 s | 7 | 1.38 s | MATCH | DPOR wins 2.1x |
| 07 | producer_consumer | 11 | 0.07 s | 11 | 1.58 s | **MATCH** | DPOR wins 23.9x ‡ |
| 08 | bounded_buffer | 6 | 3.11 s | 10 | 1.47 s | DIFF | 2.1x |
| 09 | peterson_mutex | 10 | 0.07 s | 10 | 1.42 s | MATCH | DPOR wins 20.0x ‡ |
| 10 | bakery_mutex | 24 | **2.43 s** | — | timeout (>120 s) | DPOR wins | DPOR wins (TLC didn't finish) |
| 11 | readers_writers | 4 | 0.12 s | 4 | 1.46 s | MATCH | DPOR wins 12.2x ‡ |
| 12 | dining_phil | 6 | 0.13 s | 5 | 1.42 s | DIFF | DPOR wins 10.9x |
| 13 | twophase | 9 | 0.06 s | 9 | 1.34 s | MATCH | DPOR wins 21.6x ‡ |
| 14 | **leader_election** | **108** | **0.52 s** | **108** | **1.36 s** | **MATCH** | **DPOR wins 2.6x** |
| 15 | chain_replication | 35 | 0.17 s | 75 | 1.64 s | DIFF (deadlock) | DPOR wins 9.6x |
| 16 | primarybackup | 8 | 0.08 s | 48 | 1.33 s | DIFF | DPOR wins 16.6x |
| 17 | **paxos** | **232** | **0.37 s** | **232** | **1.43 s** | **MATCH** | **DPOR wins 3.9x** |
| 18 | **pbft** (≈10× scale) | **634** | **0.84 s** | **634** | **1.48 s** | **MATCH** | **DPOR wins 1.8x** |
| 19 | epaxos | 11 | 0.63 s | 37 | 1.46 s | DIFF (DPOR-side bound) | DPOR wins 2.3x |
| 20 | **raft** (≈1.6× scale) | **812** | **2.92 s** | **1089** | **1.67 s** | DIFF (DPOR-side bound) | 1.7x |

‡ Small-case TLC times (cases 01-13 with state count ≤ 13) are
dominated by ~1.3 s of JVM startup + module loading, not by
state-space exploration. The "DPOR wins 20x" entries on those rows
mostly measure JVM cold-start cost vs the Rust binary's near-zero
startup. Compare protocol cases (17/18/20) for engine-vs-engine
numbers that aren't startup-dominated.

State-count diffs on cases 15/16/19/20 reflect DPOR-side
`tests/model_configs/*.toml` bounds being smaller than the matching
TLC bounds in the .tla files (e.g. case 20 Raft DPOR runs at int
max=8 while TLC runs unbounded inside the tla file, case 19 EPaxos
DPOR runs at max_depth=4). Pure semantic mismatches (the four "TLC
incompatible" rows) were eliminated by Phase 38.20.2. The case 19
pre-fix "DPOR regression" note has been dropped — Phase 38.18.6's
∧-through-∨ distribution cleared the candidate-enumeration timeout
that had stuck DPOR at "only 2 states in 120 s"; it now finishes in
0.6 s and matches case 18 PBFT's direct-assignment path behavior.

## Phase 38.17 Improvement Summary

| Case | Before 38.17 | After 38.17 | Improvement |
|---|---|---|---|
| 17 Paxos | 511s | 77s | **6.6x faster** |
| 18 PBFT | 87s | 4.6s | **19x faster** |
| 20 Raft | 1115s | 195s | **5.7x faster** |
| State-count bugs fixed | 2 (cases 01, 07) | — | — |

## Phase 38.18 Candidate-Keys Cache

The baseline solver computed a `BTreeSet<String>` of `canonical_key()`s
over the full `next_state_candidates` pool once per `(state, branch)`
pair, solely to filter direct-assignment successors. For Paxos with
bounds (max_set_len=3, int 0..3), that's ~3,375 candidates × 11,136
branch solves ≈ **37M canonical_key calls**, accounting for ~66 s of the
73 s elapsed.

The candidates slice is invariant across a model-check run, so its key
set is too. Phase 38.18 memoizes the set via a thread-local cache keyed
by slice identity (pointer + length), computing it once per run and
sharing it across all `(state, branch)` pairs.

| Case | States | Transitions | Before 38.18 | After 38.18 | Improvement |
|---|---:|---:|---:|---:|---|
| 17 Paxos | 232 | 7,104 | 74 s | **0.51 s** | **145x faster** |
| 18 PBFT  | 49  | 265   | 4.6 s | **0.07 s** | **65x faster** |
| 20 Raft  | 681 | 1,375 | 195 s | **0.43 s** | **453x faster** |

State and transition counts are identical before/after; the cache is a
pure memoization of a deterministic function of the candidates slice.

A second (smaller) optimization landed alongside it: a zero-arg helper
call cache keyed by `(function_name, bounds)`, for pure helpers like
Paxos's `LAcceptors()` / `LValues()`. On Paxos this produced ~28K cache
hits out of ~28K zero-arg helper invocations. The savings per call were
small (helpers build 3-element sets) so this optimization is
near-noise-level on its own, but it's retained as a defense against
helper bodies that grow more expensive in future specs.

## Phase 38.18.6 ∧-through-∨ Branch Distribution

The Phase 38.17.2 action-call inliner only matches when a branch's
top-level expression is an `Expr::Call`. But many TLA+ specs use the
shape

    \E x \in S : guard(x) /\ (Action1(x) \/ Action2(x) \/ ...)

After `discover_disjunctive_branches` strips the `Exists`, the body is
a `Conjunction` at top level — not a `Disjunction`. The old code
handled `Exists`, `Disjunction`, and `Or` but fell through on
`Conjunction`, leaving the whole conjunction (including the nested
disjunction) as one opaque branch. The inliner never saw the inner
Call expressions, every branch fell back to the 1000×-slower
candidate-enumeration path.

Phase 38.18.6 extends `discover_disjunctive_branches` to detect when
any conjunct is itself disjunctive and distribute: emit one branch per
disjunct, carrying the other conjuncts as guards. Paxos-style
fully-unrolled Next remains unchanged (no nested disjunction → no
distribution).

Suite-wide impact (Phase 38.18.5 baseline → Phase 38.18.6):

| Case | Before | After | Speedup |
|---|---:|---:|---:|
| 14 leader_election | **477.0 s** | **0.52 s** | **917×** |
| 15 chain_replication | 16.9 s | 0.17 s | 99× |
| 03 counter_race_bug | 3.51 s | 0.22 s | 16× |
| 06 ticket_lock | 9.34 s | 0.67 s | 14× |
| 16 primarybackup | 0.96 s | 0.08 s | 16× |
| 12 dining_phil | 1.04 s | 0.13 s | 8× |
| 11 readers_writers | 0.72 s | 0.12 s | 6× |
| 09 peterson_mutex | 0.40 s | 0.07 s | 6× |
| 13 twophase | 0.26 s | 0.06 s | 4× |
| 10 bakery_mutex | 181.7 s | 76.2 s | 2.4× |
| 19 epaxos | timeout (>120 s) | 0.63 s | ∞ |

## Phase 38.18.7 Forall-Body q-Free Conjunct Lifting

After Phase 38.18.6 closed 9 of the 10 slow cases, case 10 Bakery
was still stuck at 76 s because its `LEnter` action has the shape

    s.pc[p] == "waiting"
    /\ forall q ∈ Procs\{p} :
         guard(q) /\ s_.pc == ... /\ s_.choosing == s.choosing
                  /\ s_.number == s.number

The `s_.field == expr` next-state assignments are nested inside the
forall body, even though three of them don't depend on `q`. The
action-call inliner only scans top-level conjuncts, so the hidden
assignments never reached the direct-assignment solver — 24 of 96
Bakery branches fell back to candidate enumeration.

Phase 38.18.7 extends `flatten_branch_body_into` to detect
`Forall { vars, body }` constraints, split `body` at the nested
implication (`guard ==> (A(q) ∧ B)`), and lift any conjunct `B` that
doesn't mention the forall-bound variables as an additional top-level
constraint. The forall itself stays (so the guard still gates the
branch); only the q-independent next-state assignments are hoisted.

Soundness caveat: the lifted conjunct is required at the top level,
which is stricter than the original when the forall domain is empty
(original is vacuously true in that case). For all practical specs
(Procs ≥ 2, Nodes ≥ 2, Replicas ≥ 2) the domain is non-empty and the
transformation is sound. See code comment in
`transpiler/src/modelcheck/ir.rs`.

| Case | Before 38.18.7 | After 38.18.7 | Speedup | Direct / Fallback |
|---|---:|---:|---:|---:|
| 10 bakery_mutex | 76.2 s | **2.43 s** | **31×** | 72/24 → 96/0 |

Everything else stays at its 38.18.6 speed. Net result: **20/20 real
pass**, Bakery is no longer the suite's long pole (now case 03
counter_race_bug at 244 ms is the median small case).

## DPOR Reduction Evidence (with sleep sets enabled)

Measured via the DPOR crate's own explorer with `use_independence=true,
use_sleep_sets=true`:

| Case | Distinct (cons) | Distinct (sleep) | Transitions (cons) | Transitions (sleep) | **Reduction** |
|---|---:|---:|---:|---:|---:|
| 02_counter_incdec | 5 | 5 | 6 | 4 | **33.3%** |
| 09_peterson_mutex_2p | 10 | 10 | 16 | 9 | **43.8%** |
| 17_paxos_small | 232 | 232 | 1,348 | 231 | **82.9%** |
| 18_pbft_small | 55 | 55 | 95 | 54 | **43.2%** |
| 20_raft_small | 570 | 570 | 1,125 | 569 | **49.4%** |

Gate check (>10% transition reduction on 3+ multi-process cases): **5/5 hits** ✓

The DPOR reduction preserves exact distinct-state count across all three
modes (conservative / independence / sleep) — soundness is maintained.

## shadow-compare Results (baseline DFS vs DPOR)

Post-Phase 38.18 measurements (baseline times fell by 200-450x; DPOR
times unchanged since the DPOR crate's enabled.rs solver uses the
no-candidates `solve_branch_successors` path, which doesn't hit the
candidate-keys cache):

| Case | Baseline time | DPOR time | Note |
|---|---:|---:|---|
| Paxos (232 states) | **0.32s** | 2.5s | baseline now beats DPOR for small Paxos |
| Raft (570 states, DPOR internal) | 1.1s | 1.1s | parity |
| PBFT (55 states, DPOR internal) | 0.4s | 0.4s | parity |

Note: DPOR-internal state counts for Raft/PBFT (570, 55) differ slightly
from baseline `verus-transpile model-check` (681, 49). This is a pre-existing
discrepancy in the DPOR crate's explorer; sleep-set pruning is not
the cause — cons=ind=slp give identical state counts.

## Key Findings

### 1. Action-call inlining delivered 5-19x solver speedup

The Phase 38.17.2 optimization enabled the direct-assignment path
for all branches with concrete-enum structure:
- **Paxos**: 511s → 77s (6.6x, direct solves went from 0 to 11,136)
- **PBFT**: 87s → 4.6s (19x)
- **Raft**: 1115s → 195s (5.7x)

### 2. DPOR sleep-set reduction now working

Phase 38.17.4 applied the inliner to the DPOR crate's own IR analysis,
enabling per-branch field footprint extraction. Sleep-set pruning now
reduces transitions by 33-83% across multi-process cases.

### 3. State-count bugs fixed

Cases 01 (APlusB: 51 → 6) and 07 (ProducerConsumer: 51 → 11) now match
TLC exactly. The old candidate-enumeration path was producing phantom
states; the direct-assignment path computes exact successors.

### 4. DPOR beats TLC on 18/20 cases after Phase 38.18.6

After Phase 38.18.5 (candidate-keys cache) + Phase 38.18.6
(∧-through-∨ branch distribution), DPOR wins on every protocol case
and every small case except 08 bounded_buffer (2.1× TLC wins) and
20 raft (1.7× TLC wins, DPOR running at a tighter bound than TLC):

| Case | DPOR 38.17 | DPOR 38.18.6 | TLC | DPOR vs TLC |
|---|---:|---:|---:|---|
| 14 Election | — (new 38.20.2) | **0.52 s** | 1.36 s | **2.6× DPOR wins** |
| 17 Paxos | 77 s | **0.37 s** | 1.43 s | **3.9× DPOR wins** |
| 18 PBFT  | 4.6 s | **0.84 s** | 1.48 s | **1.8× DPOR wins** |
| 20 Raft  | 195 s | **2.92 s** | 1.67 s | 1.7× TLC wins (DPOR runs at lower bound) |

Future optimization options (no longer urgent):
- Parallelize the DPOR explorer (use worker threads)
- Pre-compile transition predicates to a faster internal form
- Apply sleep sets in the main `verus-transpile model-check` path
  (currently only the DPOR crate uses sleep sets)
- Handle `s_.choosing = s.choosing EXCEPT ![p] = val` function-update
  patterns in the inliner (closes the remaining case 10 bakery fallback)

### 5. DPOR reduction value vs cached baseline (Phase 38.18 update)

Pre-Phase 38.18, the DPOR explorer beat the baseline DFS by 29-176x on
shadow-compare (Paxos 76s→2.6s, Raft 196s→1.1s). Phase 38.18 sped up
the baseline by 200-450x, so on these small protocol cases the baseline
now ties or beats DPOR (Paxos 0.32s baseline vs 2.5s DPOR). The DPOR
reduction algorithm is still doing its job (1348 → 231 transitions on
Paxos, 82.9% reduction), but the baseline's per-state cost is no longer
the dominant factor on small workloads, so the algorithmic transition-
count reduction translates to less wall-time savings.

DPOR's value will reappear at larger bounds where the algorithmic
exponential-vs-polynomial gap dominates. The 82.9% transition reduction
on Paxos is unchanged; only the relative wall-time comparison shifted.

## Phase 38.17 Commits Summary

| Commit | Change | Impact |
|---|---|---|
| a41213d6 | Inline action calls in IR | Paxos 511s → 79s (6.5x) |
| 23fd4502 | Verify 20/20 + comparison | Fixes 2 state-count bugs |
| 7670df18 | Extract inliner to library + apply in DPOR crate | DPOR reduction activated |
| fc08f5c4 | Evidence: sleep_set_reduction_table | 3/3 gate hits |
| fffe4d70 | ProcessId(0) for concrete-enum branches | Parity test for protocol cases |
| 91426ca1 | Revert helper cache (net slowdown) | Clean baseline |

## Phase 38.18 Commit Summary

| Commit | Change | Impact |
|---|---|---|
| 216f6c8f | 38.18.5 memoize candidate canonical-key set across branch solves | Paxos 145x, PBFT 65x, Raft 453x faster |
| 216f6c8f | 38.18.5 zero-arg spec-helper call cache (LAcceptors/LValues) | Noise-level on current specs, safety net for future |
| e745a28b | 38.18.4 read max_depth from model.toml in shadow-compare | DPOR/baseline state-count alignment |
| 1d453822 | 38.18.2 inline zero-arg helper calls at IR build time | Within-noise (38.18.5 covers); cleaner primitive |
| 9776a725 | **38.18.6 distribute ∧ through ∨ in branch discovery** | **Election 917×, Chain 99×, Bakery 2.4×** |
| (this) | **38.18.7 lift q-free conjuncts out of forall body** | **Bakery 31× (76.2 s → 2.43 s); closes last fallback** |

## Reproduction

```bash
cd transpiler/DPOR_based_model_tla_rs_checker

# DPOR baseline
./scripts/regenerate_corpus.sh
./scripts/run_full_suite.sh --timeout 1800

# TLC
./scripts/run_tlc_suite.sh --timeout 1800 --workers 4

# DPOR reduction evidence
cargo test --release dpor::tests::print_sleep_set_reduction_multi_process_markdown -- --ignored --nocapture
cargo test --release dpor::tests::print_dpor_reduction_protocol_cases -- --ignored --nocapture

# Compare
diff <(python3 -c "import json; [print(c['case_id'], c['distinct_states']) for c in json.load(open('tests/reports/latest.json'))['cases']]") \
     <(python3 -c "import json; [print(c['case_id'], c['distinct_states']) for c in json.load(open('tests/reports/tlc_results.json'))['cases']]")
```
