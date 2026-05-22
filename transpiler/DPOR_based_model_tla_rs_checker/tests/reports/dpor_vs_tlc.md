# DPOR vs TLC Performance Comparison (Phase 38.16.5 / 38.21)

Generated: 2026-05-22 (Phase 38.16.3.b scaled configs)

DPOR run: `run_full_suite.sh --timeout 1800` (single-threaded; all
  optimizations through Phase 38.21.J). **20/20 real pass, 0 vacuous.**
TLC run: `run_tlc_suite.sh --timeout 300 --workers 4` (TLC 2026.03,
  Java 17). **19/20 pass, 1 timeout (case 10 BakeryMutex).**

## Per-Case Comparison (Phase 38.16.3 Scaled Configs)

All configs scaled to maximize distinct states (Phase 38.16.3.a+b).
Cases 01 and 07 use linear state chains (depth 6000/10000); protocol
cases use widened constants and deeper search.

**Column key.** *Parity* compares distinct-state counts:
- `MATCH` = exact state-count agreement between DPOR and TLC.
- `DIFF`  = state counts differ (different bounding mechanisms or
  exploration order on negative cases).
- `TIMEOUT` = one engine didn't finish within budget.

| # | Case | DPOR states | DPOR time | TLC states | TLC time | Parity | Notes |
|---|---|---:|---:|---:|---:|---|---|
| 01 | aplusb | 6,001 | 0.21 s | 5,001 | 0.90 s | DIFF | TLC CONSTRAINT cuts 1 state |
| 02 | counter_incdec | 28 | 5.76 s | 28 | 0.77 s | **MATCH** | |
| 03 | counter_race_bug | 13 | 0.17 s | 13 | 0.81 s | **MATCH** | Negative |
| 04 | lock_basic | 5 | 0.12 s | 5 | 0.75 s | **MATCH** | |
| 05 | broken_lock_bug | 17 | 0.12 s | 9 | 0.80 s | DIFF | Negative; different trace |
| 06 | ticket_lock | 7 | 0.41 s | 7 | 0.74 s | **MATCH** | |
| 07 | producer_consumer | 10,001 | 0.82 s | 201 | 0.83 s | DIFF | TLC CONSTRAINT much tighter |
| 08 | bounded_buffer | 6 | 2.34 s | 10 | 0.82 s | DIFF | Negative; TLC explores more |
| 09 | peterson_mutex | 10 | 0.12 s | 10 | 0.82 s | **MATCH** | |
| 10 | bakery_mutex | 24 | 2.03 s | -- | timeout | TIMEOUT | TLC can't finish at int 0..2 |
| 11 | readers_writers | 4 | 0.09 s | 4 | 0.80 s | **MATCH** | Negative |
| 12 | dining_phil | 14 | 3.69 s | 14 | 0.86 s | **MATCH** | Negative (deadlock) |
| 13 | twophase | 257 | 7.43 s | 257 | 0.80 s | **MATCH** | NumRM=7 |
| 14 | leader_election | 1,313 | 26.57 s | 5,786 | 1.08 s | DIFF | Symmetry collapse (DPOR) |
| 15 | chain_replication | 114 | 3.27 s | 154 | 0.85 s | DIFF | Negative (deadlock) |
| 16 | primarybackup | 861 | 40.99 s | 861 | 0.90 s | **MATCH** | |
| 17 | paxos | 945 | 27.26 s | 391,936 | 33.07 s | DIFF | Symmetry collapse (DPOR) |
| 18 | pbft | 3,659 | 7.17 s | 3,659 | 1.15 s | **MATCH** | replica=45 |
| 19 | epaxos | 11 | 0.58 s | 37 | 0.84 s | DIFF | Different bounds |
| 20 | raft | 1,089 | 2.68 s | 1,089 | 0.91 s | **MATCH** | server=8, depth=50 |

**Summary:**
- **MATCH on 11/20 cases** (02,03,04,06,09,11,12,13,16,18,20)
- **DIFF on 8/20 cases** (01,05,07,08,14,15,17,19) — all explained by
  bounding differences or symmetry reduction
- **TIMEOUT on 1/20** (case 10 BakeryMutex — TLC can't finish even at
  NumProcs=2 within 300s)
- DPOR finds exact same verdicts as TLC on all 19 comparable cases

**DIFF explanations:**
- Cases 01, 07: DPOR uses depth-based bounding; TLC uses
  CONSTRAINT on integer variables. Different mechanisms explore
  different subsets.
- Cases 05, 08, 15: Negative cases where exploration order affects
  how many states are seen before the violation/deadlock.
- Case 14, 17: DPOR's symmetry reduction (`symmetry_fields`) collapses
  equivalent states that TLC explores individually.
- Case 19: DPOR's tighter int bounds (0..1) vs TLC's wider exploration.

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

## Phase 38.21.D + 38.21.J — Complete Symmetry + SpecContext Cache

Two follow-on optimizations on top of Phase 38.18.9/10:

**38.21.D — complete canonical labeling** (commit `13aaa959`).
Phase 38.18.9 used field-walk-order rank assignment, sound but
incomplete: states X = (maxBal={1,2}, maxVBal={2}) and
Y = (maxBal={1,2}, maxVBal={1}) are equivalent under the 1↔2
permutation but were canonicalized to different keys.

The replacement: for each int that appears in any symmetric field,
compute a *signature* — the tuple of its membership in each
symmetric field. Two ints with the same signature are interchangeable;
sort by (signature, original_value) and assign ranks. Sound AND
complete for Set<int>/Map<int, _> field-wise permutations.

**38.21.J — SpecContext lazy-init cache** (commit `208bbf0e`).
Added `OnceLock` fields to SpecContext for the post-inlining
TransitionIr and per-branch existential expansions. Both are run-
invariant; previously rebuilt for every state inside
`solve_successors_with_branch_labels`.

### Re-measured results on Election + Paxos (2026-04-19)

| Case | Strategy | States | Trans | Wall | Sym collapses |
|---|---|---:|---:|---:|---:|
| 14 Election (4 nodes) | `--search bfs` | **1,263** | 19,887 | **33.3 s** | 2,547 |
| 14 Election (4 nodes) | `--search dpor` | **38** | 37 | 37.8 s | n/a |
| 17 Paxos (8 acceptors / 5 values) | `--search bfs` | **945** | 17,957 | **32.3 s** | 5,404 |
| 17 Paxos (8 acceptors / 5 values) | `--search dpor` | **153** | 152 | 33.3 s | n/a |

### Profile breakdown

**Paxos BFS (32.3 s, 945 states, 17,957 transitions):**

| Phase | Time | % |
|---|---:|---:|
| `successor_solving_ms` | 26,407 ms | 82 % |
| `candidate_generation_evaluation_ms` | 3,877 ms | 12 % |
| `dedup_hashing_normalization_ms` | 1,906 ms | 6 % |
| `invariant_evaluation_ms` | 6 ms | 0 % |

Solver dominates. Direct-assignment branch solves: **3,780**
(zero enumeration fallback). Guard pruning eliminated **586,185**
candidate assignments — over 70 % of total — confirming the
Phase-38.17.2 inliner + symmetry tightening are doing their job.

**Election BFS (31.8 s, 1,263 states, 19,887 transitions):**

| Phase | Time | % |
|---|---:|---:|
| `successor_solving_ms` | 10,698 ms | 34 % |
| `candidate_generation_evaluation_ms` | 9,696 ms | 30 % |
| `dedup_hashing_normalization_ms` | 2,792 ms | 9 % |
| (residual / explorer overhead) | 8,574 ms | 27 % |

Election's solver-vs-candidate split is more balanced because its
branches each take an existential `node` parameter that's enumerated
inside the solve. **84,229** existential assignments guard-pruned.

**Paxos / Election DPOR (`--search dpor`):** the synthesized
`ExplorationResult` doesn't decompose the DPOR engine's internal
phases, so its `dedup_hashing_normalization_ms` is a residual catch-
all (29,099 ms / 20,484 ms respectively). Real time is split across
DPOR's own per-state successor enumeration, sleep-set computation,
and the symmetry-aware canonical-key construction — all currently
uninstrumented in the synthesized result. Future work: thread
DPOR-internal phase timers up through the `DporResult` struct.

## Phase 38.18.9 Cross-Field Symmetry Reduction (superseded by 38.21.D)

The existing `search.symmetry_fields` mechanism in
`transpiler/src/modelcheck/explorer.rs` was per-field — it normalized
each named field's int atoms independently with a fresh atom map per
field. That's correct for *single-field* symmetry but loses cross-
field permutation equivalence: state {maxBal={1,2}, maxVBal={1}}
and state {maxBal={3,4}, maxVBal={3}} (both representing "two
acceptors voted in 1b, one in 2b ack, where the 2b acceptor is one
of the 1b acceptors") were treated as distinct.

Phase 38.18.9 makes the atom map *shared* across all listed
symmetry fields — first-encountered int values get atom IDs in
field-walk order, and the same int gets the same atom ID across all
listed fields. This correctly canonicalizes states that differ only
in acceptor-permutation when multiple fields share the same actor
domain.

Soundness: my algorithm is sound (won't merge non-equivalent states)
but not complete (may miss some equivalences depending on field
walk order). For Paxos, a 17× empirical reduction at 6/5 scale
suggests it captures the bulk of the symmetric class structure.

| Case | Pre-symmetry | Post-symmetry | Reduction |
|---|---:|---:|---:|
| 17 Paxos 6/5 | 24,256 states / 370.6 s | 1,447 states / 25.0 s | **17× states / 14.8× wall-time** |

After the win, Paxos was scaled from 6/5 → 8/5 (same wall-time
budget):
- 6/5 + sym: 1,447 / 25.0 s
- 7/5 + sym: 2,972 / 75.4 s
- 8/5 + sym: **6,033 / 194.3 s** (chosen)
- 9/5 + sym: 12,166 / 555.5 s (over-margin)

Opt-in per-case: add `symmetry_fields = ["field1", "field2", ...]`
to `[search]`. Only Paxos is currently using it; the other multi-
process protocols (PBFT, Raft, Election) could benefit similarly
once their symmetry classes are annotated.

## Phase 38.18.8 Model-Bound Scale-Up

After Phase 38.18.5/6/7 closed the solver's performance holes, the
per-case `tests/model_configs/*.toml` configs were scaled up toward
the 10-minute DPOR budget. Old scale-up attempts (Phase 38.20.3)
timed out at these bounds because the inliner wasn't firing; with
the inliner fixes, larger state spaces become tractable:

| Case | Old bound / states | New bound / states | DPOR time |
|---|---|---|---:|
| 17 Paxos | 3/3, 232 states | **6 acceptors / 5 values**, 24,256 states | 370.6 s |
| 18 PBFT | 20 replicas, 634 states | **40 replicas**, 2,854 states | 6.67 s |
| 14 Election | 2 nodes, 108 states | **4 nodes**, 5,704 states | 60.5 s |
| 16 PrimaryBackup | MaxLogLen=1, 8 states | **MaxLogLen=3, 2 values**, 261 states | 3.14 s |
| 15 Chain | 1 value, 35 states | **ChainLen=3, 2 values**, 114 states | 3.80 s |

Bounds that can't go higher on the current engine:
- **19 EPaxos** capped at NumReplicas=2, MaxBallot=1 — 12-field state
  struct explodes the candidate-enumeration pool at any larger bound
  (even 1 M / 10 M candidate caps were exceeded).
- **20 Raft** capped at server=8 — server≥10 hits an evaluator-hook
  missing bug for `LFollower` in constants-dependent Init expressions.
- **18 PBFT** capped at replica=40 — replica≥50 hits the same
  evaluator-hook pattern for `LPrePrepare`.
- **10 Bakery** capped at NumProcs=2 for the suite run — NumProcs=3
  has the same evaluator-hook issue at int max=3.

These ceiling bugs are tracked as follow-ups; they're not in the
inliner path, they're in `expand_type_domain_candidates` /
`eval_constants_dependent_init`.

Notable finding: at the new Paxos 6/5 scale, DPOR and TLC agree on
an **exactly 24,256-state** reachable set (MATCH) — the same parity
story held at 3/3 (232 states) is preserved 100× larger. This is a
stronger soundness cross-check than any prior run.

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

### 6. DPOR sleep-set in main path — landed (Phase 38.18.10)

The cyclic dep that blocked this for months has been broken:
`transpiler/src/modelcheck/dpor/{baseline,enabled,explore,types,witness}.rs`
now hold the DPOR algorithm directly, and the prototype `dpor-checker`
crate is a thin re-export. The main `verus-transpile model-check` CLI
gained `--search dpor` to invoke the relocated explorer instead of
BFS/DFS.

Measured directly on Paxos 8/5 (post-symmetry):
- `--search bfs`  (default): 6,033 distinct states / 199 s
- `--search dpor` (new):     **153 distinct states / 33 s**

That's **39× state-set reduction, 6× wall-time** on top of the symmetry
win. The MATCH-vs-DIFF parity column for case 17 reflects the
algorithmic reduction — DPOR's sleep-set explores fewer interleavings
that produce equivalent state sequences.

Caveat: when `--search dpor` is set, the leads_to/liveness checker is
skipped (DPOR doesn't store full RuntimeValue for every reached
state, only canonical-key strings). For invariant-only specs (the
common case), this has no effect.

### 7. Solver throughput is the remaining bottleneck

Post-symmetry profile of Paxos 8/5 (204 s wall-clock):
- successor_solving_ms: **186,040 ms (91%)** ← AST-interpreter overhead
- dedup_hashing_normalization_ms: 13,447 ms (6.6%)
- everything else: ~5%

`canonical_key()` String dedup is no longer the bottleneck; it's the
per-action AST-interpreted `eval_expr` walking RuntimeValue trees and
cloning ~3 `Set<int>` field structs per successful transition. To get
another order of magnitude:
- **Codegen spec functions to Rust closures** at startup (5-20× win
  on solver, multi-day implementation)
- **Hash-cons / Arc<RuntimeValue> for unchanged subfields** to avoid
  per-successor field-clones
- **FxHash u64 dedup** instead of String canonical_key — small win
  now (~5% wall-time on Paxos 8/5) since dedup is no longer dominant

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
| 9776a725 | 38.18.6 distribute ∧ through ∨ in branch discovery | Election 917×, Chain 99×, Bakery 2.4× |
| 6315cb3b | 38.18.7 lift q-free conjuncts out of forall body | Bakery 31× (76.2 s → 2.43 s); closes last fallback |
| c4d77402 | 38.18.8 scale up all 20 case bounds toward 10-min budget | Paxos 100× state-count growth, etc. |
| (this) | **38.18.9 cross-field acceptor-symmetry reduction** | **Paxos 17× state-set reduction; enables 8/5 scale-up at 4× headroom** |

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
