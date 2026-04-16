# Sleep-Set Reduction Evidence (Phase 38.17.4)

Generated: 2026-04-16

After Phase 38.17.4 (inline action calls for branch footprint extraction),
DPOR sleep-set pruning is now **actively reducing** transitions on
multi-process cases.

## Multi-Process Transition Reduction

Measured via:
```bash
cargo test --release dpor::tests::print_sleep_set_reduction_multi_process_markdown -- --ignored --exact --nocapture
```

| Case | Distinct (cons) | Distinct (ind) | Distinct (sleep) | Transitions (cons) | Transitions (ind) | Transitions (sleep) | **Transition Reduction** | Sleep Prunes |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 02_counter_incdec | 5 | 5 | 5 | 6 | 6 | **4** | **33.3%** | 2 |
| 09_peterson_mutex_2p | 10 | 10 | 10 | 16 | 16 | **9** | **43.8%** | 3 |
| 17_paxos_small | 232 | 232 | 232 | 1,348 | 1,348 | **231** | **82.9%** | 1,117 |

**Gate check** (>10% transition reduction on at least 3 multi-process cases): **3/3 hits** ✓

Distinct-state counts are preserved exactly across conservative / independence
/ sleep modes — DPOR is sound (no states lost).

## What enabled the reduction

Before Phase 38.17.4:
- **All transitions tagged `ProcessId(0)`** (no per-process identity from branches)
- **TransitionFootprints were empty** (no read/write sets extracted)
- **0% reduction across all cases** — DPOR degenerated to exhaustive DFS

Phase 38.17.4 applies the shared `inline_action_calls` function in three places:
1. **Main model checker** (`transpiler/src/main.rs`): already used the inliner
   for solver direct-assignment
2. **DPOR solver path** (`DPOR_based_model_tla_rs_checker/src/enabled.rs:321`):
   so `enumerate_successors` sees decomposed branch constraints
3. **DPOR footprint path** (`DPOR_based_model_tla_rs_checker/src/enabled.rs:635`):
   so `branch_footprints` sees real `s_.field == ...` constraints and can
   extract proper read/write sets via `por::branch_footprint`

With inlined branches, the POR analyzer now sees constraints like:
```
Eq { target: NextState, path: ["maxBal"], value: s.maxBal.union({b}) }
```
and correctly identifies `maxBal` as a written field, enabling sleep-set
propagation to prune redundant interleavings.

## Independence Blocker Breakdown (sleep mode)

| Case | cand | ind | same | unknown | conflict |
|---|---:|---:|---:|---:|---:|
| 02_counter_incdec | 10 | 0 | 7 | 0 | 3 |
| 09_peterson_mutex_2p | 24 | 15 | 9 | 0 | 0 |
| 17_paxos_small | 4,083 | 0 | 231 | 0 | 3,852 |

- **`ind`**: independence proven, transition kept in backtrack set
- **`same`**: same process — always dependent (cannot be pruned)
- **`conflict`**: field-level conflict (writes overlap) — cannot be pruned

The large `conflict` count on Paxos (3,852) means many transitions write
the shared `maxBal` / `maxVBal` / `maxVal` fields, limiting parallelism.
Even so, sleep sets pruned 1,117 redundant interleavings (82.9% reduction).

## Correctness Verification

The `test_sleep_set_parity_all_passing_cases` regression test confirms
**exact state-count preservation** across:
- Conservative (no reduction)
- Independence-only (no sleep sets)
- Independence + sleep sets

All 7 parity-subset cases produce identical distinct-state sets in all
three modes. DPOR reduction prunes **redundant transitions** without
losing any reachable states.

## Historical Context

Prior to Phase 38.17.4, the DPOR engine had been in a paradoxical state:
all the algorithmic infrastructure (backtrack sets, sleep sets, vector
clocks, dependence relation) was implemented and tested — but it never
actually ran because:

1. `ProcessId(0)` was assigned to every transition (from `stable_nonzero_process_hash`)
2. `TransitionFootprint` was always empty (no field extraction)
3. `independent_of()` returned false for everything

Phase 38.17.4 fixed this by making the inliner available to the DPOR crate's
IR-analysis path, so the footprint extractor finally sees the real
field-level constraints.

## Next Steps

- 38.17.5: Run full suite with `use_sleep_sets = true` enabled by default
  and measure end-to-end wall-time impact
- 38.17.6: Extend reduction measurement to cases 10, 13, 18, 20 (which
  have more complex branch structures)
- 38.17.7: Consider adopting the optimal DPOR algorithm (Abdulla et al.)
  which prunes more aggressively than source-DPOR
