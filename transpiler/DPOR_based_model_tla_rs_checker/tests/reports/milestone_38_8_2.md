# Phase 38.8.2 Milestone Report: Source-DPOR with Baseline Parity

**Date**: 2026-03-26
**Milestone**: 38.8.2 — Source-DPOR backtrack/source-set insertion with exact verdict parity

## Parity Subset Results (Cases 01-12)

| # | Case ID | Baseline Verdict | DPOR Verdict | Baseline States | DPOR States | Match | Notes |
|---|---------|-----------------|--------------|-----------------|-------------|-------|-------|
| 01 | `01_aplusb` | ok | ok | 21 | **21** | **EXACT** | Linear chain, single process |
| 02 | `02_counter_incdec` | — | — | — | — | N/A | Translation failed (CONSTANT) |
| 03 | `03_counter_race_bug` | — | — | — | — | N/A | Translation failed (CONSTANT) |
| 04 | `04_lock_basic` | — | — | — | — | N/A | Translation failed (CONSTANT) |
| 05 | `05_broken_lock_bug` | — | — | — | — | N/A | Translation failed (CONSTANT) |
| 06 | `06_ticket_lock` | — | — | — | — | N/A | Translation failed (CONSTANT) |
| 07 | `07_producer_consumer_1slot` | ok (21) | ok (1) | 21 | 1 | SUBSET | Predicate solver limitation |
| 08 | `08_bounded_buffer_2slot` | error | error | 0 | 0 | N/A | Spec parser: closure syntax |
| 09 | `09_peterson_mutex_2p` | error | error | 0 | 0 | N/A | Spec parser: closure syntax |
| 10 | `10_bakery_mutex_3p` | — | — | — | — | N/A | Translation failed (CHOOSE) |
| 11 | `11_readers_writers_small` | — | — | — | — | N/A | Translation failed (CONSTANT) |
| 12 | `12_dining_philosophers_3` | — | — | — | — | N/A | Translation failed (CONSTANT) |

## Summary

| Metric | Value |
|--------|-------|
| Cases in parity subset | 12 |
| Cases where both engines run | 2 |
| **Exact state-set parity** | **1** (APlusB: 21 == 21) |
| DPOR subset of baseline | 1 (ProducerConsumer: 1 ⊆ 21) |
| Cases blocked on translation | 8 |
| Cases blocked on spec parser | 2 |

## APlusB Detailed Metrics

| Metric | Baseline | DPOR Conservative | DPOR w/ Independence |
|--------|----------|-------------------|---------------------|
| Distinct states | 21 | 21 | 21 |
| Transitions fired | — | 20 | 20 |
| Traces explored | — | 20 | 20 |
| Max depth | 20 | 20 | 20 |
| Verdict | ok | ok | ok |
| **Parity** | — | **EXACT** | **EXACT** |

## Independence-Based Pruning Status

- **Mechanism**: POR branch-footprint analysis from `por.rs`
- **Current effect on APlusB**: None (single process, `reads_whole_state=true`)
- **Reason**: Translated TLA+ specs use predicate-style branches (`LAdd(s, s_)`)
  which conservatively mark the whole state as read. Field-level independence
  requires direct assignment-style branches.
- **When it will help**: Multi-process protocol specs with field-level assignments
  (e.g., when `02_counter_incdec` becomes translatable with CONSTANT support)

## Architecture Delivered

| Component | File | Purpose |
|-----------|------|---------|
| Core types | `src/types.rs` | ProcessId, ActionId, EnabledTransition, TransitionFootprint, ScheduledStep, VectorClock |
| Spec loading | `src/enabled.rs` | SpecContext: load spec, initial states, enabled transitions, full successors |
| DFS explorer | `src/dpor.rs` | explore_dpor(): DFS with backtrack sets, state dedup, configurable limits |
| Baseline oracle | `src/baseline.rs` | Subprocess-based baseline model checker invocation |
| Export analysis | `src/explorer.rs` | Parse --export-parity-debug output for graph analysis |
| Library extraction | `modelcheck/helpers.rs` | eval_spec_function_call_recursive + helpers |
| Library extraction | `modelcheck/domain.rs` | expand_type_domain_candidates + find_struct_definition |
| POR footprints | `modelcheck/por.rs` | Footprint + branch_footprint() + independent_of() |

## Test Coverage

| Test Category | Count |
|---------------|-------|
| Type unit tests | 14 |
| Baseline subprocess tests | 2 |
| Export graph analysis tests | 6 |
| Enabled-set enumeration tests | 7 |
| DPOR DFS exploration tests | 4 |
| DPOR parity tests | 2 |
| Independence parity test | 1 |
| **Total** | **36** |

## Next Steps

1. **38.8.2.a**: Raise the 2/12 pass floor by adding CONSTANT/EXCEPT support to TLA+ translator
2. **38.8.3**: Sleep sets and wakeup trees (gated on baseline parity on more cases)
3. Multi-process process-identity extraction for real independence pruning
