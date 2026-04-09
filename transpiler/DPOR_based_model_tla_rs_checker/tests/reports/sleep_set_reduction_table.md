# Sleep-Set Reduction Table (Phase 38.14.10.d)

This report is generated from the evidence harness:

```bash
cargo test --manifest-path transpiler/DPOR_based_model_tla_rs_checker/Cargo.toml \
  dpor::tests::print_sleep_set_reduction_multi_process_markdown \
  -- --ignored --exact --nocapture
```

Measurement bounds:

- `max_depth=20`
- `max_states=10000`
- modes compared: conservative (`no ind/no sleep`), independence-only, independence+sleep

## Multi-Process Focused Measurements

| Case | Distinct (cons) | Distinct (ind) | Distinct (sleep) | Distinct Reduction vs cons | Transitions (cons) | Transitions (ind) | Transitions (sleep) | Transition Reduction vs cons |
|------|-----------------:|---------------:|-----------------:|----------------------------:|-------------------:|------------------:|--------------------:|-----------------------------:|
| 02_counter_incdec | 5 | 5 | 5 | 0.0% | 6 | 6 | 6 | 0.0% |
| 09_peterson_mutex_2p | 10 | 10 | 10 | 0.0% | 16 | 16 | 16 | 0.0% |
| 17_paxos_small | 40 | 40 | 40 | 0.0% | 168 | 168 | 168 | 0.0% |

## Gate Status (Phase 38.14.10.d)

Required gate to close `38.14.10`:

- `>10%` distinct-state reduction on at least `3` multi-process cases.

Observed from measured runs above:

- `0 / 3` cases above 10%.

Status:

- **NOT MET**.

## Notes

- The harness enforces parity-safety during measurement by asserting:
  `conservative ⊆ independence` and `conservative ⊆ sleep` for distinct states.
- Because the gate is not met, `38.14.10` remains open pending algorithmic reduction work (`38.14.10.d.b` / `38.14.10.d.c`).
