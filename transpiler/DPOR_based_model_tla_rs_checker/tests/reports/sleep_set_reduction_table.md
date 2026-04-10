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

| Case | Distinct (cons) | Distinct (ind) | Distinct (sleep) | Distinct Reduction vs cons | Transitions (cons) | Transitions (ind) | Transitions (sleep) | Transition Reduction vs cons | Sleep Prunes (sleep) | Sleep Cardinality (avg/max by depth, sleep) | Independence Blockers (early_off/chosen_unknown/cand/ind/same/unknown/conflict, sleep) |
|------|-----------------:|---------------:|-----------------:|----------------------------:|-------------------:|------------------:|--------------------:|-----------------------------:|---------------------:|---------------------------------------------|----------------------------------------------------------------------------------------|
| 02_counter_incdec | 5 | 5 | 5 | 0.0% | 6 | 6 | 6 | 0.0% | 0 | d0:0.0/0;d1:0.0/0;d2:0.0/0 | early_off=0 chosen_unknown=0 cand=10 ind=0 same=7 unknown=0 conflict=3 |
| 09_peterson_mutex_2p | 10 | 10 | 10 | 0.0% | 16 | 16 | 12 | 25.0% | 0 | d0:0.0/0;d1:0.5/1;d2:0.5/1;d3:0.7/1 | early_off=0 chosen_unknown=0 cand=24 ind=15 same=9 unknown=0 conflict=0 |
| 17_paxos_small | 40 | 40 | 40 | 0.0% | 168 | 168 | 168 | 0.0% | 0 | d0:0.0/0;d1:3.0/6;d2:3.0/6;d3:1.6/5;d4:0.7/2;d5:0.0/0 | early_off=0 chosen_unknown=0 cand=423 ind=210 same=39 unknown=0 conflict=174 |

## Gate Status (Phase 38.14.10.d)

Current distinct-state gate in TODO:

- `>10%` distinct-state reduction on at least `3` multi-process cases.

Observed from measured runs above:

- `0 / 3` cases above 10%.

Transition-work signal from the same run:

- `>10%` transition reduction on `1 / 3` measured cases.

Status:

- **Distinct-state gate: NOT MET**.
- **Transition-reduction signal: PARTIAL (1/3)**.

## Notes

- The harness enforces parity safety by asserting:
  `conservative ⊆ independence` and `conservative ⊆ sleep`.
- Under that enforced subset contract, positive distinct-state reduction vs
  conservative is mathematically impossible (`|sleep| >= |conservative|`).
- See `docs/dpor_sleep_set_reduction_gate_rationale.md` for the rationale and
  proposed next decomposition under `38.14.10.d.b.c.i`.
