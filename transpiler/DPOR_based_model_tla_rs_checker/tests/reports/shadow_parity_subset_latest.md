# Shadow Parity Subset Report

Timestamp: 2026-04-10T07:23:15Z

Subset source: `src/dpor.rs::test_automated_baseline_vs_dpor_comparison`

## Summary

- Total cases: 12
- positive_exact: 8
- negative_witness_match: 4
- positive_state_mismatch: 0
- negative_witness_mismatch: 0
- verdict_mismatch: 0
- other_classifications: 0
- parity_failures: 0

## Cases

| Case | Classification | Baseline verdict/states | DPOR verdict/states |
|---|---|---|---|
| 01_aplusb | positive_exact | ok / 21 | ok / 21 |
| 02_counter_incdec | positive_exact | ok / 5 | ok / 5 |
| 03_counter_race_bug | negative_witness_match | invariant_violated / 13 | invariant_violated / 5 |
| 04_lock_basic | positive_exact | ok / 3 | ok / 3 |
| 05_broken_lock_bug | negative_witness_match | invariant_violated / 5 | invariant_violated / 3 |
| 06_ticket_lock | positive_exact | ok / 7 | ok / 7 |
| 07_producer_consumer_1slot | positive_exact | ok / 21 | ok / 21 |
| 08_bounded_buffer_2slot | positive_exact | ok / 6 | ok / 6 |
| 09_peterson_mutex_2p | positive_exact | ok / 10 | ok / 10 |
| 11_readers_writers_small | negative_witness_match | invariant_violated / 4 | invariant_violated / 4 |
| 12_dining_philosophers_3 | negative_witness_match | deadlock_detected / 6 | deadlock_detected / 3 |
| 13_twophase_small | positive_exact | ok / 9 | ok / 9 |
