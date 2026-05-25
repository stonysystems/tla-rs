# Native Codegen Cross-Check Report

Generated: 2026-05-25T09:24:22Z

## Summary

| Metric | Count |
|--------|-------|
| Total cases | 12 |
| Exact match | 12 |
| Mismatch | 0 |
| Errors | 0 |

## Per-Case Results

| Case | Verdict | Baseline States | Native States | Status |
|------|---------|----------------|--------------|--------|
| 01_aplusb | ok | 6001 | 6001 | PASS |
| 02_counter_incdec | ok | 28 | 28 | PASS |
| 03_counter_race_bug | invariant_violated | 13 | 13 | PASS |
| 04_lock_basic | ok | 5 | 5 | PASS |
| 05_broken_lock_bug | invariant_violated | 17 | 17 | PASS |
| 06_ticket_lock | ok | 7 | 7 | PASS |
| 07_producer_consumer_1slot | ok | 10001 | 10001 | PASS |
| 08_bounded_buffer_2slot | ok | 9 | 9 | PASS |
| 09_peterson_mutex_2p | ok | 10 | 10 | PASS |
| 11_readers_writers_small | invariant_violated | 4 | 4 | PASS |
| 12_dining_philosophers_3 | deadlock_detected | 14 | 14 | PASS |
| 13_twophase_small | ok | 257 | 257 | PASS |
