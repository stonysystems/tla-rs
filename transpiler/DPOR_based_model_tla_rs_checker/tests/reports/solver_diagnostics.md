# Solver Branch Diagnostics (Phase 38.17.1)

| Case | Branch | Eq | Pred | Solver | Fallback Reason | Invocations | Eval Calls | Solve ms |
|------|--------|----|------|--------|-----------------|-------------|------------|----------|
| 01_aplusb | branch_0 | 2 | 0 | direct | direct | 6000 | 12000 | 0 |
| 02_counter_incdec | branch_0 | 2 | 2 | direct | direct | 28 | 1232 | 1054 |
| 02_counter_incdec | branch_1 | 2 | 3 | direct | direct | 28 | 1540 | 0 |
| 03_counter_race_bug | branch_0 | 3 | 2 | direct | direct | 10 | 150 | 17 |
| 03_counter_race_bug | branch_1 | 3 | 2 | direct | direct | 10 | 150 | 0 |
| 04_lock_basic | branch_0 | 3 | 2 | direct | direct | 5 | 125 | 7 |
| 04_lock_basic | branch_1 | 2 | 2 | direct | direct | 5 | 100 | 0 |
| 05_broken_lock_bug | branch_0 | 2 | 2 | direct | direct | 5 | 100 | 7 |
| 05_broken_lock_bug | branch_1 | 2 | 2 | direct | direct | 5 | 100 | 0 |
| 06_ticket_lock | branch_0 | 4 | 2 | direct | direct | 7 | 126 | 63 |
| 06_ticket_lock | branch_1 | 5 | 2 | direct | direct | 7 | 147 | 0 |
| 06_ticket_lock | branch_2 | 4 | 2 | direct | direct | 7 | 126 | 0 |
| 07_producer_consumer_1slot | branch_0 | 4 | 1 | direct | direct | 10000 | 50000 | 0 |
| 07_producer_consumer_1slot | branch_1 | 4 | 1 | direct | direct | 10000 | 50000 | 0 |
| 08_bounded_buffer_2slot | branch_0 | 6 | 1 | direct | direct | 4 | 28 | 325 |
| 08_bounded_buffer_2slot | branch_1 | 6 | 1 | direct | direct | 4 | 28 | 0 |
| 09_peterson_mutex_2p | branch_0 | 3 | 2 | direct | direct | 10 | 150 | 7 |
| 09_peterson_mutex_2p | branch_1 | 3 | 3 | direct | direct | 10 | 180 | 0 |
| 09_peterson_mutex_2p | branch_2 | 3 | 2 | direct | direct | 10 | 150 | 0 |
| 10_bakery_mutex_3p | branch_0 | 3 | 2 | direct | direct | 24 | 360 | 248 |
| 10_bakery_mutex_3p | branch_1 | 3 | 2 | direct | direct | 24 | 360 | 0 |
| 10_bakery_mutex_3p | branch_2 | 3 | 3 | direct | direct | 24 | 432 | 0 |
| 10_bakery_mutex_3p | branch_3 | 3 | 2 | direct | direct | 24 | 360 | 0 |
| 11_readers_writers_small | branch_0 | 4 | 3 | direct | direct | 3 | 42 | 5 |
| 11_readers_writers_small | branch_1 | 4 | 2 | direct | direct | 3 | 36 | 0 |
| 11_readers_writers_small | branch_2 | 4 | 4 | direct | direct | 3 | 96 | 0 |
| 11_readers_writers_small | branch_3 | 4 | 3 | direct | direct | 3 | 84 | 0 |
| 12_dining_philosophers_3 | branch_0 | 2 | 3 | direct | direct | 10 | 200 | 455 |
| 12_dining_philosophers_3 | branch_1 | 2 | 3 | direct | direct | 10 | 200 | 0 |
| 12_dining_philosophers_3 | branch_2 | 2 | 2 | direct | direct | 10 | 160 | 0 |
| 13_twophase_small | branch_0 | 4 | 3 | direct | direct | 257 | 14392 | 1367 |
| 13_twophase_small | branch_1 | 5 | 1 | direct | direct | 257 | 12336 | 0 |
| 13_twophase_small | branch_2 | 4 | 1 | direct | direct | 257 | 10280 | 0 |
| 14_leader_election_small | branch_0 | 9 | 3 | direct | direct | 1313 | 78780 | 3549 |
| 14_leader_election_small | branch_1 | 8 | 2 | direct | direct | 1313 | 65650 | 2 |
| 14_leader_election_small | branch_2 | 8 | 4 | direct | direct | 1313 | 393900 | 0 |
| 14_leader_election_small | branch_3 | 10 | 3 | direct | direct | 1313 | 426725 | 0 |
| 14_leader_election_small | branch_4 | 10 | 4 | direct | direct | 1313 | 459550 | 0 |
| 14_leader_election_small | branch_5 | 8 | 4 | direct | direct | 1313 | 1969500 | 1989 |
| 14_leader_election_small | branch_6 | 8 | 4 | direct | direct | 1313 | 1969500 | 3491 |
| 15_chain_replication_small | branch_0 | 12 | 3 | direct | direct | 4 | 180 | 467 |
| 15_chain_replication_small | branch_1 | 12 | 4 | direct | direct | 4 | 192 | 0 |
| 15_chain_replication_small | branch_2 | 11 | 6 | direct | direct | 4 | 204 | 0 |
| 15_chain_replication_small | branch_3 | 12 | 5 | direct | direct | 4 | 204 | 0 |
| 15_chain_replication_small | branch_4 | 11 | 7 | direct | direct | 4 | 216 | 0 |
| 15_chain_replication_small | branch_5 | 11 | 5 | direct | direct | 4 | 192 | 0 |
| 15_chain_replication_small | branch_6 | 11 | 7 | direct | direct | 4 | 7776 | 16 |
| 16_primarybackup_small | branch_0 | 13 | 2 | direct | direct | 861 | 77490 | 8322 |
| 16_primarybackup_small | branch_1 | 13 | 1 | direct | direct | 861 | 72324 | 0 |
| 16_primarybackup_small | branch_2 | 11 | 3 | direct | direct | 861 | 72324 | 0 |
| 16_primarybackup_small | branch_3 | 12 | 2 | direct | direct | 861 | 72324 | 0 |
| 16_primarybackup_small | branch_4 | 12 | 2 | direct | direct | 861 | 72324 | 0 |
| 16_primarybackup_small | branch_5 | 13 | 2 | direct | direct | 861 | 77490 | 0 |
| 16_primarybackup_small | branch_6 | 11 | 3 | direct | direct | 861 | 72324 | 0 |
| 16_primarybackup_small | branch_7 | 11 | 2 | direct | direct | 861 | 67158 | 0 |
| 17_paxos_small | branch_0 | 3 | 2 | direct | direct | 945 | 42525 | 0 |
| 17_paxos_small | branch_1 | 3 | 5 | direct | direct | 945 | 612360 | 945 |
| 17_paxos_small | branch_2 | 3 | 8 | direct | direct | 945 | 7577955 | 8910 |
| 17_paxos_small | branch_3 | 3 | 12 | direct | direct | 945 | 10333575 | 11776 |
| 18_pbft_small | branch_0 | 6 | 2 | direct | direct | 3659 | 29272 | 917 |
| 18_pbft_small | branch_1 | 6 | 2 | direct | direct | 3659 | 29272 | 0 |
| 18_pbft_small | branch_10 | 6 | 5 | direct | direct | 3659 | 40249 | 0 |
| 18_pbft_small | branch_11 | 6 | 5 | direct | direct | 3659 | 40249 | 0 |
| 18_pbft_small | branch_12 | 6 | 5 | direct | direct | 3659 | 40249 | 0 |
| 18_pbft_small | branch_13 | 6 | 5 | direct | direct | 3659 | 40249 | 0 |
| 18_pbft_small | branch_14 | 6 | 5 | direct | direct | 3659 | 40249 | 0 |
| 18_pbft_small | branch_15 | 6 | 5 | direct | direct | 3659 | 40249 | 0 |
| 18_pbft_small | branch_16 | 5 | 1 | direct | direct | 3659 | 21954 | 0 |
| 18_pbft_small | branch_17 | 6 | 6 | direct | direct | 3659 | 43908 | 0 |
| 18_pbft_small | branch_18 | 6 | 6 | direct | direct | 3659 | 43908 | 0 |
| 18_pbft_small | branch_19 | 6 | 6 | direct | direct | 3659 | 43908 | 0 |
| 18_pbft_small | branch_2 | 6 | 2 | direct | direct | 3659 | 29272 | 0 |
| 18_pbft_small | branch_20 | 6 | 6 | direct | direct | 3659 | 43908 | 0 |
| 18_pbft_small | branch_21 | 6 | 6 | direct | direct | 3659 | 43908 | 0 |
| 18_pbft_small | branch_22 | 6 | 6 | direct | direct | 3659 | 43908 | 0 |
| 18_pbft_small | branch_23 | 6 | 6 | direct | direct | 3659 | 43908 | 0 |
| 18_pbft_small | branch_24 | 5 | 1 | direct | direct | 3659 | 21954 | 0 |
| 18_pbft_small | branch_25 | 4 | 0 | direct | direct | 3659 | 14636 | 0 |
| 18_pbft_small | branch_3 | 6 | 2 | direct | direct | 3659 | 29272 | 0 |
| 18_pbft_small | branch_4 | 6 | 2 | direct | direct | 3659 | 29272 | 0 |
| 18_pbft_small | branch_5 | 6 | 2 | direct | direct | 3659 | 29272 | 0 |
| 18_pbft_small | branch_6 | 6 | 2 | direct | direct | 3659 | 29272 | 0 |
| 18_pbft_small | branch_7 | 6 | 2 | direct | direct | 3659 | 29272 | 0 |
| 18_pbft_small | branch_8 | 6 | 2 | direct | direct | 3659 | 29272 | 0 |
| 18_pbft_small | branch_9 | 6 | 5 | direct | direct | 3659 | 40249 | 0 |
| 19_epaxos_small | branch_0 | 13 | 1 | direct | direct | 11 | 308 | 76 |
| 19_epaxos_small | branch_1 | 12 | 2 | direct | direct | 11 | 1232 | 0 |
| 19_epaxos_small | branch_10 | 13 | 6 | direct | direct | 11 | 13376 | 11 |
| 19_epaxos_small | branch_2 | 14 | 5 | direct | direct | 11 | 6688 | 2 |
| 19_epaxos_small | branch_3 | 15 | 5 | direct | direct | 11 | 3520 | 0 |
| 19_epaxos_small | branch_4 | 15 | 5 | direct | direct | 11 | 3520 | 0 |
| 19_epaxos_small | branch_5 | 12 | 4 | direct | direct | 11 | 2816 | 0 |
| 19_epaxos_small | branch_6 | 14 | 6 | direct | direct | 11 | 7040 | 0 |
| 19_epaxos_small | branch_7 | 14 | 6 | direct | direct | 11 | 7040 | 0 |
| 19_epaxos_small | branch_8 | 13 | 5 | direct | direct | 11 | 6336 | 0 |
| 19_epaxos_small | branch_9 | 12 | 8 | direct | direct | 11 | 14080 | 16 |
| 20_raft_small | branch_0 | 5 | 1 | direct | direct | 1089 | 6534 | 434 |
| 20_raft_small | branch_1 | 5 | 1 | direct | direct | 1089 | 6534 | 0 |
| 20_raft_small | branch_10 | 6 | 2 | direct | direct | 1089 | 8712 | 0 |
| 20_raft_small | branch_11 | 6 | 2 | direct | direct | 1089 | 8712 | 0 |
| 20_raft_small | branch_12 | 6 | 2 | direct | direct | 1089 | 8712 | 0 |
| 20_raft_small | branch_13 | 6 | 2 | direct | direct | 1089 | 8712 | 0 |
| 20_raft_small | branch_14 | 6 | 2 | direct | direct | 1089 | 8712 | 0 |
| 20_raft_small | branch_15 | 5 | 0 | direct | direct | 1089 | 5445 | 0 |
| 20_raft_small | branch_2 | 5 | 1 | direct | direct | 1089 | 6534 | 0 |
| 20_raft_small | branch_3 | 5 | 1 | direct | direct | 1089 | 6534 | 0 |
| 20_raft_small | branch_4 | 5 | 1 | direct | direct | 1089 | 6534 | 0 |
| 20_raft_small | branch_5 | 5 | 3 | direct | direct | 1089 | 8712 | 0 |
| 20_raft_small | branch_6 | 5 | 3 | direct | direct | 1089 | 8712 | 0 |
| 20_raft_small | branch_7 | 5 | 3 | direct | direct | 1089 | 8712 | 0 |
| 20_raft_small | branch_8 | 5 | 3 | direct | direct | 1089 | 8712 | 0 |
| 20_raft_small | branch_9 | 5 | 3 | direct | direct | 1089 | 8712 | 0 |

## Summary

- Total branches across all cases: 112
- Direct assignment: 112 (100%)
- Enumeration fallback: 0 (0%)

### Fallback reason breakdown

- `direct`: 112 branches

