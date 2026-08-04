# Verus verification timing

| field | value |
|---|---|
| label | 0.2026.08.02.b677dd5 full crate (min of 3 runs @ 06620bb8) |
| verus version | 0.2026.08.02.b677dd5 |
| source log | min of 3 runs |
| modules | 142 |
| total verify time | 211512 ms |
| total-time | 37601 ms |
| verification-time | 28022 ms |
| total-verify | 219118 ms |

## Per module

| module | verify ms | air ms | smt-init ms | smt-run ms | rlimit |
|---|---:|---:|---:|---:|---:|
| `implementation::RSL::cmessage` | 19131 | 481 | 0 | 17701 | 383549728 |
| `protocol::RSL::refinement_proof::execution` | 18576 | 871 | 1 | 17272 | 14129990 |
| `protocol::Raft::refinement_proof::invariants` | 16578 | 1186 | 8 | 13813 | 51517393 |
| `protocol::RSL::common_proof::message2b` | 16149 | 727 | 0 | 15044 | 11179926 |
| `protocol::RSL::common_proof::message1b` | 15310 | 530 | 0 | 14287 | 9735137 |
| `protocol::RSL::common_proof::message2a` | 11609 | 709 | 1 | 10490 | 8164216 |
| `protocol::RSL::common_proof::learner_state` | 10162 | 616 | 0 | 8824 | 7266320 |
| `protocol::RSL::common_proof::chosen` | 10002 | 460 | 0 | 9039 | 7272628 |
| `generated::RSL::replica_gen` | 9642 | 1126 | 1 | 7961 | 8500341 |
| `protocol::RSL::common_proof::packet_sending` | 7995 | 348 | 0 | 7378 | 5740012 |
| `protocol::RSL::refinement_proof::requests` | 7956 | 504 | 0 | 7120 | 6016349 |
| `protocol::RSL::common_proof::max_ballot_sent_1a` | 5812 | 249 | 0 | 5165 | 3861661 |
| `protocol::RSL::common_proof::constants` | 5660 | 406 | 0 | 4984 | 3363522 |
| `protocol::RSL::common_proof::receive1b` | 2985 | 167 | 0 | 2469 | 1684606 |
| `generated::RSL::proposer_gen` | 2937 | 459 | 0 | 2076 | 3084268 |
| `protocol::RSL::common_proof::max_ballot` | 2716 | 172 | 0 | 2270 | 1502692 |
| `protocol::RSL::refinement_proof::refinement` | 2575 | 262 | 0 | 1987 | 3295158 |
| `implementation::RSL::replicaimpl_no_receive_no_clock` | 2568 | 385 | 0 | 1916 | 1426849 |
| `implementation::RSL::replicaimpl_no_receive_clock` | 2372 | 351 | 0 | 1799 | 1311257 |
| `implementation::RSL::gen_helpers` | 2241 | 363 | 0 | 1488 | 2492269 |
| `implementation::common::marshalling` | 2024 | 226 | 2 | 1497 | 21631329 |
| `implementation::RSL::types_i` | 1998 | 311 | 2 | 1365 | 8949010 |
| `protocol::RSL::common_proof::environment` | 1775 | 185 | 0 | 1317 | 775373 |
| `implementation::RSL::replicaimpl_process_packet_no_clock` | 1337 | 466 | 0 | 640 | 647911 |
| `protocol::RSL::common_proof::quorum` | 1326 | 88 | 0 | 1104 | 3312076 |
| `implementation::RSL::ReplicaImpl` | 1320 | 308 | 0 | 661 | 593985 |
| `generated::RSL::election_gen` | 1274 | 267 | 0 | 698 | 1768224 |
| `protocol::RSL::common_proof::actions` | 1098 | 175 | 0 | 695 | 443408 |
| `protocol::Raft::refinement_proof::committed` | 953 | 141 | 0 | 593 | 1856282 |
| `generated::Raft::raft_gen` | 925 | 198 | 1 | 463 | 1389084 |
| `generated::RSL::executor_gen` | 893 | 228 | 0 | 391 | 960847 |
| `implementation::RSL::replicaimpl_class` | 836 | 121 | 0 | 464 | 412028 |
| `implementation::RSL::ProposerImpl` | 831 | 231 | 0 | 346 | 818080 |
| `generated::RSL::learner_gen` | 796 | 210 | 0 | 328 | 810896 |
| `protocol::RSL::refinement_proof::chosen` | 709 | 181 | 0 | 291 | 457861 |
| `implementation::RSL::replicaimpl_main` | 609 | 180 | 0 | 267 | 304564 |
| `generated::RSL::acceptor_gen` | 594 | 163 | 0 | 251 | 621952 |
| `generated::EPaxos::epaxos_gen` | 577 | 186 | 0 | 211 | 660253 |
| `implementation::RSL::appinterface` | 576 | 160 | 0 | 100 | 546029 |
| `implementation::RSL::ExecutorImpl` | 512 | 157 | 0 | 174 | 422600 |

_102 further modules omitted._
