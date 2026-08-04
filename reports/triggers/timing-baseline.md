# Verus verification timing

| field | value |
|---|---|
| label | 0.2026.08.02.b677dd5 full crate (output-json) |
| verus version | 0.2026.08.02.b677dd5 |
| source log | /tmp/baseline_json.log |
| modules | 142 |
| total verify time | 219662 ms |
| total-time | 38497 ms |
| verification-time | 28617 ms |
| total-verify | 219735 ms |

## Per module

| module | verify ms | air ms | smt-init ms | smt-run ms | rlimit |
|---|---:|---:|---:|---:|---:|
| `protocol::RSL::refinement_proof::execution` | 19788 | 903 | 1 | 18541 | 14129990 |
| `implementation::RSL::cmessage` | 19315 | 509 | 0 | 17955 | 383549728 |
| `protocol::RSL::common_proof::message2b` | 16988 | 794 | 0 | 15813 | 11179926 |
| `protocol::Raft::refinement_proof::invariants` | 16694 | 1227 | 10 | 14086 | 51517393 |
| `protocol::RSL::common_proof::message1b` | 16307 | 640 | 0 | 15168 | 9735137 |
| `protocol::RSL::common_proof::message2a` | 12123 | 771 | 0 | 10909 | 8164216 |
| `protocol::RSL::common_proof::learner_state` | 11138 | 678 | 0 | 9755 | 7266320 |
| `protocol::RSL::common_proof::chosen` | 10729 | 505 | 0 | 9707 | 7272628 |
| `generated::RSL::replica_gen` | 10670 | 1195 | 1 | 8912 | 8500341 |
| `protocol::RSL::common_proof::packet_sending` | 8909 | 344 | 0 | 8157 | 5740012 |
| `protocol::RSL::refinement_proof::requests` | 8739 | 584 | 0 | 7844 | 6016349 |
| `protocol::RSL::common_proof::constants` | 5594 | 416 | 0 | 4935 | 3363522 |
| `protocol::RSL::common_proof::max_ballot_sent_1a` | 5453 | 252 | 0 | 4801 | 3861661 |
| `protocol::RSL::common_proof::max_ballot` | 2984 | 184 | 0 | 2445 | 1502692 |
| `generated::RSL::proposer_gen` | 2981 | 456 | 1 | 2103 | 3084268 |
| `protocol::RSL::common_proof::receive1b` | 2944 | 195 | 0 | 2436 | 1684606 |
| `implementation::RSL::replicaimpl_no_receive_no_clock` | 2456 | 361 | 0 | 1842 | 1426849 |
| `protocol::RSL::refinement_proof::refinement` | 2355 | 255 | 0 | 1852 | 3295158 |
| `implementation::RSL::gen_helpers` | 2171 | 370 | 0 | 1421 | 2492269 |
| `implementation::RSL::types_i` | 2086 | 323 | 2 | 1385 | 8949010 |
| `implementation::RSL::replicaimpl_no_receive_clock` | 1967 | 288 | 0 | 1481 | 1311257 |
| `implementation::common::marshalling` | 1962 | 216 | 3 | 1487 | 21631329 |
| `protocol::RSL::common_proof::environment` | 1636 | 191 | 0 | 1182 | 775373 |
| `implementation::RSL::ReplicaImpl` | 1302 | 319 | 0 | 671 | 593985 |
| `generated::RSL::election_gen` | 1293 | 252 | 1 | 719 | 1768224 |
| `protocol::RSL::common_proof::quorum` | 1247 | 79 | 0 | 1032 | 3312076 |
| `implementation::RSL::replicaimpl_process_packet_no_clock` | 1135 | 391 | 0 | 562 | 647911 |
| `protocol::RSL::common_proof::actions` | 1120 | 195 | 0 | 650 | 443408 |
| `protocol::Raft::refinement_proof::committed` | 1014 | 148 | 0 | 635 | 1856282 |
| `generated::Raft::raft_gen` | 968 | 212 | 1 | 484 | 1389084 |
| `generated::RSL::executor_gen` | 905 | 245 | 0 | 388 | 960847 |
| `generated::RSL::learner_gen` | 855 | 228 | 0 | 354 | 810896 |
| `implementation::RSL::ProposerImpl` | 817 | 218 | 0 | 348 | 818080 |
| `implementation::RSL::replicaimpl_class` | 816 | 119 | 0 | 488 | 412028 |
| `protocol::RSL::refinement_proof::chosen` | 760 | 189 | 0 | 331 | 457861 |
| `implementation::RSL::replicaimpl_main` | 610 | 179 | 0 | 276 | 304564 |
| `generated::EPaxos::epaxos_gen` | 601 | 190 | 0 | 232 | 660253 |
| `implementation::RSL::appinterface` | 597 | 180 | 0 | 112 | 546029 |
| `generated::RSL::acceptor_gen` | 584 | 162 | 0 | 254 | 621952 |
| `implementation::RSL::ExecutorImpl` | 556 | 156 | 0 | 175 | 422600 |

_102 further modules omitted._
