# Quantifier sites and trigger annotations

Static source scan. **Not** a prediction of `automatically chose triggers` note counts — Verus's default `selective` mode only reports the choices it finds ambiguous. This is the upper bound on sites Phase 54 may touch.

| classification | sites |
|---|---:|
| total | 1435 |
| unannotated | 882 |
| ambiguous | 36 |
| annotated | 445 |
| auto | 72 |

## By directory

| directory | total | unannotated | ambiguous | annotated | auto |
|---|---:|---:|---:|---:|---:|
| `src/protocol/Raft/refinement_proof` | 389 | 197 | 9 | 183 | 0 |
| `src/implementation/RSL` | 213 | 148 | 4 | 53 | 8 |
| `src/generated/RSL` | 174 | 111 | 9 | 46 | 8 |
| `src/protocol/RSL` | 75 | 75 | 0 | 0 | 0 |
| `src/protocol/RSL/common_proof` | 78 | 73 | 0 | 5 | 0 |
| `src/common/collections` | 94 | 58 | 3 | 32 | 1 |
| `src/protocol/RSL/refinement_proof` | 54 | 50 | 1 | 3 | 0 |
| `src/generated_backup/RSL` | 65 | 35 | 8 | 8 | 14 |
| `src/protocol/Raft` | 21 | 21 | 0 | 0 | 0 |
| `src/common/logic` | 44 | 15 | 0 | 29 | 0 |
| `src/protocol/EPaxos` | 11 | 11 | 0 | 0 | 0 |
| `src/verus_extra` | 43 | 11 | 1 | 31 | 0 |
| `src/protocol/TwoPhase` | 10 | 10 | 0 | 0 | 0 |
| `src/protocol/VerticalPaxos` | 10 | 10 | 0 | 0 | 0 |
| `src/protocol/PBFT` | 9 | 9 | 0 | 0 | 0 |
| `src/protocol/ChainReplication` | 8 | 8 | 0 | 0 | 0 |
| `src/protocol/LeaderElection` | 8 | 8 | 0 | 0 | 0 |
| `src/protocol/PrimaryBackup` | 8 | 8 | 0 | 0 | 0 |
| `src/services/lock` | 29 | 7 | 1 | 6 | 15 |
| `src/protocol/Paxos` | 6 | 6 | 0 | 0 | 0 |
| `src/protocol/Jetpack` | 4 | 4 | 0 | 0 | 0 |
| `src/implementation/lock` | 7 | 3 | 0 | 2 | 2 |
| `src/implementation/common` | 24 | 2 | 0 | 18 | 4 |
| `src/common/framework` | 5 | 1 | 0 | 2 | 2 |
| `src/protocol/lock` | 24 | 1 | 0 | 5 | 18 |
| `src/common/native` | 1 | 0 | 0 | 1 | 0 |
| `src/generated/ChainReplication` | 3 | 0 | 0 | 3 | 0 |
| `src/generated/EPaxos` | 1 | 0 | 0 | 1 | 0 |
| `src/generated/LeaderElection` | 3 | 0 | 0 | 3 | 0 |
| `src/generated/PBFT` | 1 | 0 | 0 | 1 | 0 |
| `src/generated/Paxos` | 1 | 0 | 0 | 1 | 0 |
| `src/generated/Raft` | 1 | 0 | 0 | 1 | 0 |
| `src/generated/TwoPhase` | 1 | 0 | 0 | 1 | 0 |
| `src/generated/VerticalPaxos` | 1 | 0 | 0 | 1 | 0 |
| `src/generated_backup/ChainReplication` | 3 | 0 | 0 | 3 | 0 |
| `src/generated_backup/LeaderElection` | 3 | 0 | 0 | 3 | 0 |
| `src/generated_backup/Paxos` | 1 | 0 | 0 | 1 | 0 |
| `src/generated_backup/Raft` | 1 | 0 | 0 | 1 | 0 |
| `src/generated_backup/TwoPhase` | 1 | 0 | 0 | 1 | 0 |

## Files with the most unannotated sites

| file | unannotated | total |
|---|---:|---:|
| `src/protocol/Raft/refinement_proof/invariants.rs` | 168 | 318 |
| `src/generated/RSL/replica_gen.rs` | 43 | 45 |
| `src/implementation/RSL/gen_helpers.rs` | 43 | 61 |
| `src/implementation/RSL/ProposerImpl.rs` | 29 | 44 |
| `src/implementation/RSL/types_i.rs` | 24 | 43 |
| `src/common/collections/sets.rs` | 23 | 33 |
| `src/generated/RSL/proposer_gen.rs` | 22 | 41 |
| `src/protocol/RSL/refinement_proof/chosen.rs` | 19 | 19 |
| `src/protocol/RSL/replica.rs` | 19 | 19 |
| `src/generated/RSL/election_gen.rs` | 18 | 24 |
| `src/generated_backup/RSL/types_gen.rs` | 18 | 28 |
| `src/protocol/RSL/common_proof/chosen.rs` | 18 | 20 |
| `src/protocol/RSL/common_proof/quorum.rs` | 17 | 17 |
| `src/protocol/RSL/refinement_proof/refinement.rs` | 17 | 20 |
| `src/implementation/RSL/acceptor_helpers.rs` | 16 | 22 |
| `src/protocol/Raft/raft_refinement.rs` | 16 | 16 |
| `src/protocol/Raft/refinement_proof/state_machine.rs` | 15 | 29 |
| `src/common/logic/heuristics_i.rs` | 13 | 28 |
| `src/common/collections/hashsets.rs` | 12 | 20 |
| `src/implementation/RSL/ElectionImpl.rs` | 12 | 12 |
| `src/protocol/EPaxos/epaxos.rs` | 11 | 11 |
| `src/protocol/RSL/proposer.rs` | 11 | 11 |
| `src/protocol/Raft/refinement_proof/message_invariants.rs` | 11 | 27 |
| `src/generated/RSL/learner_gen.rs` | 10 | 37 |
| `src/generated_backup/RSL/learner_gen.rs` | 10 | 25 |
| `src/implementation/RSL/cbroadcast.rs` | 10 | 12 |
| `src/protocol/RSL/learner.rs` | 10 | 10 |
| `src/protocol/TwoPhase/twophase.rs` | 10 | 10 |
| `src/protocol/VerticalPaxos/vpaxos.rs` | 10 | 10 |
| `src/common/collections/count_matches.rs` | 9 | 14 |
