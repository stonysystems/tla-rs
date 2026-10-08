// pub mod lock;
pub mod Jetpack; // recovery-layer single-process spec (R1 slice, Phase 51.1-51.8 + 51.13)
pub mod ChainReplication;
pub mod ConsensusSafety;
pub mod Corfu;
pub mod Gaios;
pub mod Om;
pub mod ReplicatedCommit;
pub mod SpecPaxos;
pub mod next_five_witnesses;
pub mod EPaxos;
pub mod LeaderElection;
pub mod Mako;
pub mod Mencius;
pub mod PBFT;
pub mod Paxos;
pub mod PrimaryBackup;
pub mod RSL;
pub mod Raft;
pub mod TwoPhase;
pub mod Tiga;
pub mod CausalMesh;
pub mod VerticalPaxos;
pub mod common;
// TLAPSBench has its own crate root, src/protocol/tlaps_bench_harness.rs.
// The separate tlaps-bench.yml workflow runs it weekly or on demand with
// scripts/verify_tlaps_bench_manual.sh (default rlimit, zero trigger notes).
// Keep this expensive benchmark out of the main crate so PR/push CI, daily
// verification, and the Verita entry point do not run it.
