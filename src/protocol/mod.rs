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
// TLAPSBench is deliberately not part of this crate. It is verified as its
// own crate root, src/protocol/tlaps_bench_harness.rs, by
// scripts/verify_tlaps_bench_manual.sh under the settings its published
// evidence (reports/tlaps_bench_manual/results.json) was recorded with.
// The main-crate gate, which verus-lang's verita also runs, holds every
// module to the default rlimit with zero trigger notes.
