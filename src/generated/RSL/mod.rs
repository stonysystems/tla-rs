// Auto-generated RSL types and functions module
// DO NOT EDIT MANUALLY

// 6 of 7 function modules are enabled and wired into ReplicaImpl (Phases C-G).
// election_gen is disabled: not yet referenced by ReplicaImpl (election calls
// are routed through proposer_gen's delegate wrappers to manual ElectionImpl).
pub mod acceptor_gen;
pub mod broadcast_gen;
// pub mod election_gen;  // available but unused — enable when direct election wiring is added
pub mod executor_gen;
pub mod learner_gen;
pub mod proposer_gen;
pub mod replica_gen;
pub mod types_gen;
