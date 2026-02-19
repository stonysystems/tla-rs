pub mod CStateMachine;
pub mod ElectionImpl;
/// Deprecated: use `crate::generated::RSL::executor_gen` for functional wrappers.
/// Retained because generated wrappers delegate to methods in this module.
pub mod ExecutorImpl;
/// Deprecated: use `crate::generated::RSL::proposer_gen` for functional wrappers.
/// Retained because generated wrappers delegate to methods in this module.
pub mod ProposerImpl;
pub mod ReplicaImpl;
/// Deprecated: use `crate::generated::RSL::acceptor_gen` for functional wrappers.
/// Retained because generated wrappers delegate to methods in this module.
pub mod acceptorimpl;
pub mod appinterface;
pub mod cbroadcast;
pub mod cconfiguration;
pub mod cconstants;
pub mod cmessage;
pub mod cparameters;
/// Shared helper functions (clone_cpacket_*, outbound_packets_to_vec) used by
/// generated RSL dispatch wrappers. Centralizes duplicated helpers from *_gen.rs files.
pub mod gen_helpers;
/// Hand-written dispatch functions that orchestrate IO patterns for the RSL replica.
/// These functions call into transpiler-generated functions in replica_gen.rs.
pub mod replica_dispatch;
/// Deprecated: use `crate::generated::RSL::learner_gen` for functional wrappers.
/// Retained because generated wrappers delegate to methods in this module.
pub mod learnerimpl;
pub mod replicaimpl_class;
pub mod cmd_line_parser;
pub mod host_i;
pub mod host_s;
pub mod netrsl_i;
pub mod replicaimpl_delivery;
pub mod replicaimpl_main;
pub mod replicaimpl_no_receive_clock;
pub mod replicaimpl_no_receive_no_clock;
pub mod replicaimpl_process_packet_no_clock;
pub mod replicaimpl_process_packet_x;
pub mod replicaimpl_read_clock;
pub mod types_i;
