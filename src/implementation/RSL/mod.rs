pub mod CStateMachine;
pub mod ElectionImpl;
/// Deprecated: use `crate::generated::RSL::executor_gen` for functional wrappers.
/// Retained for type re-exports and impl methods still called by generated wrappers.
pub mod ExecutorImpl;
/// Deprecated: use `crate::generated::RSL::proposer_gen` for functional wrappers.
/// Retained for impl methods still called by generated wrappers (clone-delegate pattern).
pub mod ProposerImpl;
pub mod ReplicaImpl;
/// Generated wrappers live in `crate::generated::RSL::acceptor_gen`.
/// This module owns CAcceptor type infrastructure and log-truncation helper logic.
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
/// Generated wrappers live in `crate::generated::RSL::learner_gen`.
/// This module owns CLearner type infrastructure.
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
