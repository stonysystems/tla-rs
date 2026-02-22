pub mod CStateMachine;
pub mod ElectionImpl;
/// Generated wrappers live in `crate::generated::RSL::executor_gen`.
/// This module owns CExecutor/CIncompleteBatchTimer type infrastructure and CExecutorExecute.
pub mod ExecutorImpl;
/// Generated wrappers live in `crate::generated::RSL::proposer_gen`.
/// This module owns CProposer type infrastructure and proposer helper methods.
pub mod ProposerImpl;
pub mod ReplicaImpl;
/// Standalone acceptor vote-map helpers moved out of generated manual injection.
pub mod acceptor_helpers;
/// Generated wrappers live in `crate::generated::RSL::acceptor_gen`.
/// This module owns CAcceptor type infrastructure and compatibility symbol wrappers.
pub mod acceptorimpl;
pub mod appinterface;
pub mod cbroadcast;
pub mod cconfiguration;
pub mod cconstants;
/// Legacy runtime entrypoint parser glue still used by `host_i`/`host_s`.
pub mod cmd_line_parser;
pub mod cmessage;
pub mod cparameters;
/// Shared helper functions (clone_cpacket_*, outbound_packets_to_vec) used by
/// generated RSL dispatch wrappers. Centralizes duplicated helpers from *_gen.rs files.
pub mod gen_helpers;
pub mod host_i;
pub mod host_s;
/// Generated wrappers live in `crate::generated::RSL::learner_gen`.
/// This module owns CLearner type infrastructure.
pub mod learnerimpl;
/// Legacy runtime network glue used by host/replica orchestration modules.
pub mod netrsl_i;
/// Legacy runtime orchestration modules used by `host_i`/`host_s` dispatch paths.
pub mod replicaimpl_class;
pub mod replicaimpl_delivery;
pub mod replicaimpl_main;
pub mod replicaimpl_no_receive_clock;
pub mod replicaimpl_no_receive_no_clock;
pub mod replicaimpl_process_packet_no_clock;
pub mod replicaimpl_process_packet_x;
pub mod replicaimpl_read_clock;
pub mod types_i;
