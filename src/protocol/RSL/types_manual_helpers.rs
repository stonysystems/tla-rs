// Legacy helper notes for RSL concrete types generation.
//
// As of Phase 21.7.5.5, `types_transpile.toml` no longer uses
// `output.manual_code`, so this file is not injected into generated output.
//
// Historical note: this file previously required body-only snippets intended for
// insertion inside an existing `verus! { ... }` block.
//
// Helper functions shared with types_i.rs (COperationNumber helpers, CBalLt/Leq/Eq,
// CRequestBatch helpers, CReplyCache helpers, CVotes helpers, CLearnerTuple,
// CLearnerState helpers) are defined in types_i.rs and bulk re-exported via:
//   pub use crate::implementation::RSL::types_i::*;
// in the re_exports section of types_transpile.toml.
//
// CRslIo is generated via [extra_type_aliases] in types_transpile.toml.

// =============================================================================
// Legacy manual-helper note
// =============================================================================
//
// As of Phase 21.7.5.5, types generation no longer injects `output.manual_code`.
// Remaining CParameters validity/view semantics moved to:
//   src/implementation/RSL/cparameters.rs
//
// This file is intentionally retained as migration documentation only.

// Foundational type blocks (`CConfiguration`, `CConstants`, `CReplicaConstants`)
// have been re-homed to implementation/RSL/{cconfiguration,cconstants}.rs.

// Component block A (`CAcceptor`, `CLearner`, `CElectionState`, `COutstandingOperation`)
// has been re-homed to implementation/RSL/{acceptorimpl,learnerimpl,ElectionImpl}.rs.

// =============================================================================
// Component extension section (part 2 extraction)
// =============================================================================
// Component block B (`CExecutor`, `CIncompleteBatchTimer`, `CProposer`, `CReplica`,
// `CScheduler`, CRslIo abstractify helpers) has been re-homed to
// implementation/RSL/{ExecutorImpl,ProposerImpl,ReplicaImpl}.rs.
